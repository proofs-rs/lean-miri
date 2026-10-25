#!/usr/bin/env bash
# Build the pinned reference interpreter, then its matching MIR-enabled std.
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
features=()
if [[ "${1:-}" == --no-default-features ]]; then
  features+=(--no-default-features)
  shift
fi
if [[ $# != 0 ]]; then
  echo 'Usage: tools/setup-miri-reference.sh [--no-default-features]' >&2
  exit 2
fi
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-$repo_root/.rustup}"
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-$repo_root/.cargo}"
toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
python3 tools/prepare-source-audit.py
python3 tools/coverage.py check --root scratch/source-audit
revision="$(rustc -vV | sed -n 's/^commit-hash: //p')"
if [[ "$revision" != "$(cat upstream/miri-source/rust-version)" ]]; then
  echo 'The reference Miri build requires the exact pinned rustc-dev toolchain.' >&2
  exit 1
fi
for lock in upstream/miri-source/Cargo.lock upstream/miri-source/cargo-miri/Cargo.lock \
  "$toolchain/lib/rustlib/src/rust/library/Cargo.lock"; do
  python3 tools/vendor_pinned_crates.py --lock "$lock" \
    --destination scratch/miri-vendor --cargo-cache "$CARGO_HOME/registry/cache"
done
cargo --config "$repo_root/scratch/cargo-vendor.toml" build --offline --locked \
  --manifest-path upstream/miri-source/Cargo.toml --bin miri "${features[@]}"
cargo --config "$repo_root/scratch/cargo-vendor.toml" test --offline --locked \
  --manifest-path upstream/miri-source/Cargo.toml --lib "${features[@]}"
cargo --config "$repo_root/scratch/cargo-vendor.toml" build --offline --locked \
  --manifest-path upstream/miri-source/cargo-miri/Cargo.toml
# Setup spawns Cargo in a temporary directory. Give those invocations the same
# explicit, locked directory source without altering any user's Cargo config.
cat > scratch/cargo-offline.sh <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
exec "$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d/bin/cargo" \
  --config "$repo_root/scratch/cargo-vendor.toml" "$@"
WRAPPER
chmod +x scratch/cargo-offline.sh
export CARGO="$repo_root/scratch/cargo-offline.sh"
export CARGO_NET_OFFLINE=true
export MIRI="$repo_root/upstream/miri-source/target/debug/miri"
export MIRI_SYSROOT="$repo_root/scratch/miri-sysroot"
upstream/miri-source/cargo-miri/target/debug/cargo-miri miri setup
python3 - "$MIRI" "$revision" "${features[*]}" <<'RECORD'
import hashlib, json, pathlib, sys
binary = pathlib.Path(sys.argv[1])
record = dict(rustc_commit=sys.argv[2], cargo_feature_args=sys.argv[3].split(),
              binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest())
pathlib.Path('scratch/miri-reference-build.json').write_text(json.dumps(record, indent=2) + '\n')
RECORD
printf 'Reference Miri sysroot: %s\n' "$MIRI_SYSROOT"
