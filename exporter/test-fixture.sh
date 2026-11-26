#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/exporter/tests/fixture-env.sh"

if [[ -z "${EXPORTER_BIN:-}" ]]; then
  "$CARGO_HOME/bin/cargo" +"$TOOLCHAIN" build --offline --manifest-path "$ROOT/exporter/Cargo.toml"
fi
EXPORTER="${EXPORTER_BIN:-$ROOT/exporter/target/debug/lean-miri-mir-exporter}"
OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-mir-XXXXXX.json")"
SCOPE_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-mir-scope-XXXXXX.json")"
VIRTUAL_SCOPE_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-mir-scope-virtual-XXXXXX.json")"
SCOPE_ERR="$(mktemp "${TMPDIR:-/tmp}/lean-miri-mir-scope-XXXXXX.err")"
NOOP_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-mir-noops-XXXXXX.json")"
PROVENANCE_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-provenance-XXXXXX.json")"
trap 'rm -f "$OUT" "$SCOPE_OUT" "$VIRTUAL_SCOPE_OUT" "$SCOPE_ERR" "$NOOP_OUT" "$PROVENANCE_OUT"' EXIT
"$EXPORTER" \
  --output "$OUT" --root direct_tag_value --root get_vtable_root --root as_trait_object \
  --root as_drop_trait_object --root call_trait_object --root make_link --root promoted_ref \
  --root byte_string --root pointer_slice --root read_tls --root id --root array_len --root exercise \
  "$ROOT/exporter/fixtures/mir_features.rs" \
  --crate-type=lib --crate-name=mir_features
python3 "$ROOT/exporter/tests/validate_fixture.py" "$OUT"

# A variadic FnPtr call must not send its extra operands to unrelated
# nonvariadic function-pointer candidates during ABI metadata collection.
"$ROOT/exporter/test-variadic-fixture.sh"

# Check actual typed indirect, virtual, and pthread transfer inputs and relations.
"$ROOT/exporter/test-call-transfer-fixture.sh"

"$ROOT/exporter/test-coroutine-traits-fixture.sh"

# Coverage instrumentation injects compiler-only statements. The pinned
# interpreter discards these statements, so export the exact typed no-op tag.
"$EXPORTER" \
  --output "$NOOP_OUT" --root covered "$ROOT/exporter/fixtures/mir_noops.rs" \
  --crate-type=lib --crate-name=mir_noops -Cinstrument-coverage -Zno-profiler-runtime
python3 "$ROOT/exporter/tests/validate_noops_fixture.py" "$NOOP_OUT"
python3 "$ROOT/tools/exporter_provenance.py" \
  --document "$NOOP_OUT" \
  --exporter "$EXPORTER" \
  --manifest "$PROVENANCE_OUT" --root "$ROOT"
python3 "$ROOT/exporter/tests/validate_provenance_manifest.py" "$PROVENANCE_OUT"

# A successful root has no failed semantic payload in any emitted catalog.
"$EXPORTER" \
  --output "$SCOPE_OUT" --root add_one "$ROOT/exporter/fixtures/scope/simple.rs" \
  --crate-type=lib --crate-name=scoped_closure
python3 "$ROOT/exporter/tests/validate_scope_fixture.py" "$SCOPE_OUT"
"$EXPORTER" \
  --output "$VIRTUAL_SCOPE_OUT" --root call_trait_object \
  "$ROOT/exporter/fixtures/mir_features.rs" --crate-type=lib --crate-name=mir_features
python3 "$ROOT/exporter/tests/validate_virtual_scope.py" "$VIRTUAL_SCOPE_OUT"
for ROOT_NAME in missing; do
  if "$EXPORTER" \
    --output "$SCOPE_OUT" --root "$ROOT_NAME" "$ROOT/exporter/fixtures/scope/simple.rs" \
    --crate-type=lib --crate-name=scoped_closure > /dev/null 2> "$SCOPE_ERR"; then
    echo "rooted export unexpectedly accepted $ROOT_NAME" >&2
    exit 1
  fi
  grep -q 'did not resolve to a local MIR body' "$SCOPE_ERR"
done
"$EXPORTER" --output "$SCOPE_OUT" --root identity \
  "$ROOT/exporter/fixtures/scope/simple.rs" --crate-type=lib --crate-name=scoped_closure
python3 - "$SCOPE_OUT" <<'PYROOT'
import json, sys
value = json.load(open(sys.argv[1]))
assert value["body_roots"] == [] and value["bodies"] == []
assert [root["def_path"] for root in value["root_declarations"]] == ["identity"]
assert not any(row["kind"] == "instance_mir" for row in value["instances"])
PYROOT
echo "validated fail-closed rooted function selection"

# The executable must fail closed when the selected `rustc` is not the pin.
# Cargo tests inherit a pinned RUSTUP_TOOLCHAIN; keep it out of this negative case.
ERR="$(mktemp "${TMPDIR:-/tmp}/lean-miri-rustc-pin-XXXXXX.err")"
trap 'rm -f "$OUT" "$SCOPE_OUT" "$VIRTUAL_SCOPE_OUT" "$SCOPE_ERR" "$ERR" "$NOOP_OUT" "$PROVENANCE_OUT"' EXIT
if env -u RUSTUP_TOOLCHAIN PATH="$CARGO_HOME/bin:/usr/bin:/bin" RUSTUP_HOME="$RUSTUP_HOME" CARGO_HOME="$CARGO_HOME" \
  LD_LIBRARY_PATH="$SYSROOT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
  "$EXPORTER" --output "$OUT" \
  "$ROOT/exporter/fixtures/mir_features.rs" --crate-type=lib --crate-name=mir_features \
  > /dev/null 2> "$ERR"; then
  echo "exporter unexpectedly accepted a non-pinned rustc" >&2
  exit 1
fi
grep -q "expected pinned rustc 8eb778d04094d3af4b26580cab327e0413eb1e02" "$ERR"
echo "validated fail-closed compiler revision check"

# Exercise rustc-wrapper mode with a path dependency. The application can only
# export the helper's private MIR if the dependency was compiled with encoded MIR.
CARGO_TARGET_BASE="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-cargo-target-XXXXXX")"
trap 'rm -f "$OUT" "$SCOPE_OUT" "$VIRTUAL_SCOPE_OUT" "$SCOPE_ERR" "$ERR" "$NOOP_OUT" "$PROVENANCE_OUT"; rm -rf "$CARGO_TARGET_BASE"' EXIT
if [[ -n "${MIRI_SYSROOT:-}" ]]; then
  CARGO_TARGET_DIR="$CARGO_TARGET_BASE" "$EXPORTER" \
    --cargo --root external_generic_call --root external_std_call build --lib -p exporter-cargo-app --offline \
    --manifest-path "$ROOT/exporter/fixtures/cargo-external/Cargo.toml"
elif [[ -d "$ROOT/scratch/lake/miri-sysroot" ]]; then
  MIRI_SYSROOT="$ROOT/scratch/lake/miri-sysroot" CARGO_TARGET_DIR="$CARGO_TARGET_BASE" \
    "$EXPORTER" \
    --cargo --root external_generic_call --root external_std_call build --lib -p exporter-cargo-app --offline \
    --manifest-path "$ROOT/exporter/fixtures/cargo-external/Cargo.toml"
  export MIRI_SYSROOT="$ROOT/scratch/lake/miri-sysroot"
else
  CARGO_TARGET_DIR="$CARGO_TARGET_BASE" "$EXPORTER" \
    --cargo --root external_generic_call --root external_std_call build --lib -p exporter-cargo-app --offline \
    --manifest-path "$ROOT/exporter/fixtures/cargo-external/Cargo.toml"
fi
python3 "$ROOT/exporter/tests/validate_cargo_fixture.py" \
  "$CARGO_TARGET_BASE/lean-miri-exporter-8eb778d04094"
