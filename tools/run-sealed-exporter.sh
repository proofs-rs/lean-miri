#!/usr/bin/env bash
# Execute a caller-selected immutable exporter after verifying its build seal.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
TOOLCHAIN="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$TOOLCHAIN/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$TOOLCHAIN/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
: "${MIRI_SEALED_EXPORTER:?set the sealed exporter binary path}"
: "${MIRI_SEALED_EXPORTER_MANIFEST:?set its source-seal JSON manifest path}"
python3 - "$MIRI_SEALED_EXPORTER" "$MIRI_SEALED_EXPORTER_MANIFEST" <<'PY'
import hashlib,json,pathlib,sys
binary,manifest=map(pathlib.Path,sys.argv[1:])
seal=json.loads(manifest.read_text())
if (seal.get('build_exit') != 0 or not isinstance(seal.get('before'),dict)
        or not seal['before'] or seal.get('before') != seal.get('after')):
    raise SystemExit('sealed exporter build failed or source changed during build')
if hashlib.sha256(binary.read_bytes()).hexdigest() != seal.get('binary_sha256'):
    raise SystemExit('sealed exporter binary SHA-256 differs from manifest')
PY
exec "$MIRI_SEALED_EXPORTER" "$@"
