#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/exporter/tests/fixture-env.sh"
OUT="${FN_POINTER_HRTB_OUT:-$(mktemp -d /tmp/lean-miri-fnptr-hrtb.XXXXXXXX)}"
mkdir -p "$OUT"
cd "$ROOT"
if [[ -z "${EXPORTER_BIN:-}" ]]; then
  echo 'Set EXPORTER_BIN to an immutable exporter built from the current source.' >&2
  exit 2
fi
"$EXPORTER_BIN" --output "$OUT/source.json" --root roundtrip -- \
  tests/repro/compiler-queries/fn-pointer-hrtb-shims.rs --crate-type=lib \
  --crate-name=fn_pointer_hrtb_shims -Cpanic=abort --edition=2021 \
  -Zmir-opt-level=0 --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir
rustc --edition=2024 tools/fn-pointer-shim-oracle.rs -o "$OUT/oracle"
python3 - "$OUT" <<'PYCODE'
import json, os, pathlib, subprocess, sys
out = pathlib.Path(sys.argv[1])
source = json.loads((out / 'source.json').read_text())
shims = [body for body in source['bodies'] if body['body_kind'] == 'fn_pointer_shim']
assert len(shims) == 8, 'expected eight source-only higher-ranked conversion shims'
assert all('basic_blocks' not in body for body in shims), 'source shim retained computed MIR'
with (out / 'oracle.json').open('w') as stdout:
    subprocess.run([str(out / 'oracle'), *source['invocation']['rustc_args']],
                   stdout=stdout, check=True, timeout=90)
normalized_env = dict(os.environ, FN_POINTER_SHIM_NORMALIZE='1')
with (out / 'normalized-oracle.json').open('w') as stdout:
    subprocess.run([str(out / 'oracle'), *source['invocation']['rustc_args']],
                   stdout=stdout, env=normalized_env, check=True, timeout=90)
args = source['invocation']['rustc_args']
oracle_source = 'tests/repro/compiler-queries/fn-pointer-hrtb-shim-novel-oracle.rs'
args = [oracle_source if arg.endswith('fn-pointer-hrtb-shims.rs') else arg for arg in args]
assert oracle_source in args, 'production invocation omitted the source path'
with (out / 'novel-oracle.json').open('w') as stdout:
    subprocess.run([str(out / 'oracle'), *args], stdout=stdout, env=normalized_env,
                   check=True, timeout=90)
assert len(json.loads((out / 'novel-oracle.json').read_text())) == 16
wrong = json.loads((out / 'normalized-oracle.json').read_text())
wrong[0]['expected']['argument_count'] += 1
(out / 'wrong-oracle.json').write_text(json.dumps(wrong))
PYCODE
if [[ "${FN_POINTER_HRTB_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.CallResolution
fi
lake env lean --run tests/compiler_queries/FnPointerShim.lean "$OUT/oracle.json"
lake env lean --run tests/compiler_queries/FnPointerShimProduction.lean "$OUT/source.json" "$OUT/normalized-oracle.json" 8 "$OUT/novel-oracle.json"
if lake env lean --run tests/compiler_queries/FnPointerShimProduction.lean "$OUT/source.json" "$OUT/wrong-oracle.json" 8 >"$OUT/wrong-oracle.log" 2>&1; then
  echo 'incorrect FnPtr shim body oracle was accepted' >&2
  exit 1
fi
rg -q 'production shim differs from complete independent rustc body' "$OUT/wrong-oracle.log"
