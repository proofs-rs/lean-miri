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
python3 - "$OUT/source.json" <<'PYCODE'
import json, sys
source = json.load(open(sys.argv[1]))
shims = [instance for instance in source['instances']
         if instance['instance_kind'].get('shim_kind') in
         ('fn_pointer_as_pointer', 'fn_pointer_from_pointer')]
assert len(shims) == 8, 'expected eight concrete FnPtr conversion shims'
body_by_instance = {body['instance_id']: body for body in source['bodies']}
abi_instances = {row['instance_id'] for row in source['compiler_instance_abis']}
for shim in shims:
    instance_id = shim['instance_id']
    assert body_by_instance[instance_id]['body_kind'] == 'material'
    assert instance_id in abi_instances
PYCODE
if [[ "${FN_POINTER_HRTB_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.CallResolution Miri.Input.CompilerInstanceAbi
fi
lake env lean --run tests/compiler_queries/FnPointerShimProduction.lean "$OUT/source.json" 8
