#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
OUT="${HIGHER_RANKED_BOUND_ALIASES_OUT:-$ROOT/scratch/higher-ranked-bound-aliases}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
bash tools/export-mir.sh --output "$OUT/source.json" --root higher_ranked_alias_root -- \
  tests/repro/compiler-queries/higher-ranked-bound-aliases.rs --crate-type=lib --crate-name=higher_ranked_bound_aliases
TEMP_DIR="$(mktemp -d /tmp/lean-miri-higher-ranked-alias.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 --cfg=higher_ranked_bound_alias_oracle tools/higher-ranked-trait-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json, pathlib, subprocess, sys
oracle, out = sys.argv[1], pathlib.Path(sys.argv[2])
source = json.loads((out / 'source.json').read_text())
with (out / 'oracle.json').open('w') as stdout, (out / 'oracle.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout,
                   stderr=stderr, check=True, timeout=90)
rows = json.loads((out / 'oracle.json').read_text())
next(row for row in rows if row['name'] == 'static_only')['accepted'] = True
(out / 'wrong-oracle.json').write_text(json.dumps(rows))
PY
if [[ "${HIGHER_RANKED_BOUND_ALIASES_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.AliasRuntime Miri.Input.Decoder
fi
lake env lean tests/compiler_queries/QueryAliasOwnership.lean
lake env lean --run tests/compiler_queries/HigherRankedBoundAliases.lean "$OUT/source.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/HigherRankedBoundAliases.lean "$OUT/source.json" \
    "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  printf 'mutated scoped alias oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'scoped alias trait result differs from rustc: static_only' "$OUT/wrong-oracle.log"
printf 'scoped alias static-only mutated oracle rejection PASS\n'
