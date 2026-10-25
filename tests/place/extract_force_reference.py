"""Extract the pinned force_allocation body verbatim into a mock-leaf harness.
The compiler/memory leaves expose event order; this does not compare full Miri.
"""
from pathlib import Path
source = Path('upstream/rustc-source/compiler/rustc_const_eval/src/interpret/place.rs').read_text()
start = source.index('        let mplace = match place.place {', source.index('    pub fn force_allocation('))
end = source.index('\n    }', start)
body = source[start:end].replace('interp_ok(MPlaceTy { mplace, layout: place.layout })', 'Ok(MPlaceTy { mplace, layout: place.layout })')
template = Path('tests/place/force_reference.rs.in').read_text()
print(template.replace('/* EXTRACTED_BODY */', body))
