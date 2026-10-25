import Miri.Memory.ProvenanceMap

open Miri.Memory Miri.ABI

private def fixture [PointerProvenance Prov] (mk : UInt64 → Prov) (scenario : Nat) :
    Except ProvenanceMapError (ProvenanceMap Prov) := Id.run do
  let mut ptrs := #[]
  let mut fragments := none
  if scenario == 1 || scenario == 2 || scenario == 10 then
    ptrs := ptrs.push (Size.ofBytes 8, mk 1)
  if scenario == 2 then ptrs := ptrs.push (Size.ofBytes 24, mk 2)
  if 3 ≤ scenario && scenario ≤ 9 then
    let mut values := #[]
    for idx in [:8] do
      if scenario == 4 && idx ≥ 4 then break
      let mut prov := if scenario == 5 && idx == 3 then mk 2 else mk 1
      if scenario == 8 || (scenario == 9 && idx % 2 == 0) then
        if let some wildcard := PointerProvenance.wildcard (Prov := Prov) then
          prov := wildcard
      let index := if scenario == 6 && idx == 4 then 0 else idx
      let bytes : Vector UInt8 8 := Vector.ofFn fun bit =>
        if scenario == 7 && idx == 2 && bit.val == 0 then 1 else 0
      let frag : PointerFrag Prov := ⟨UInt8.ofNat index, prov, bytes⟩
      values := values.push (Size.ofBytes (UInt64.ofNat (8 + idx)), frag)
    fragments := some values
  if scenario == 10 then
    fragments := some #[(Size.ofBytes 0, ⟨0, mk 2, Vector.replicate 8 0⟩)]
  return ProvenanceMap.fromParts ptrs fragments

private def run [DecidableEq Prov] [PointerProvenance Prov]
    (flavor : String) (mk : UInt64 → Prov) (code : Prov → String) : IO Unit := do
  for scenario in [:11] do
    let .ok map := fixture mk scenario | throw (IO.userError "invalid fixture")
    for offset in ([0, 7, 8, 9, 15, 16, 24, 25] : List UInt64) do
      let read := match map.readPtr (Size.ofBytes offset) (Size.ofBytes 8) with
        | .ok (some prov) => code prov
        | .ok none => "none"
        | .error (.readPartialPointer _) => "partial"
        | .error _ => "panic"
      IO.println s!"read {flavor} {scenario} {offset} {read}"
      for len in ([0, 1, 7, 8, 9] : List UInt64) do
        let range := allocRange (Size.ofBytes offset) (Size.ofBytes len)
        let empty := match map.rangeEmpty range (Size.ofBytes 8) with
          | .ok result => toString result
          | .error _ => "panic"
        let entries := match map.getRange range (Size.ofBytes 8) with
          | .error _ => "panic"
          | .ok entries => String.intercalate "," (entries.toList.map fun (entry : AllocRange × Prov) => s!"{entry.1.start.bytes}:{entry.1.size.bytes}:{code entry.2}")
        IO.println s!"range {flavor} {scenario} {offset} {len} {empty} {entries}"
    let snapshot := fun (state : ProvenanceMap Prov) =>
      let ptrs := String.intercalate "," (state.ptrs.toList.map fun (entry : Size × Prov) => s!"{entry.1.bytes}:{code entry.2}")
      let frags := match state.byteFragments with
        | none => "none"
        | some values => "some[" ++ String.intercalate "," (values.toList.map fun (entry : Size × PointerFrag Prov) =>
            s!"{entry.1.bytes}:{entry.2.idx}:{code entry.2.prov}:" ++ String.intercalate "." (entry.2.bytes.toArray.toList.map toString)) ++ "]"
      s!"p[{ptrs}]b[{frags}]"
    let data : Array UInt8 := (List.range 64).toArray.map UInt8.ofNat
    let (merged, result) := match ProvenanceMap.mergeBytes (Size.ofBytes 8) map with
      | .ok value state => (state, toString value)
      | .error _ state => (state, "panic")
    IO.println s!"merge {flavor} {scenario} {result} {snapshot merged}"
    for offset in ([0, 7, 8, 9, 15, 16, 24, 25] : List UInt64) do
      for len in ([0, 1, 7, 8, 9] : List UInt64) do
        for operation in ["clear", "wildcard"] do
          let range := allocRange (Size.ofBytes offset) (Size.ofBytes len)
          let computation := if operation == "clear" then ProvenanceMap.clear range data (Size.ofBytes 8)
                             else ProvenanceMap.writeWildcards range data (Size.ofBytes 8)
          let (next, result) := match computation map with
            | .ok _ state => (state, "ok")
            | .error _ state => (state, "panic")
          IO.println s!"mutate {flavor} {scenario} {operation} {offset} {len} {result} {snapshot next}"
        for repeats in ([0, 1, 2] : List UInt64) do
          let range := allocRange (Size.ofBytes offset) (Size.ofBytes len)
          let target := allocRange (Size.ofBytes 40) (Size.ofBytes len)
          let (next, result) := match map.prepareCopy range data (Size.ofBytes 8) with
            | .error _ => (ProvenanceMap.new, "panic")
            | .ok copy =>
              match ProvenanceMap.applyCopy copy target repeats ProvenanceMap.new with
              | .ok _ state => (state, "ok")
              | .error _ state => (state, "panic")
          IO.println s!"copy {flavor} {scenario} {offset} {len} {repeats} {result} {snapshot next}"

def main : IO Unit := do
  let id1 : AllocId := ⟨1, by decide⟩
  let id2 : AllocId := ⟨2, by decide⟩
  let m1 := Provenance.concrete id1 BorTag.one
  let m2 := Provenance.concrete id2 BorTag.one
  run "m" (fun n => if n == 1 then m1 else m2) (fun p => match p with
    | .concrete id _ => s!"c{id.value}"
    | .wildcard => "w")
  let .ok c1 := CtfeProvenance.fromAllocId id1 | throw (IO.userError "invalid CTFE id")
  let .ok c2 := CtfeProvenance.fromAllocId id2 | throw (IO.userError "invalid CTFE id")
  run "c" (fun n => if n == 1 then c1 else c2) (fun p => s!"c{p.allocId.value}")
