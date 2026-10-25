import Miri.Memory.CtfeProvenance

open Miri.Memory Miri.ABI

private def resultCode [ToString α] : Except ε α → String
  | .ok value => toString value
  | .error _ => "panic"

private def values : List UInt64 :=
  [0, 1, 127, 128, 255, 256, 65535, 65536, 2147483648,
   9223372036854775808, 18446744073709551615]

private def pointerOffset (result : Except PointerError (Pointer Prov)) : String :=
  resultCode (result.map (fun ptr => ptr.offset.bytes))

def main : IO Unit := do
  let alloc : AllocId := ⟨3, by decide⟩
  let tag : BorTag := ⟨5, by decide⟩
  for size in ([0, 1, 2, 3, 4, 7, 8, 9, 16, 17] : List UInt64) do
    let cx : PointerArithmetic := ⟨Size.ofBytes size⟩
    IO.println s!"bounds {size} {resultCode cx.targetUsizeMax} {resultCode cx.targetIsizeMin} {resultCode cx.targetIsizeMax}"
    for value in values do
      IO.println s!"arithmetic {size} {value} {resultCode (cx.truncateToTargetUsize value)} {resultCode (cx.signExtendToTargetIsize value)}"
      for prov in ([.concrete alloc tag, .wildcard] : List Provenance) do
        let code := match prov with | .wildcard => "w" | _ => "c"
        let ptr : Pointer Provenance := .new prov (Size.ofBytes value)
        for delta in ([0, 1, 2, 18446744073709551615] : List UInt64) do
          IO.println s!"unsigned {size} {value} {code} {delta} {pointerOffset (ptr.wrappingOffset (Size.ofBytes delta) cx)}"
        for delta in ([-9223372036854775808, -65536, -1, 0, 1, 9223372036854775807] : List Int) do
          IO.println s!"signed {size} {value} {code} {delta} {pointerOffset (ptr.wrappingSignedOffset (Int64.ofInt delta) cx)}"
  for value in ([0, 1, 2, 255, 18446744073709551614, 18446744073709551615] : List UInt64) do
    let created := BorTag.ofUInt64 value
    let code := fun tag => toString (BorTag.value tag)
    IO.println s!"tag {value} {(created.map code).getD "none"} {((created.bind BorTag.succ).map code).getD "none"}"
  IO.println s!"default_tag {BorTag.one.value}"
  for value in values do
    let ptr := Pointer.withoutProvenance (Prov := Provenance) value
    let outcome := match ptr.intoPointerOrAddr with
      | .ok _ => "pointer"
      | .error addr => s!"address:{addr.bytes}"
    IO.println s!"no_provenance {value} {outcome}"
    for prov in ([.concrete alloc tag, .wildcard] : List Provenance) do
      let code := match prov with | .wildcard => "w" | _ => "c"
      let ptr : Pointer Provenance := .new prov (Size.ofBytes value)
      let allocation := ((prov.getAllocId.map AllocId.value).map toString).getD "none"
      IO.println s!"provenance {value} {code} {allocation} {resultCode (ptr.withOptionalProvenance.addr.map Size.bytes)} {(ptr.mapProvenance fun _ => .wildcard).offset.bytes}"
  for extra in ([.concrete tag, .wildcard] : List ProvenanceExtra) do
    IO.println s!"extra {((extra.andThen fun tag => some tag.value).map toString).getD "none"}"
  for id in ([1, 2, 4611686018427387903, 4611686018427387904, 9223372036854775808, 18446744073709551615] : List UInt64) do
    for immutable in [false, true] do
      for shared in [false, true] do
        let code := match AllocId.ofUInt64 id with
          | none => "panic"
          | some alloc =>
            match CtfeProvenance.fromParts (alloc, immutable, shared) with
            | .error _ => "panic"
            | .ok p =>
              let (a, i, s) := p.intoParts
              s!"{p.packed}:{a.value}:{if i then 1 else 0}:{if s then 1 else 0}:{p.asImmutable.packed}:{p.asSharedRef.packed}"
        IO.println s!"ctfe {id} {if immutable then 1 else 0} {if shared then 1 else 0} {code}"
