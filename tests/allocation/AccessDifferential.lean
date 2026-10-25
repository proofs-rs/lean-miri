import Miri.Memory.Access

open Miri.ABI
open Miri.Memory

private def mkSize (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def target64 : PointerArithmetic := ⟨mkSize 8⟩
private def mkId : IO AllocId :=
  match AllocId.ofUInt64 1 with
  | some id => pure id
  | none => throw (IO.userError "test allocation ID 1 was rejected")

private def mkPointer {Prov : Type} (provenance : Option Prov) (offset : Nat) :
    Pointer (Option Prov) := ⟨mkSize offset, provenance⟩

private def resolveConcrete (pointer : Pointer (Option Provenance)) (_size : Int) :
    Except UInt64 (ResolvedPointer Unit) :=
  match pointer.provenance with
  | some (.concrete id _) => .ok ⟨id, pointer.offset, ()⟩
  | some .wildcard | none => .error pointer.offset.bytes

inductive RelativeTestProvenance where
  | concrete (id : AllocId)
  deriving DecidableEq, Repr

instance : PointerProvenance RelativeTestProvenance where
  offsetIsAddr := false
  wildcard := none
  getAllocId
    | .concrete id => some id

inductive AbsoluteTestProvenance where
  | concrete (id : AllocId)
  deriving DecidableEq, Repr

instance : PointerProvenance AbsoluteTestProvenance where
  offsetIsAddr := true
  wildcard := none
  getAllocId
    | .concrete id => some id

private def resolveRelative (pointer : Pointer (Option RelativeTestProvenance)) (_size : Int) :
    Except UInt64 (ResolvedPointer Unit) :=
  match pointer.provenance with
  | some (.concrete id) => .ok ⟨id, pointer.offset, ()⟩
  | none => .error pointer.offset.bytes

private def resolveAbsolute (pointer : Pointer (Option AbsoluteTestProvenance)) (_size : Int) :
    Except UInt64 (ResolvedPointer Unit) :=
  match pointer.provenance with
  | some (.concrete id) => .ok ⟨id, pointer.offset, ()⟩
  | none => .error pointer.offset.bytes

private def mkInfo (size align : Nat) (kind : AllocationKind := .liveData) : AllocationInfo :=
  ⟨mkSize size, ⟨Nat.log2 align⟩, kind, .Mut⟩

private def showBounds (result : Except AccessError (Option (CheckedPointerAccess Unit))) : String :=
  match result with
  | .ok none => "N"
  | .ok (some access) =>
    s!"O{access.pointer.allocId.value}:{access.pointer.offset.bytes.toNat}:{access.allocation.size.bytes.toNat}:{(match Align.bytes access.allocation.align with | .ok b => b.toNat | .error _ => 0)}"
  | .error (.danglingIntegerPointer address size _) => s!"D{address}:{size}"
  | .error (.allocationLookup (.deadAllocation id)) => s!"F{id.value}"
  | .error (.pointerOutOfBounds id allocSize offset size _) =>
    s!"B{id.value}:{allocSize.bytes.toNat}:{offset}:{size}"
  | .error error => s!"E{error}"

private def showMisalignment (result : Except AccessError (Option Misalignment)) : String :=
  match result with
  | .ok none => "N"
  | .ok (some misalignment) =>
    let has := match Align.bytes misalignment.has with | .ok value => value.toNat | .error _ => 0
    let required := match Align.bytes misalignment.required with | .ok value => value.toNat | .error _ => 0
    s!"M{has}:{required}"
  | .error error => s!"E{error}"

private def emitBounds (tag : String) (id : AllocId) (offset : Nat)
    (signedSize : Int) (resolution : PointerResolver Provenance Unit)
    (lookup : LiveAllocationLookup) : IO Unit := do
  let pointer := mkPointer (some (.concrete id BorTag.one)) offset
  let result := checkAndDerefPtr target64 pointer signedSize .memoryAccess resolution lookup
  IO.println s!"B {tag} {showBounds result}"

private def emitMisalignment {Prov : Type} [PointerProvenance Prov]
    (tag : String) (pointer : Pointer (Option Prov))
    (required : Align) (enforce : Bool)
    (resolution : PointerResolver Prov Unit) (id : AllocId)
    (info : AllocationInfo) : IO Unit := do
  let lookup : AllocId → Except AllocationLookupError AllocationInfo := fun actual =>
    if actual == id then .ok info else .error (.unavailable actual)
  let result := isPtrMisaligned pointer required enforce resolution lookup
    (fun _ _ _ _ _ => none)
  IO.println s!"M {tag} {showMisalignment result}"

def main : IO Unit := do
  let id ← mkId
  let live : LiveAllocationLookup := fun actual =>
    if actual == id then .ok (mkInfo 8 8)
    else .error (.unavailable actual)
  let dead : LiveAllocationLookup := fun actual =>
    if actual == id then .error (.deadAllocation id)
    else .error (.unavailable actual)
  emitBounds "zero" id 0 0 (fun _ _ => .error 77) live
  emitBounds "positive_ok" id 2 3 resolveConcrete live
  emitBounds "positive_oob" id 7 2 resolveConcrete live
  emitBounds "negative_ok" id 5 (-3) resolveConcrete live
  emitBounds "negative_underflow" id 2 (-3) resolveConcrete live
  emitBounds "negative_end_oob" id 9 (-1) resolveConcrete live
  emitBounds "offset_high_oob" id 18446744073709551615 1 resolveConcrete live
  emitBounds "dangling" id 4 1 (fun _ _ => .error 77) live
  emitBounds "dead" id 1 1 resolveConcrete dead

  let relativeInfo := mkInfo 16 8
  emitMisalignment "disabled" (mkPointer (Prov := RelativeTestProvenance) none 3) ⟨3⟩ false
    (fun _ _ => .error 3) id relativeInfo
  emitMisalignment "one" (mkPointer (Prov := RelativeTestProvenance) none 3) Align.ONE true
    (fun _ _ => .error 3) id relativeInfo
  emitMisalignment "address" (mkPointer (Prov := RelativeTestProvenance) none 3) ⟨3⟩ true
    (fun _ _ => .error 3) id relativeInfo
  emitMisalignment "relative_offset" (mkPointer (some (.concrete id)) 3) ⟨2⟩ true
    resolveRelative id relativeInfo
  emitMisalignment "allocation_align" (mkPointer (some (.concrete id)) 8) ⟨3⟩ true
    resolveRelative id (mkInfo 16 4)
  emitMisalignment "aligned" (mkPointer (some (.concrete id)) 8) ⟨3⟩ true
    resolveRelative id (mkInfo 16 8)

  let absInfo := mkInfo 16 16
  let absPointer := mkPointer (some (.concrete id)) 3
  emitMisalignment "absolute" absPointer ⟨3⟩ true resolveAbsolute id absInfo
