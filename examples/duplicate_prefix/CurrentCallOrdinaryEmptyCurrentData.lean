import duplicate_prefix.CurrentCallEmptyClassification
import duplicate_prefix.GlobalDataOnlyMaterialize
import duplicate_prefix.StaticGlobalAllocInfo

/-! Pure CURRENT-target extraction for the adopted empty-source classifier.
Offsets are reconstructed modulo UInt64; no source extent, initialization,
ownership family, or operation outcome is introduced. -/
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CurrentCallEmptyClassification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem empty_source {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place) (empty : len = 0) :
    EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer argument) := by
  rcases input.source with zero | positive
  · exact zero.2.1
  · exact False.elim (positive.1 empty)

private theorem literal (pointer : Pointer Provenance) (provenance : Provenance) (address : UInt64)
    (kind : pointer.provenance = provenance) (bits : pointer.offset.bytes = address) :
    pointer = Pointer.new provenance (Size.ofBytes address) := by
  cases pointer with
  | mk position prov =>
    cases position
    simp_all [Pointer.new, Size.ofBytes]

/-- The existing `Target.current` constructor supplies the initial metadata;
the adopted source determines the selected base and literal concrete pointer.
Compatibility fixes the cached root to the pointer's actual tag. -/
theorem concrete {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place) (empty : len = 0)
    (pointer : Pointer Provenance) (encoding : argument = .pointer pointer)
    (id : AllocId) (tag : BorTag) (provenance : pointer.provenance = .concrete id tag)
    (source : Allocation CtfeProvenance Unit) (root : BorTag)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : before.memory.hasFunctionPointer id = false) (noVaList : before.memory.hasVaListId id = false)
    (registry : InitialRegistryVacant before id) (current : CurrentPayload before id source)
    (storage : Storage source) (compiler : CompilerFormat source)
    (cachedRoot : input.tracker.global.rootTag? id = some root)
    (compatible : (some tag : Option BorTag) = none ∨ some tag = some root) :
    ∃ base offset : UInt64,
      argument = .pointer (Pointer.new (.concrete id root) (Size.ofBytes (base + offset))) ∧
      CurrentPayload before id source ∧ before.memory.live.find? (fun row => row.1 == id) = none ∧
      before.memory.hasFunctionPointer id = false ∧ before.memory.hasVaListId id = false ∧
      InitialRegistryVacant before id ∧ input.tracker.global.rootTag? id = some root ∧
      before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ ∧
      base + offset ≠ 0 ∧ Storage source ∧ CompilerFormat source := by
  have physical : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer pointer)) :=
    Eq.mp (congrArg (fun arg => EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer arg)) encoding)
      (empty_source input empty)
  simp only [DuplicatePrefixSliceArgument.placePointer, Pointer.withOptionalProvenance, provenance] at physical
  change pointer.offset.bytes ≠ 0 ∧ (∃ base, before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩) ∧ _ at physical
  obtain ⟨nonnull, ⟨base, cachedBase⟩, _⟩ := physical
  have tagEq : tag = root := by
    rcases compatible with impossible | same
    · cases impossible
    · exact Option.some.inj same
  let offset := pointer.offset.bytes - base
  have sum : base + offset = pointer.offset.bytes := by
    rw [UInt64.add_comm]
    exact UInt64.sub_add_cancel pointer.offset.bytes base
  have ptr := literal pointer (.concrete id root) (base + offset)
    (provenance.trans (congrArg (Provenance.concrete id) tagEq)) sum.symm
  exact ⟨base, offset, encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer ptr), current,
    absent, noFunction, noVaList, registry, cachedRoot, cachedBase, sum.symm ▸ nonnull, storage, compiler⟩

/-- Wildcard HIT retains the classifier's exact exposure, cached base, and
query geometry. Its known metadata size equals the CURRENT descriptor size;
no byte containment condition is needed for a zero-size reference. -/
theorem wildcard {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place) (empty : len = 0)
    (pointer : Pointer Provenance) (encoding : argument = .pointer pointer)
    (provenance : pointer.provenance = .wildcard)
    (hit : Hit before input.tracker pointer.offset.bytes)
    (source : Allocation CtfeProvenance Unit) (root : BorTag)
    (absent : before.memory.live.find? (fun row => row.1 == hit.id) = none)
    (noFunction : before.memory.hasFunctionPointer hit.id = false) (noVaList : before.memory.hasVaListId hit.id = false)
    (registry : InitialRegistryVacant before hit.id) (current : CurrentPayload before hit.id source)
    (storage : Storage source) (compiler : CompilerFormat source)
    (cachedRoot : input.tracker.global.rootTag? hit.id = some root) :
    ∃ offset : UInt64,
      argument = .pointer (Pointer.new .wildcard (Size.ofBytes (hit.base + offset))) ∧
      CurrentPayload before hit.id source ∧ before.memory.live.find? (fun row => row.1 == hit.id) = none ∧
      before.memory.hasFunctionPointer hit.id = false ∧ before.memory.hasVaListId hit.id = false ∧
      InitialRegistryVacant before hit.id ∧ input.tracker.global.rootTag? hit.id = some root ∧
      before.user.addresses.baseAddr.find? (fun row => row.allocId == hit.id) = some ⟨hit.id, hit.base⟩ ∧
      hit.base + offset ≠ 0 ∧ Storage source ∧ CompilerFormat source ∧
      WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (hit.base + offset) hit.base hit.id source.byteSize ∧
      before.user.addresses.exposed.contains hit.id = true := by
  have physical : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer pointer)) :=
    Eq.mp (congrArg (fun arg => EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer arg)) encoding)
      (empty_source input empty)
  change pointer.offset.bytes ≠ 0 ∧ _ at physical
  let offset := pointer.offset.bytes - hit.base
  have sum : hit.base + offset = pointer.offset.bytes := by
    rw [UInt64.add_comm]
    exact UInt64.sub_add_cancel pointer.offset.bytes hit.base
  have ptr := literal pointer .wildcard (hit.base + offset) provenance sum.symm
  have known : before.memory.getAllocInfo hit.id = .ok ⟨source.byteSize, source.align, .liveData, source.mutability⟩ := by
    cases current with
    | memory descriptor => exact GlobalDataOnlyMaterialize.alloc_info before hit.id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor initializer =>
      exact StaticGlobalAllocInfo.alloc_info before hit.id source definition absent noFunction noVaList descriptor
  have sizeEq : hit.info.size = source.byteSize := congrArg AllocationInfo.size (Except.ok.inj (hit.known.symm.trans known))
  refine ⟨offset, encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer ptr), current, absent,
    noFunction, noVaList, registry, cachedRoot, hit.cached, sum.symm ▸ physical.1, storage, compiler, ?_, hit.exposed⟩
  rw [sum, ← sizeEq]
  exact hit.geometry

end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentData

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyCurrentData.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty CURRENT extraction dependency {name}: {dependency}"
