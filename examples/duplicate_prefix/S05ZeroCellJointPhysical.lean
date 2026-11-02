import duplicate_prefix.S05ZeroCellJointPacket
import duplicate_prefix.OrdinaryBorrowAuthority

/-! Physical and current-value facts for one closed call-time packet. These
facts refer to the actual generated raw W tree and the coexisting Bool backing.
They supply no operation-success, future-safety or ordinary-domain premise. -/
namespace DuplicatePrefix.S05ZeroCellJointPhysical
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix
open S05ZeroCellJointPacket
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

theorem source_physical : OrdinaryPhysicalValidity.MutU8Slice sourceEntry.allocation 0 2 :=
  S05ZeroCellCorrelatedWrite.sourceFor_physical w.tree

theorem destination_physical : OrdinaryPhysicalValidity.BoolDestination destinationEntry.allocation 0 := by
  constructor
  · constructor
    · rfl
    · rfl
    · cbv
    · change ProvenanceCopy.WellFormed (ProvenanceMap.new : ProvenanceMap Provenance) 1
      constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
  · decide
  · rfl

/-- Both physical witnesses name allocations in the SAME current machine. -/
theorem current_physical :
    before.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry) ∧
    before.memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry) ∧
    OrdinaryPhysicalValidity.MutU8Slice sourceEntry.allocation 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination destinationEntry.allocation 0 :=
  ⟨source_present,destination_present,source_physical,destination_physical⟩

theorem source_identity : sourcePointer.provenance = .concrete sourceId (tag 6) ∧
    sourcePointer.offset = Size.ofBytes 4096 := ⟨rfl,rfl⟩

theorem destination_identity : destinationPointer.provenance = .concrete destinationId (tag 7) ∧
    destinationPointer.offset = Size.ofBytes 8192 := ⟨rfl,rfl⟩

/-- The two-byte W footprint and one-byte Bool footprint are physically
nonoverlapping; allocation identity is independently distinct as well. -/
theorem distinct_footprints : sourceId ≠ destinationId ∧
    sourcePointer.offset.bytes.toNat + 2 ≤ destinationPointer.offset.bytes.toNat := by
  exact ⟨distinct_ids,by decide⟩

theorem pointer_geometry : sourcePointer.offset.bytes ≠ 0 ∧ destinationPointer.offset.bytes ≠ 0 ∧
    sourceEntry.allocation.byteSize = Size.ofBytes 2 ∧
    destinationEntry.allocation.byteSize = Size.ofBytes 1 := by
  exact ⟨by decide,by decide,rfl,rfl⟩

/-- The call argument is the concrete W pointer and length two under the
CURRENT function's actual reference layout, not an auxiliary type-ID rewrite. -/
theorem current_argument :
    (DuplicatePrefixSliceArgument.first PreparedReflection.actual.runtime.target.base argument 2).op =
      .immediate argumentValue2.imm ∧
    (DuplicatePrefixSliceArgument.first PreparedReflection.actual.runtime.target.base argument 2).layout =
      RootCompilerFacts.sliceLayout ∧
    argumentValue2.layout = RootCompilerFacts.sliceLayout := ⟨rfl,rfl,rfl⟩

theorem argument_layout_query : PreparedReflection.actual.runtime.lookup 3 = .ok argumentValue2.layout :=
  RootCompilerFacts.slice_layout_eq

theorem destination_layout_query : PreparedReflection.actual.runtime.lookup 0 = .ok place.layout :=
  RootCompilerFacts.bool_layout_eq

theorem destination_place : place.layout = RootCompilerFacts.boolLayout ∧
    place.mplace.ptr = destinationPointer.withOptionalProvenance ∧
    place.mplace.metadata = .none ∧ place.mplace.misaligned = none := ⟨rfl,rfl,rfl,rfl⟩

/-- The concrete call-time tracker imposes no protector on either allocation.
This describes the one shared tracker; no independently selected protector set
is attached to the W and Bool claims. -/
theorem current_protectors (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) : tracker.global.protectedTags = {} := by
  unfold before at enabled
  dsimp only at enabled
  cases Option.some.inj enabled
  rfl

/-- The Bool allocation has its actual root grant and Unique byte. These are
static tables; no successful Write is used as an authority assumption. -/
theorem destination_tag : destinationEntry.allocation.extra.tagMapping.get (tag 7) = some (ix 0) := by
  decide +kernel

theorem destination_permission :
    ((destinationEntry.allocation.extra.locations.entries[0]'(by decide +kernel)).data.perms.get (ix 0)) =
      some ⟨.Unique,true,.None⟩ := by decide +kernel

theorem destination_static_authority :
    OrdinaryBorrowAuthority.LocalWrite
      (((destinationEntry.allocation.extra.locations.entries[0]'(by decide +kernel)).data.perms.get (ix 0)).getD
        ⟨.Disabled,false,.None⟩) false := by
  rw [destination_permission]
  unfold OrdinaryBorrowAuthority.LocalWrite
  decide

end DuplicatePrefix.S05ZeroCellJointPhysical

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellJointPhysical." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved joint physical dependency {dependency}"
