import duplicate_prefix.GeneralBorrowForestGeneratedTagHistoryData
namespace DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryConstruct
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestTagHighWater
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def advanced (state : Snapshot) (fresh : state.global.nextPointerTag.value<18446744073709551615) : GlobalState :=
  {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag fresh}

private theorem registered_bounds (id : AllocId) (state : Snapshot) (initial : Invariant state)
    (fresh : state.global.nextPointerTag.value<18446744073709551615) (held : Bool) :
    let next := register id state (advanced state fresh) state.global.nextPointerTag held
    Below state.tree next.global.protectedTags next.global.nextPointerTag ∧
      state.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat := by
  have full := GenericTagHighWaterPreservation.register_below state.tree state.global.protectedTags state.global.nextPointerTag fresh
    (GeneralBorrowForestTagHighWater.complete _ _ _ initial.below initial.structural.allocator.nodeTags) held
  have strict : state.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag state.global.nextPointerTag fresh).value.toNat := by
    have value := GenericFunctionEntryNumerics.successor_value state.global.nextPointerTag fresh
    omega
  cases held <;> exact ⟨⟨full.mapping,full.protectors⟩,strict⟩

/-- Actual allocation, optional actual protector registration and arbitrary
mixed-map constructor all complete from reached raw applicability data. The
fresh tag is the real returned counter tag, never a caller-provided freshness
or operation-success certificate. -/
theorem constructor (id : AllocId) (state : Snapshot) (initial : Invariant state)
    (parent : ProvenanceExtra) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
    (allowed : Applicable state (.constructor parent base inside outside held)) :
    (step id state (.constructor parent base inside outside held)).completed=true ∧
      Invariant (step id state (.constructor parent base inside outside held)).state ∧
      (step id state (.constructor parent base inside outside held)).state.tree.locations.size=state.tree.locations.size := by
  obtain ⟨counterRoom,nodeRoom,parentData,initialOutside,notUnique,⟨sifa,foreign⟩,bounded,insideInitial⟩ := allowed
  let allocated := advanced state counterRoom
  let registered := register id state allocated state.global.nextPointerTag held
  have tagActual : state.global.newPointerTag=.ok (allocated,state.global.nextPointerTag) := TypedRetagEmpty.allocate_tag state.global counterRoom
  have tagFresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state initial
  have bounds := registered_bounds id state initial counterRoom held
  cases parent with
  | wildcard =>
    have checked := GeneralBorrowStructuralHistoryMixedWildcardComplete.construct state.tree initial.structural state.global.nextPointerTag tagFresh nodeRoom
      outside sifa held initialOutside notUnique foreign base inside bounded insideInitial
    have afterBelow := GeneralBorrowForestTagHighWaterCtorFrame.wildcard state.tree initial.structural.toGraphState
      registered.global.protectedTags registered.global.nextPointerTag state.global.nextPointerTag bounds.1 tagFresh nodeRoom bounds.2
      outside sifa held initialOutside notUnique foreign base inside
    have actual : step id state (.constructor .wildcard base inside outside held) =
        ⟨{registered with tree:=(state.tree.newChild base .wildcard state.global.nextPointerTag inside outside held).tree},true⟩ := by
      simp only [step,tagActual,checked.1,beq_self_eq_true]
      rfl
    rw [actual]
    exact ⟨rfl,⟨checked.2.1,afterBelow⟩,checked.2.2.1⟩
  | concrete parentTag =>
    obtain ⟨parent,node,tagged,present⟩ := parentData
    have checked := GeneralBorrowStructuralHistoryMixedConcreteComplete.construct state.tree initial.structural parentTag parent node tagged present
      state.global.nextPointerTag tagFresh nodeRoom outside sifa held initialOutside notUnique foreign base inside bounded insideInitial
    have afterBelow := GeneralBorrowForestTagHighWaterConcreteFrame.concrete state.tree initial.structural
      registered.global.protectedTags registered.global.nextPointerTag parentTag parent node tagged present state.global.nextPointerTag bounds.1 tagFresh nodeRoom bounds.2
      outside sifa held initialOutside notUnique foreign base inside
    have actual : step id state (.constructor (.concrete parentTag) base inside outside held) =
        ⟨{registered with tree:=(state.tree.newChild base (.concrete parentTag) state.global.nextPointerTag inside outside held).tree},true⟩ := by
      simp only [step,tagActual,checked.1,beq_self_eq_true]
      rfl
    rw [actual]
    exact ⟨rfl,⟨checked.2.1,afterBelow⟩,checked.2.2.1⟩
end DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryConstruct
