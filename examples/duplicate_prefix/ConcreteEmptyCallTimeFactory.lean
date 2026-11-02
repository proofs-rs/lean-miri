import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.ConcreteEmptyPoolContinuationData
import duplicate_prefix.ConcreteEmptyRuntimeEntry
import duplicate_prefix.GenericFunctionEntryNumerics
import duplicate_prefix.PositiveRootInvocationState
namespace DuplicatePrefix.ConcreteEmptyCallTimeFactory
open Miri Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open DuplicatePrefixCallSpecification DuplicatePrefixEmptyReferenceInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Actual checked counter stages required by the existing empty-call family.
The payload consists only of initial numeric consequences of the resource bound. -/
structure Tags (tracker : MachineHooks.BorrowState) where
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  slotFresh : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value < 18446744073709551615
  thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615

def tags (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value.toNat+16 < 2^64) : Tags tracker := by
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr;change tracker.global.nextPointerTag.value.toNat < 18446744073709551615;omega
  have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  change (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
  have secondFresh : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr;change (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value.toNat < 18446744073709551615;omega
  have second := GenericFunctionEntryNumerics.successor_value (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag secondFresh
  change (PositiveRootInvocationState.held tracker fresh secondFresh).global.nextPointerTag.value.toNat = (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value.toNat+1 at second
  have thirdFresh : (PositiveRootInvocationState.held tracker fresh secondFresh).global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr;change (PositiveRootInvocationState.held tracker fresh secondFresh).global.nextPointerTag.value.toNat < 18446744073709551615;omega
  have third := GenericFunctionEntryNumerics.successor_value (PositiveRootInvocationState.held tracker fresh secondFresh).global.nextPointerTag thirdFresh
  change (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh secondFresh) thirdFresh).global.nextPointerTag.value.toNat = (PositiveRootInvocationState.held tracker fresh secondFresh).global.nextPointerTag.value.toNat+1 at third
  have fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh secondFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr;change (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh secondFresh) thirdFresh).global.nextPointerTag.value.toNat < 18446744073709551615;omega
  exact ⟨fresh,secondFresh,thirdFresh,fourthFresh⟩

def Tags.shared (tracker : MachineHooks.BorrowState) (t : Tags tracker) : BorTag :=
  (PositiveRootInvocationState.held tracker t.fresh t.slotFresh).global.nextPointerTag
def Tags.len (tracker : MachineHooks.BorrowState) (t : Tags tracker) : BorTag :=
  (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker t.fresh t.slotFresh) t.thirdFresh).global.nextPointerTag

theorem Tags.values (tracker : MachineHooks.BorrowState) (t : Tags tracker) :
    (t.shared tracker).value.toNat = tracker.global.nextPointerTag.value.toNat+2 ∧
    (t.len tracker).value.toNat = tracker.global.nextPointerTag.value.toNat+3 := by
  have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag t.fresh
  change (PositiveRootInvocationState.next tracker t.fresh).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
  have second := GenericFunctionEntryNumerics.successor_value (PositiveRootInvocationState.next tracker t.fresh).global.nextPointerTag t.slotFresh
  change (t.shared tracker).value.toNat = (PositiveRootInvocationState.next tracker t.fresh).global.nextPointerTag.value.toNat+1 at second
  have third := GenericFunctionEntryNumerics.successor_value (t.shared tracker) t.thirdFresh
  change (t.len tracker).value.toNat = (t.shared tracker).value.toNat+1 at third
  constructor <;> omega

/-- The return-slot tag is the intermediate allocated tag t+1, and cannot
collide with the actual len-reference tag t+3. -/
theorem Tags.slot_not_len (tracker : MachineHooks.BorrowState) (t : Tags tracker) :
    (PositiveRootInvocationState.next tracker t.fresh).global.nextPointerTag ≠ t.len tracker := by
  have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag t.fresh
  change (PositiveRootInvocationState.next tracker t.fresh).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
  have last := (t.values tracker).2
  intro same
  have equal := congrArg (fun x : BorTag => x.value.toNat) same
  omega

/-- The same initial tag-map highwater discharges future-tag freshness for
any live allocation, including the return allocation's original tag. -/
theorem fresh_at_or_above (tree : BorrowTree) (global : GlobalState)
    (below : GeneralBorrowForestTagHighWater.Below tree global.protectedTags global.nextPointerTag)
    (tag : BorTag) (atLeast : global.nextPointerTag.value.toNat ≤ tag.value.toNat) :
    GeneralBorrowTagMap.Fresh tree.tagMapping tag := by
  intro row member same
  have bounded := below.mapping row member
  have equal := congrArg (fun x : BorTag => x.value.toNat) same
  omega

/-- The concrete live parent fact follows from the existing TargetMetadata
candidate, rather than being supplied as a post-state or constructor success. -/
theorem live_parent {K : Type} (context : ImageContext)
    (memory : MemoryState Provenance BorrowTree K) (addresses : AllocAddresses.GlobalAddressState)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree K)
    (target : TargetMetadata context memory addresses id (some tag))
    (live : memory.live.find? (fun row => row.1 == id) = some (id,entry)) : Parent entry.allocation.extra (some tag) := by
  rcases target with known | image
  · cases known with
    | live entry' present parent => cases Option.some.inj (present.symm.trans live);exact parent
    | functionRow absent present => rw [live] at absent;cases absent
    | vaListRow absent noFunction present => rw [live] at absent;cases absent
    | nondataGlobal descriptor absent noFunction noVaList present kind => rw [live] at absent;cases absent
    | dead deadEntry absent noFunction noVaList noGlobal present => rw [live] at absent;cases absent
  · obtain ⟨source,root,absent,_⟩ := image
    rw [live] at absent
    cases absent

/-- All pool/depth/Clean/high-water continuation data is DERIVED from the
existing runtime/resource record and initial parent lookup. No future state,
operation success, preselected allocator slot or empty free pool is an input. -/
def continuation (before : Before) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixRuntimeInput.State before tracker)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (resources : Resources options limits remaining before tracker 0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (parentTag : BorTag) (parent : Parent entry.allocation.extra (some parentTag)) :
    ConcreteEmptyPoolContinuationData.Input entry.allocation.extra parentTag tracker.global.nextPointerTag
      ((tags tracker resources.tagRoom).shared tracker) ((tags tracker resources.tagRoom).len tracker) := by
  let anchor : UniIndex := Classical.choose parent
  let node : TreeNode := Classical.choose (Classical.choose_spec parent)
  have facts := Classical.choose_spec (Classical.choose_spec parent)
  have tagged : entry.allocation.extra.indexOfTag parentTag = some anchor := facts.1
  have present : entry.allocation.extra.nodeAt anchor = some node := facts.2
  have member : (id,entry) ∈ before.memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have formed := runtime.formed (id,entry) member
  have below := resources.tagsBelow (id,entry) member
  let t := tags tracker resources.tagRoom
  obtain ⟨sharedValue,lenValue⟩ := t.values tracker
  have fresh (tag : BorTag) (bound : tracker.global.nextPointerTag.value.toNat ≤ tag.value.toNat) : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag := by
    intro row rowMember same
    have smaller := below.mapping row rowMember
    have equal := congrArg (fun x : BorTag => x.value.toNat) same
    omega
  have different (left right : BorTag) (bound : left.value.toNat ≠ right.value.toNat) : left ≠ right := fun equal => bound (congrArg (fun x : BorTag => x.value.toNat) equal)
  exact {
    parent := anchor,parentNode := node,tagged := tagged,present := present,
    depth := Classical.choice formed.depth,pool := formed.allocator.pool,accounting := formed.allocator.accounting,
    clean := GeneralBorrowStructuralHistorySifaState.vacant_clean _ _ formed,
    rootFresh := fresh _ (Nat.le_refl _),sharedFresh := fresh _ (by omega),lenFresh := fresh _ (by omega),
    rootShared := different _ _ (by omega),rootLen := different _ _ (by omega),sharedLen := different _ _ (by omega),
    room := by have bounded := resources.nodeRoom (id,entry) member;dsimp only at bounded;omega }
/-- Concrete-live candidate dispatch data at the SAME address/id/tag. Empty
references need no offset containment or initialized backing byte. -/
theorem candidate_live (before : Before) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixRuntimeInput.State before tracker)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (resources : Resources options limits remaining before tracker 0)
    (context : ImageContext) (address : UInt64) (id : AllocId) (tag : BorTag)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (candidate : Candidate context before.memory before.user.addresses (Pointer.new (some (.concrete id tag)) (Size.ofBytes address))) :
    ∃ base, before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
      base+(address-base)=address ∧ base+(address-base) ≠ 0 ∧
      Nonempty (ConcreteEmptyPoolContinuationData.Input entry.allocation.extra tag tracker.global.nextPointerTag
        ((tags tracker resources.tagRoom).shared tracker) ((tags tracker resources.tagRoom).len tracker)) := by
  have nonzero := candidate.1
  obtain ⟨⟨base,cached⟩,target⟩ := candidate.2
  have parent := live_parent context before.memory before.user.addresses id tag entry target live
  have addressEq : base+(address-base)=address := by rw [UInt64.add_comm,UInt64.sub_add_cancel]
  exact ⟨base,cached,addressEq,by simpa only [addressEq,Pointer.new,Size.ofBytes] using nonzero,
    ⟨continuation before tracker runtime options limits remaining resources id entry live tag parent⟩⟩

end
end DuplicatePrefix.ConcreteEmptyCallTimeFactory
