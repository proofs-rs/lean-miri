import duplicate_prefix.GeneralBorrowForestTagHighWaterConcreteFrame
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedConcreteComplete
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedWildcardComplete
import duplicate_prefix.GeneralBorrowStructuralHistoryFrames
namespace DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryData
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestTagHighWater
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Runtime data only. Frames are actual addProtector results; no proof or
preselected future constructor tag is stored in the generated history. -/
structure Snapshot where
  tree : BorrowTree
  global : GlobalState
  frames : Array (BorTag × FrameState) := #[]

structure Invariant (state : Snapshot) : Prop where
  structural : GeneralBorrowStructuralHistoryState.State state.tree
  below : Below state.tree state.global.protectedTags state.global.nextPointerTag

structure Result where
  state : Snapshot
  completed : Bool

inductive Event where
  | allocate
  | constructor (parent : ProvenanceExtra) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
  | access (source : ProvenanceExtra) (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
  | release
  | gc (live : Array BorTag)

/-- These guards mention only reached runtime data. Fresh constructor tags
are not inputs: the real global counter allocation supplies them. -/
def Applicable (state : Snapshot) : Event → Prop
  | .allocate => state.global.nextPointerTag.value<18446744073709551615
  | .constructor parent base inside outside held =>
      state.global.nextPointerTag.value<18446744073709551615 ∧ state.tree.nodes.size+1≤4294967295 ∧
      (match parent with | .wildcard => True | .concrete tag => ∃index node,state.tree.indexOfTag tag=some index ∧ state.tree.nodeAt index=some node) ∧
      outside.isInitial=true ∧ outside.isUnique=false ∧
      (∃sifa,outside.strongestIdempotentForeignAccess held=.Access sifa) ∧
      GeneralBorrowStructuralHistoryMixedWildcard.Bounded inside base state.tree.locations.size ∧
      GeneralBorrowStructuralHistoryMixedWildcardComplete.InitialInside inside base held
  | .access _ offset len .. => offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat
  | .release => state.frames.back?.isSome=true
  | .gc live => ∀ row∈state.global.protectedTags.entries,live.contains row.1=true

/-- The optional protector is installed with the actual GlobalState API and
its returned singleton frame is retained for the later source release. -/
def register (id : AllocId) (state : Snapshot) (allocated : GlobalState) (tag : BorTag) (held : Bool) : Snapshot :=
  if held then
    let pair := allocated.addProtector {} id tag .StrongProtector
    ⟨state.tree,pair.1,state.frames.push (tag,pair.2)⟩
  else ⟨state.tree,allocated,state.frames⟩

def step (id : AllocId) (state : Snapshot) : Event → Result
  | .allocate =>
      match state.global.newPointerTag with
      | .error _ => ⟨state,false⟩
      | .ok (allocated,_) => ⟨{state with global:=allocated},true⟩
  | .constructor parent base inside outside held =>
      match state.global.newPointerTag with
      | .error _ => ⟨state,false⟩
      | .ok (allocated,tag) =>
          let registered := register id state allocated tag held
          let actual := state.tree.newChild base parent tag inside outside held
          ⟨{registered with tree:=actual.tree},actual.outcome==.ok ()⟩
  | .access source offset len kind mode =>
      let actual := state.tree.performBorrowAccessRange source offset len kind state.global.protectedTags mode
      ⟨{state with tree:=actual.tree},actual.status==.Completed⟩
  | .release =>
      match state.frames.back? with
      | none => ⟨state,false⟩
      | some (tag,frame) =>
          let actual := state.tree.releaseProtector tag state.global.protectedTags
          if actual.status==.Released then
            ⟨⟨actual.tree,state.global.endCall frame,state.frames.pop⟩,true⟩
          else ⟨{state with tree:=actual.tree},false⟩
  | .gc live =>
      let actual := state.tree.removeUnreachableTags live
      ⟨{state with tree:=actual.tree},actual.outcome==.ok ()⟩

/-- The initial history is itself an actual rootPointerTag allocation from
GlobalState.new followed by BorrowTree.new. There is no initial bound input. -/
def seed (id : AllocId) (size : Size) (tracked : Array BorTag := #[]) : Except GlobalStateError Snapshot := do
  let (global,root) ← (GlobalState.new tracked).rootPointerTag id
  pure ⟨BorrowTree.new root size,global,#[]⟩

def initial (id : AllocId) (size : Size) (tracked : Array BorTag := #[]) : Snapshot :=
  ⟨BorrowTree.new BorTag.one size,
    {nextPointerTag:=⟨2,by decide⟩,rootPointerTags:=#[(id,BorTag.one)],trackedPointerTags:=tracked},#[]⟩

theorem seed_actual (id : AllocId) (size : Size) (tracked : Array BorTag) : seed id size tracked=.ok (initial id size tracked) := by
  rfl

theorem initial_invariant (id : AllocId) (size : Size) (tracked : Array BorTag) : Invariant (initial id size tracked) := by
  refine ⟨GeneralBorrowStructuralHistorySeed.initial BorTag.one size,?_⟩
  exact GeneralBorrowForestTagHighWaterHistory.seed BorTag.one ⟨2,by decide⟩ size {} (by decide) (by simp)

/-- Current-counter freshness follows from the original stored-key bound. -/
theorem fresh (state : Snapshot) (initial : Invariant state) : GeneralBorrowTagMap.Fresh state.tree.tagMapping state.global.nextPointerTag := by
  intro row member same
  have less := initial.below.mapping row member
  have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
  omega
end DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryData
