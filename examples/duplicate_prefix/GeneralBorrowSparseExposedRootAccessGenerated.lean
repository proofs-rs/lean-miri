import duplicate_prefix.GeneralBorrowSparseExposedRootAccessResources
import duplicate_prefix.GeneralBorrowProtectorCacheMap
namespace DuplicatePrefix.GeneralBorrowSparseExposedRootAccessGenerated
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedRootFormation GeneralBorrowSparseExposedRootHistory GeneralBorrowSparseExposedLeafState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

def formedHistory (capacity : UInt64) (nonzero : capacity≠0) (windows : List (Window capacity))
    (room : windows.length+9<65536) :=
  GeneralBorrowSparseExposedRootAccessHistory.formed capacity nonzero windows (by omega)

/-- Canonical actual root allocation/exposure, partial-root constructor/exposure
history and bounded NONE Read/Write suffix. No final permission or success input. -/
def source (capacity : UInt64) (nonzero : capacity≠0) (windows : List (Window capacity))
    (room : windows.length+9<65536) (events : List (GeneralBorrowSparseExposedLeafHistory.Event capacity)) : State capacity :=
  GeneralBorrowSparseExposedRootAccessResources.finish (formedHistory capacity nonzero windows room).state events

private theorem allocation_protections (before after : GlobalState) (tag : BorTag)
    (actual : before.newPointerTag=.ok (after,tag)) : after.protectedTags=before.protectedTags := by
  unfold GlobalState.newPointerTag at actual
  split at actual
  · cases actual
  · cases actual;rfl

private theorem trace_protections {capacity} {before after : State capacity} {windows : List (Window capacity)}
    (actual : Trace before windows after) : after.global.protectedTags=before.global.protectedTags := by
  induction actual with
  | nil=>rfl
  | cons one tail ih=>exact ih.trans (allocation_protections _ _ _ one.allocated)

private theorem node_below {capacity} (s : State capacity) (index : UniIndex) (node : TreeNode)
    (present : s.tree.nodeAt index=some node) : node.tag.value.toNat<s.global.nextPointerTag.value.toNat := by
  have lookup:=s.structural.allocator.nodeTags index node present
  unfold UniKeyMap.get at lookup
  cases found : s.tree.tagMapping.mapping.find? (fun row=>row.1==node.tag) with
  | none=>simp only [found,Option.map_none] at lookup;cases lookup
  | some row=>
    have equal : row.1=node.tag := by simpa only [beq_iff_eq] using Array.find?_some found
    have bounded:=s.below row (Array.mem_of_find?_eq_some found)
    rw [equal] at bounded
    exact bounded

variable (capacity : UInt64) (nonzero : capacity≠0) (windows : List (Window capacity))
  (room : windows.length+9<65536) (events : List (GeneralBorrowSparseExposedLeafHistory.Event capacity))

theorem tree_eq : (source capacity nonzero windows room events).tree=
    (GeneralBorrowSparseExposedLeafHistory.run
      (GeneralBorrowSparseExposedRootHistory.State.toAccess (formedHistory capacity nonzero windows room).state) events).tree := rfl

theorem global_eq : (source capacity nonzero windows room events).global=(formedHistory capacity nonzero windows room).state.global := rfl

theorem size : (source capacity nonzero windows room events).tree.nodes.size=1+windows.length := by
  rw [tree_eq,GeneralBorrowSparseExposedRootAccessResources.run_frame]
  have growth:=(formedHistory capacity nonzero windows room).growth
  have initial : (seeded capacity nonzero).tree.nodes.size=1:=rfl
  exact growth.trans (by rw [initial])

theorem counter : (source capacity nonzero windows room events).global.nextPointerTag.value.toNat=2+windows.length := by
  rw [global_eq]
  have actual:=(formedHistory capacity nonzero windows room).counter
  have initial : (seeded capacity nonzero).global.nextPointerTag.value.toNat=2:=rfl
  exact actual.trans (by rw [initial])

theorem nodeRoom : (source capacity nonzero windows room events).tree.nodes.size+8<65536 := by
  rw [size];omega

theorem emptyProtections : (source capacity nonzero windows room events).global.protectedTags={} := by
  rw [global_eq]
  exact (trace_protections (formedHistory capacity nonzero windows room).actual).trans (show (seeded capacity nonzero).global.protectedTags={} from rfl)

theorem fresh (tag : BorTag)
    (above : (source capacity nonzero windows room events).global.nextPointerTag.value.toNat≤tag.value.toNat) :
    GeneralBorrowTagMap.Fresh (source capacity nonzero windows room events).tree.tagMapping tag :=
  GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ (source capacity nonzero windows room events).below tag above

theorem allLeaves :
    ∀ root∈(source capacity nonzero windows room events).primary::(source capacity nonzero windows room events).extras,
      ∃ node,(source capacity nonzero windows room events).tree.nodeAt root=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
        node.tag.value≤(source capacity nonzero windows room events).global.nextPointerTag.value := by
  intro root member
  let s:=source capacity nonzero windows room events
  obtain ⟨node,present⟩:=s.geometry.present root member
  have shape:=s.geometry.nodes root node present
  exact ⟨node,present,shape.2.1,shape.2.2,UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (node_below s root node present))⟩

/-- Registering the genuinely fresh current tag changes no existing exposed
node's held flag. Actual scalar legality and coherent counters are transported,
without a final sourceRaw or successful callback premise. -/
theorem registeredRaw :
    GeneralRangeMapState.Every (fun location=>Raw (source capacity nonzero windows room events).tree location
      ((source capacity nonzero windows room events).global.protectedTags.insert
        (source capacity nonzero windows room events).global.nextPointerTag .StrongProtector))
      (source capacity nonzero windows room events).tree.locations := by
  let s:=source capacity nonzero windows room events
  have same : ∀ index node,s.tree.nodeAt index=some node→
      (s.global.protectedTags.insert s.global.nextPointerTag .StrongProtector).contains node.tag=s.global.protectedTags.contains node.tag := by
    intro index node present
    have different : node.tag≠s.global.nextPointerTag := by
      intro equal
      have bounded:=node_below s index node present
      rw [equal] at bounded;omega
    unfold ProtectedTags.contains
    rw [GeneralBorrowProtectorCacheMap.insert_other _ _ _ _ different]
  intro position valid
  have raw:=s.raw position valid
  refine ⟨GeneralBorrowProtectorCacheMap.frame s.tree _ _ _ raw.1 (fun index node present _=>same index node present),?_⟩
  intro index node present
  rw [same index node present]
  exact raw.2 index node present

/-- A witness records the actual finite source trace, rather than choosing one
of pre-existing successful whole-call families. Its graph/permission fields
are computed by `source`; the physical caller is supplied separately. -/
structure Generated where
  state : State capacity
  stateEq : state=source capacity nonzero windows room events
  empty : state.global.protectedTags={}
  capacityNonzero : capacity≠0
  allocated : GlobalState.new.rootPointerTag GeneralBorrowProtectedLifetimeSeed.allocation=
    .ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one)
  rootExposed : (BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
    ⟨(seeded capacity nonzero).tree,.ok ()⟩
  constructors : Trace (seeded capacity nonzero) windows (formedHistory capacity nonzero windows room).state
  accesses : GeneralBorrowSparseExposedLeafHistory.Trace
    (GeneralBorrowSparseExposedRootHistory.State.toAccess (formedHistory capacity nonzero windows room).state) events
    (GeneralBorrowSparseExposedLeafHistory.run
      (GeneralBorrowSparseExposedRootHistory.State.toAccess (formedHistory capacity nonzero windows room).state) events)
  actual : state.tree=(GeneralBorrowSparseExposedLeafHistory.run
      (GeneralBorrowSparseExposedRootHistory.State.toAccess (formedHistory capacity nonzero windows room).state) events).tree

def build : Generated capacity nonzero windows room events := by
  have actual:=GeneralBorrowSparseExposedRootAccessHistory.executes capacity nonzero windows (by omega) events
  exact ⟨source capacity nonzero windows room events,rfl,emptyProtections capacity nonzero windows room events,nonzero,actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,rfl⟩

end
end DuplicatePrefix.GeneralBorrowSparseExposedRootAccessGenerated
