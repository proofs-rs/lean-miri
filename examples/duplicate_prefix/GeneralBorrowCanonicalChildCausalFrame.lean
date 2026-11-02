import duplicate_prefix.GeneralBorrowCausalGraphFormation
import duplicate_prefix.GeneralBorrowTypedTreeUpdateCausalFrame
import duplicate_prefix.GeneralBorrowCanonicalReborrowSource
namespace DuplicatePrefix.GeneralBorrowCanonicalChildCausalFrame
open Miri Miri.Memory Miri.ABI Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows
open GeneralBorrowCanonicalReborrowSource
open TypedRetagEntry GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowTypedTreeUpdateCausalFrame GeneralBorrowCausalGraphFormation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- A saved graph snapshot during parent access. This is a local proof
invariant, not a definition of valid input or a successful operation. -/
def Snapshot (target : AllocId) (original : BorrowTree) (id : AllocId) (tree : BorrowTree) : Prop :=
  Formed tree ∧ (id=target → tree.nodes=original.nodes ∧ tree.tagMapping=original.tagMapping)

def childSuffix {K U : Type} [DecidableEq K]
    (location : RetagPipeline.ResolvedLocation) (inside : DedupRangeMap Tree.LocationState)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) : MachineHooks.M K U (Option Provenance) := do
  let tree ← typed_get_tree location.allocId
  let child := tree.newChild location.baseOffset location.parentProvenance tag inside
    policy.outsidePermission policy.protector.isSome
  typed_update_tree location.allocId child.tree
  typed_checked "reborrow child insertion" child.outcome
  return some (.concrete location.allocId tag)

def factoredReborrow {K User : Type} [DecidableEq K] (h : TypedRetag.Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : RetagPolicy.NewPermission) (tag : BorTag) :
    MachineHooks.M K User (Option Provenance) := do
  h.checkPtrAccess place.mplace.ptr size
  let location ← h.resolveAllocation place.mplace.ptr
  match location with
  | none =>
    if size.bytes != 0 then throw (.invalidProgram "nonzero reborrow without allocation")
    h.logCreation place size policy tag none
    return place.mplace.ptr.provenance
  | some location =>
    h.logCreation place size policy tag (some location)
    if let some protection := policy.protector then
      let frame ← MachineHooks.currentFrame
      let some borrowFrame := frame.extra.borrowTracker
        | throw (.invalidProgram "borrow frame missing")
      let old ← (typed_tracker (K:=K) (User:=User))
      let (global, borrowFrame) := old.global.addProtector borrowFrame location.allocId tag protection
      modify fun state => { state with machine := { state.machine with
        borrowTracker := some { old with global } } }
      MachineHooks.setCurrentFrame { frame with extra := { frame.extra with borrowTracker := some borrowFrame } }
    let info ← typed_checked "allocation kind" ((← get).machine.memory.getAllocInfo location.allocId)
    let provenance := some (Provenance.concrete location.allocId tag)
    if info.kind != .liveData then
      if size.bytes != 0 then throw (.invalidProgram "nonlive allocation with nonzero reborrow")
      return provenance
    let inside ← typed_inside h budget place size policy
    h.ensureTreeExtra location.allocId
    let _ ← forIn inside.iterAll () (fun segment _ => sourceSegment location segment)
    childSuffix location inside policy tag

/-- This factorization is the unchanged canonical source computation. -/
theorem source_equation {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (size : Size) (policy : RetagPolicy.NewPermission) (tag : BorTag) :
    TypedRetag.reborrow h budget place size policy tag =
      factoredReborrow h budget place size policy tag := by
  rfl

/-- Actual child insertion, update-before-error-check and return retain graph
formation even on errors. The tag/runtime are the ORIGINAL allocation snapshot,
not the already-advanced global counter. No insertion or access success is
assumed. This local suffix theorem does not establish whole-driver coverage. -/
theorem preserves {K U : Type} [DecidableEq K]
    (state : MachineHooks.State K U) (location : RetagPipeline.ResolvedLocation)
    (inside : DedupRangeMap Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (original : BorrowTree) (formed : Formed original) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original global)
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (provenance : location.parentProvenance = .concrete parentTag)
    (tagged : original.indexOfTag parentTag = some parent)
    (present : original.nodeAt parent = some node)
    (room : original.nodes.size+1 ≤ 4294967295)
    (before : AllTrees (Snapshot location.allocId original) state.machine.memory) :
    Holds (fun _ tree => Formed tree)
      (childSuffix location inside policy global.nextPointerTag state) := by
  have initial : AllTrees (fun _ tree => Formed tree) state.machine.memory := fun row member => (before row member).1
  unfold childSuffix
  unfold_typed ".TypedRetag.getTree"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
  cases found : state.machine.memory.live.find? (fun row => row.1 == location.allocId) with
  | none => simpa only [found,throw,throwThe,MonadExceptOf.throw,EStateM.throw,bind,EStateM.bind,Holds] using initial
  | some row =>
    simp only [found,pure,EStateM.pure]
    have key : row.1 = location.allocId := by simpa only [beq_iff_eq] using Array.find?_some found
    have packet := before row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
    obtain ⟨nodes,mapping⟩ := packet.2 key
    have childFormed := Formed.allocatedConcrete formed global runtime nodes mapping parentTag parent node tagged present room
      location.baseOffset inside policy.outsidePermission policy.protector.isSome
    rw [←provenance] at childFormed
    let child := row.2.allocation.extra.newChild location.baseOffset location.parentProvenance global.nextPointerTag inside
      policy.outsidePermission policy.protector.isSome
    have maintained := update_preserves state (fun _ tree => Formed tree) location.allocId child.tree initial childFormed
    cases updated : typed_update_tree location.allocId child.tree state with
    | error error changed => simpa only [child,updated,Holds] using maintained
    | ok value changed =>
      have after : AllTrees (fun _ tree => Formed tree) changed.machine.memory := by simpa only [updated,Holds] using maintained
      simp only [child,updated,bind,EStateM.bind]
      unfold_typed ".TypedRetag.checked"
      cases child.outcome <;> exact after
end DuplicatePrefix.GeneralBorrowCanonicalChildCausalFrame
