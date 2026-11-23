import Miri.Verification.ExactWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeBorrowsWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.Verification.TreeBorrowsWP Std.WP

set_option experimental.vcgen true
set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def aliasTag : BorTag := ⟨2, by decide⟩
private def bytes := Size.ofBytes 1
private def entry := BorrowTree.new BorTag.one bytes
private def permissions := DedupRangeMap.new bytes (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
private def protectors := ({} : ProtectedTags).insert aliasTag .StrongProtector
private def inserted := entry.newChild Size.ZERO (.concrete BorTag.one) aliasTag permissions .Frozen true
private def writeWith (tags : ProtectedTags) :=
  access (.concrete BorTag.one) Size.ZERO bytes .Write tags .VisitChildrenOfAccessed
private def protectedWrite := inserted.tree.performBorrowAccessRange (.concrete BorTag.one)
  Size.ZERO bytes .Write protectors .VisitChildrenOfAccessed

private def protectedError : BorrowTree.BorrowTreeAccessStatus :=
  .AccessFailure ⟨0, 1⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen))

private def visitedPermission (locations : Array BorrowTree.BorrowTreeLocationResult) : Option Permission :=
  (((locations[0]?.bind (·.normalAccess)).bind (·.tree.stateAt 1)).map (·.permission))

/-- The ranged access rule passes the failing trace and exact successor to an
arbitrary client postcondition. -/
theorem protectedAliasWrite (post : BorrowTree → Prop) (after : post protectedWrite.tree) :
    Triple (writeWith protectors) (· = inserted.tree) (fun _ _ => False)
      (fun (status, locations) tree =>
        status = protectedError ∧ visitedPermission locations = some .Disabled ∧ post tree) := by
  vcgen [writeWith]
  subst_vars
  rw [accessPre_iff]
  change (match protectedWrite.status with
    | .Completed => False
    | status => status = protectedError ∧
        visitedPermission protectedWrite.locations = some .Disabled ∧ post protectedWrite.tree)
  rw [show protectedWrite.status = protectedError from by cbv]
  exact ⟨rfl, by cbv, after⟩

/-- A protected shared child rejects a foreign write at the permission step. -/
example (post : Tree.LocationState.AccessResult → Prop)
    (retained : post (.Error ⟨.Disabled, true, .Read⟩ (.ProtectedDisabled .Frozen))) :
    (match (⟨.Frozen, true, .Read⟩ : Tree.LocationState).performAccess .Write .ForeignAccess true with
      | .Success .. => False
      | result => post result) :=
  (location_iff ⟨.Frozen, true, .Read⟩ .Write .ForeignAccess true (fun _ _ => False) post).mpr
    retained

/-- `vcgen` selects the ordered protector release rule for arbitrary trees. -/
example (tag : BorTag) (tags : ProtectedTags) (post : Unit → BorrowTree → Prop)
    (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) :
    Triple (release tag tags)
      (Miri.Verification.ProtectorReleaseWP.releasePre tag tags (post ()) failure) post failure := by
  vcgen <;> assumption

/-- Retag insertion generates its precondition with both continuations. -/
example (offset : Size) (parent : ProvenanceExtra) (tag : BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (post : Unit → BorrowTree → Prop) (failure : BorrowTree.ChildInsertError → BorrowTree → Prop) :
    Triple (insertChild offset parent tag inside outside held)
      (fun tree => BorrowTree.MutationVerification.insertChildPre tree offset parent tag inside outside held
        (post ()) failure) post failure := by
  vcgen <;> assumption

/-- Duplicate retag insertion reports the mapping left by the failed insert. -/
example (offset : Size) (parent : ProvenanceExtra) (tag : BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex)
    (failed : tree.tagMapping.insert tag = .DuplicateKeyAfterReplacement mapping index) :
    Triple (insertChild offset parent tag inside outside held) (· = tree) (fun _ _ => False)
      (fun error after => error = .DuplicateTag tag ∧ after = { tree with tagMapping := mapping }) := by
  vcgen
  subst_vars
  simp [BorrowTree.MutationVerification.insertChildPre, failed]

/-- The alias is inserted successfully. The same write completes when its
protector is absent. -/
example : inserted.outcome = .ok () := by cbv

example : (inserted.tree.performBorrowAccessRange (.concrete BorTag.one) Size.ZERO bytes .Write
    {} .VisitChildrenOfAccessed).status = .Completed := by cbv

private def exposed := entry.exposeTag {} BorTag.one
private def wildcardRead := access .wildcard Size.ZERO bytes .Read {} .VisitChildrenOfAccessed
private def wildcardReadResult :=
  exposed.tree.performBorrowAccessRange .wildcard Size.ZERO bytes .Read {} .VisitChildrenOfAccessed

/-- Exposure lets the wildcard read satisfy any postcondition of its exact
successor and trace. -/
example (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (after : post wildcardReadResult.locations wildcardReadResult.tree) :
    Triple wildcardRead (· = exposed.tree) post (fun _ _ => False) := by
  vcgen [wildcardRead]
  subst_vars
  rw [accessPre_iff]
  change (match wildcardReadResult.status with
    | .Completed => post wildcardReadResult.locations wildcardReadResult.tree
    | _ => False)
  rw [show wildcardReadResult.status = .Completed from by cbv]
  exact after

/-- An actual typed reborrow generates its staged continuation with arbitrary
compiler hooks, permissions and machine postconditions. -/
example {K U : Type} [DecidableEq K] (hooks : Miri.Interpreter.TypedRetag.Hooks K U)
    (budget : Nat) (place : Miri.Interpreter.MPlaceTy Provenance) (size : Size)
    (policy : RetagPolicy.NewPermission) (tag : BorTag)
    (post : Option Provenance → Miri.Interpreter.MachineHooks.State K U → Prop)
    (failure : Miri.Interpreter.StepError → Miri.Interpreter.MachineHooks.State K U → Prop) :
    Triple (Miri.Interpreter.TypedRetag.reborrow hooks budget place size policy tag)
      (Miri.Verification.TypedRetagWP.reborrowPre hooks budget place size policy tag post failure)
      post failure := by
  vcgen

end MiriTests.Verification.TreeBorrowsWP
