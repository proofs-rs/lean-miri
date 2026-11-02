import duplicate_prefix.OrdinaryBorrowAuthorityBridge

namespace DuplicatePrefix.OrdinaryExposedEligibility
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open OrdinaryBorrowAuthority GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false

/-- Pointwise raw mutable authority supplies the production scalar exposure
filter for either access kind. This says nothing about visiting the node. -/
theorem local_allows (state : LocationState) (held : Bool)
    (authority : LocalWrite state held) (kind : AccessKind) :
    (state.permission.strongestAllowedLocalAccess held).allows kind = true := by
  have scalar := OrdinaryBorrowAuthorityBridge.local_scalar state held authority kind
  cases kind with
  | Read => exact GeneralBorrowExposedConditionalReadPermissions.local_allows state held scalar
  | Write => exact GeneralBorrowExposedConditionalWritePermissions.local_allows state held scalar

/-- An available exposed physical grant passes the exact explicit-node filter
used in TreeState.lean:466–469, provided its tag satisfies the explicit cutoff.
The witness is obtained from actual tag/node lookup and path reflexivity.

No extra representation premise is required for this scalar conclusion. In
particular this proves neither that traversal reaches the witness nor that
hasValidExposed is set, and gives no cross-root or complete reference authority. -/
theorem eligible (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (tag : BorTag)
    (authority : AvailableExposedPhysicalGrant tree location protections tag)
    (maximum : Option BorTag)
    (cutoff : ∀ bound, maximum = some bound → tag.value ≤ bound.value)
    (kind : AccessKind) :
    ∃ index node, tree.tagMapping.get tag = some index ∧
      tree.nodes.get index = some node ∧ node.tag = tag ∧
      (node.isExposed &&
        (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
          (protections.contains node.tag)).allows kind &&
        (maximum.isNone || maximum.any (fun bound => bound.value ≥ node.tag.value))) = true := by
  obtain ⟨component,index,node,mapped,present,tagged,exposed⟩ := authority
  obtain ⟨anchor,anchorNode,anchorMapped,anchorPresent,anchorTagged,ancestors,_⟩ := component
  have same : anchor = index := Option.some.inj (anchorMapped.symm.trans mapped)
  subst anchor
  have raw := ancestors index node present (.refl index node present)
  have permits := local_allows _ _ raw kind
  have cutoffTest : (maximum.isNone || maximum.any (fun bound => bound.value ≥ node.tag.value)) = true := by
    cases maximum with
    | none => rfl
    | some bound =>
      have within := cutoff bound rfl
      simpa only [Option.isNone_some,Option.any_some,Bool.false_or,tagged,decide_eq_true_eq] using within
  exact ⟨index,node,mapped,present,tagged,by simp only [exposed,permits,cutoffTest,Bool.and_self]⟩

end DuplicatePrefix.OrdinaryExposedEligibility

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.OrdinaryExposedEligibility." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved exposed eligibility dependency {dependency}"
