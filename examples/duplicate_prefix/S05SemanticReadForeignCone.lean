import duplicate_prefix.S05ReadPostorderGraph

namespace DuplicatePrefix.S05SemanticReadForeignCone
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem numeric (total ancestor descendant : Nat) (virtual ancestorClamp descendantClamp : Bool)
    (bounded : ancestor ≤ total) (cone : descendant ≤ ancestor)
    (clamp : ancestorClamp = true → descendantClamp = true)
    (foreign : classify total ancestor virtual ancestorClamp = some .ForeignAccess) :
    classify total descendant virtual descendantClamp = some .ForeignAccess := by
  cases virtual <;> cases ancestorClamp <;> cases descendantClamp <;>
    by_cases zero : total = 0 <;> by_cases same : total = ancestor <;>
    by_cases nextSame : total+1 = ancestor <;> by_cases descendantSame : total = descendant <;>
    by_cases descendantNext : total+1 = descendant <;> by_cases ancestorZero : ancestor = 0 <;>
    by_cases descendantZero : descendant = 0 <;> simp_all [classify] <;> omega

private theorem covers_of_path (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (root query : UniIndex) (path : Path tree root query) : Covers tree.nodes root query := by
  intro row member ancestor
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  have tail := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query row.1 row.2 present _ ancestor
  exact (S05ReadPostorderGraph.trans path tail).walk depth

/-- Exact Read classification is downward closed on physical descendant
cones, including zero counters and unexposed latent nodes. No access result
or residual Authorization is a premise. -/
theorem downward (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root query descendant : UniIndex) (node descendantNode : TreeNode)
    (maximum : Option BorTag) (position : Nat)
    (present : tree.nodes.get query = some node) (found : tree.nodes.get descendant = some descendantNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (tagOrder : ParentTagOrder tree)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (rootCone : Covers tree.nodes root query) (path : Path tree query descendant)
    (foreign : relation location root query node maximum .Read position = some .ForeignAccess) :
    relation location root descendant descendantNode maximum .Read position = some .ForeignAccess := by
  have bounded := dominates location.exposedCache tree.nodes (effective location protections) coherent short root query rootCone .Read
  have cone := dominates location.exposedCache tree.nodes (effective location protections) coherent short query descendant
    (covers_of_path tree depth query descendant path) .Read
  have tags := path_tag_le tree tagOrder query descendant path node descendantNode present found
  have clamp : aboveMaximum node maximum = true → aboveMaximum descendantNode maximum = true := by
    cases maximum with
    | none => simp [aboveMaximum]
    | some maximum =>
      intro above
      simp only [aboveMaximum,decide_eq_true_eq] at above ⊢
      exact Nat.lt_of_lt_of_le above tags
  exact numeric _ _ _ _ _ _ bounded cone clamp foreign

end DuplicatePrefix.S05SemanticReadForeignCone
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S05SemanticReadForeignCone.downward) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
