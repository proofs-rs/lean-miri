import duplicate_prefix.S05ContributorPostorderFrontier
import duplicate_prefix.GeneralBorrowWildcardParentTagOrder
import duplicate_prefix.S05CutoffOwnershipGeometry
import duplicate_prefix.DuplicatePrefixResidualWriteWitnessPlan

namespace DuplicatePrefix.S05ContributorForeignCone
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem numeric_foreign_cone (total ancestor descendant : Nat)
    (virtual ancestorClamp descendantClamp : Bool)
    (bounded : ancestor ≤ total) (cone : descendant ≤ ancestor) (positive : 0 < descendant)
    (clamp : ancestorClamp = true → descendantClamp = true)
    (foreign : classify total ancestor virtual ancestorClamp = some .ForeignAccess) :
    classify total descendant virtual descendantClamp = some .ForeignAccess := by
  cases virtual <;> cases ancestorClamp <;> cases descendantClamp <;>
    by_cases zero : total = 0 <;> by_cases same : total = ancestor <;>
    by_cases nextSame : total+1 = ancestor <;> by_cases descendantSame : total = descendant <;>
    by_cases descendantNext : total+1 = descendant <;> by_cases ancestorZero : ancestor = 0 <;>
    by_cases descendantZero : descendant = 0 <;>
    simp_all [classify] <;> omega

/-- In the same actual coherent cache snapshot, a foreign ancestor forces any
positive descendant cone to be foreign too. Tag order propagates the cutoff;
count-cone bounds rule out both Local and Either descendants. This is the
classifier certificate needed by the retained-contributor DFS induction. -/
theorem foreign_cone (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root ancestor descendant : UniIndex) (ancestorNode descendantNode : TreeNode)
    (maximum : Option BorTag) (position : Nat)
    (ancestorPresent : tree.nodes.get ancestor = some ancestorNode)
    (descendantPresent : tree.nodes.get descendant = some descendantNode)
    (path : Path tree ancestor descendant) (tagOrder : ParentTagOrder tree)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (rootCone : Covers tree.nodes root ancestor) (descendantCone : Covers tree.nodes ancestor descendant)
    (positive : 0 < GeneralBorrowWildcardRelatednessBounds.count location.exposedCache descendant .Write)
    (foreign : relation location root ancestor ancestorNode maximum .Write position = some .ForeignAccess) :
    relation location root descendant descendantNode maximum .Write position = some .ForeignAccess := by
  have bounded := dominates location.exposedCache tree.nodes (effective location protections) coherent short root ancestor rootCone .Write
  have cone := dominates location.exposedCache tree.nodes (effective location protections) coherent short ancestor descendant descendantCone .Write
  have tags := path_tag_le tree tagOrder ancestor descendant path ancestorNode descendantNode ancestorPresent descendantPresent
  have clamp : aboveMaximum ancestorNode maximum = true → aboveMaximum descendantNode maximum = true := by
    cases maximum with
    | none => simp [aboveMaximum]
    | some maximum =>
      intro above
      simp only [aboveMaximum,decide_eq_true_eq] at above ⊢
      exact Nat.lt_of_lt_of_le above tags
  exact numeric_foreign_cone _ _ _ _ _ _ bounded cone positive clamp foreign

private theorem numeric_clamp (rootCount localCount : Nat) (virtual clamp : Bool)
    (positive : 0 < localCount)
    (foreign : classify rootCount localCount virtual clamp = some .ForeignAccess) : clamp = true := by
  cases virtual <;> cases clamp <;> by_cases zero : rootCount = 0 <;>
    by_cases same : rootCount = localCount <;> by_cases next : rootCount+1 = localCount <;>
    simp_all [classify]

/-- A positive cone currently classified foreign must be cutoff-clamped.
This conclusion is about the classifier, without any traversal success. -/
theorem cutoff_of_positive_foreign (location : LocationTree) (root index : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (positive : 0 < GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write)
    (foreign : relation location root index node maximum .Write position = some .ForeignAccess) :
    aboveMaximum node maximum = true := numeric_clamp _ _ _ _ positive foreign

/-- A retained positive cone under a currently foreign ancestor was foreign
in every coherent earlier DFS support-model snapshot. The cutoff witness
excludes an absent clamped relation; monotone parent tags propagate the clamp.
This is the historical classifier certificate needed at a descendant's actual
postvisit, even though counters have changed since then. -/
theorem past_foreign_certificate (tree : BorrowTree) (initial current past : LocationTree)
    (protections : ProtectedTags) (root ancestor descendant : UniIndex)
    (ancestorNode descendantNode : TreeNode) (maximum : Option BorTag) (position : Nat)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (tagOrder : ParentTagOrder tree)
    (witness : S05CutoffOwnershipGeometry.CutoffWitness tree initial protections root position maximum rights.area.contains)
    (inside : rights.area.contains descendant)
    (ancestorPresent : tree.nodes.get ancestor = some ancestorNode)
    (descendantPresent : tree.nodes.get descendant = some descendantNode)
    (path : Path tree ancestor descendant)
    (positive : 0 < GeneralBorrowWildcardRelatednessBounds.count current.exposedCache ancestor .Write)
    (foreign : relation current root ancestor ancestorNode maximum .Write position = some .ForeignAccess)
    (model : DuplicatePrefixResidualWriteWitnessPlan.Model tree initial past protections maximum)
    (coherent : LocationCoherent tree past protections) (short : tree.nodes.size < 65536) :
    relation past root descendant descendantNode maximum .Write position = some .ForeignAccess := by
  have ancestorAbove := cutoff_of_positive_foreign current root ancestor ancestorNode maximum position positive foreign
  have tags := path_tag_le tree tagOrder ancestor descendant path ancestorNode descendantNode ancestorPresent descendantPresent
  have descendantAbove : aboveMaximum descendantNode maximum = true := by
    cases maximum with
    | none => simp [aboveMaximum] at ancestorAbove
    | some maximum =>
      simp only [aboveMaximum,decide_eq_true_eq] at ancestorAbove ⊢
      exact Nat.lt_of_lt_of_le ancestorAbove tags
  obtain ⟨removed,legal,matching⟩ := model
  rw [DuplicatePrefixResidualCountModel.relation_matches tree initial past protections .Write removed matching coherent short]
  exact S05CutoffOwnershipGeometry.clamped_foreign tree initial protections root position maximum rights depth tagOrder witness
    descendant descendantNode inside descendantPresent descendantAbove .Write removed legal

end DuplicatePrefix.S05ContributorForeignCone
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05ContributorForeignCone.foreign_cone,
      ``DuplicatePrefix.S05ContributorForeignCone.cutoff_of_positive_foreign,
      ``DuplicatePrefix.S05ContributorForeignCone.past_foreign_certificate] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
