import duplicate_prefix.GeneralBorrowWildcardControlStack
import duplicate_prefix.DuplicatePrefixResidualSupportSnapshotBridge
import duplicate_prefix.GeneralBorrowResidualPrimaryWitness
import duplicate_prefix.DuplicatePrefixBorrowAuthorization

namespace DuplicatePrefix.S05NoCutoffOwnershipBridge
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A sufficient call-time ownership packet expressed only in graph,
permission, protection and activity data. It contains no callback classification,
removal-mask quantifier, operation outcome, Row, Contract or NoUB certificate.
It is not asserted to characterize all ordinarily valid mutable references.

Local rights are required at an ancestor only when an actual exposed descendant
supports that access kind. Foreign rights use the interpreter's exact initial
permission/protector/accessed table. A physical primary root additionally needs
an actual exposed Write supporter; virtual roots need no such witness. -/
structure Ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) where
  area : GeneralBorrowWildcardControlStack.Support tree root
  covers : ∀ query,area.contains query → Covers tree.nodes root query
  foreign : ∀ query node,area.contains query → tree.nodes.get query = some node → ∀ kind,
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) kind .ForeignAccess (protections.contains node.tag)
  localRights : ∀ query node,area.contains query → tree.nodes.get query = some node →
    ∀ witness witnessNode,tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → ∀ kind,
      supports (effective location protections witness witnessNode) kind = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess (protections.contains node.tag)
  primary : position = 0 → ∃ witness node,area.contains witness ∧ tree.nodes.get witness = some node ∧
    node.isExposed = true ∧ (effective location protections witness node).allows .Write = true

private theorem write_allows (level : WildcardAccessLevel) (kind : AccessKind)
    (write : level.allows .Write = true) : level.allows kind = true := by
  cases level <;> cases kind <;> simp_all [WildcardAccessLevel.allows]

private theorem classified_some (rootCount localCount : Nat) (virtual : Bool)
    (positive : 0 < rootCount + if virtual then 1 else 0) :
    classify rootCount localCount virtual false ≠ none := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify]

private theorem classified_local_positive (rootCount localCount : Nat) (virtual : Bool)
    (classified : classify rootCount localCount virtual false = some .LocalAccess) : 0 < localCount := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

/-- Positive descendant support extracts one real initial exposed contributor,
so the ownership packet supplies Local rights without assuming a classification
or the success of any future visitor. -/
theorem local_of_count (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (rights : Ownership tree location protections root position)
    (query : UniIndex) (node : TreeNode) (inside : rights.area.contains query)
    (present : tree.nodes.get query = some node) (kind : AccessKind)
    (positive : 0 < cardinality tree.nodes (effective location protections) query kind) :
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess (protections.contains node.tag) := by
  have member : ∃ row,row ∈ tree.nodes.entries.toList.filter
      (contributes tree.nodes (effective location protections) query kind) := by
    cases rows : tree.nodes.entries.toList.filter (contributes tree.nodes (effective location protections) query kind) with
    | nil => simp only [cardinality,rows,List.length_nil,Nat.lt_irrefl] at positive
    | cons row rest => exact ⟨row,by simp⟩
  obtain ⟨⟨witness,witnessNode⟩,member⟩ := member
  obtain ⟨entry,contributing⟩ := List.mem_filter.mp member
  have found := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness witnessNode).mp entry
  simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at contributing
  exact rights.localRights query node inside present witness witnessNode found contributing.1.1 contributing.2 kind contributing.1.2

/-- Independent snapshot ownership implies the existing no-cutoff callback
capability for either access kind. This is a sufficient-class bridge, not
ordinary-valid-input coverage, and it does not address concrete some-cutoff
Write residual pairs. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (rights : Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (kind : AccessKind) : Authorization tree location protections root position none kind rights.area.contains := by
  have counts (query : UniIndex) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind := by
    cases kind with
    | Read => exact nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query .Read
    | Write => exact nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query .Write
  have eligible : position = 0 → ∃ witness node,rights.area.contains witness ∧ tree.nodes.get witness = some node ∧
      Supports location protections witness node none kind := by
    intro physical
    obtain ⟨witness,node,inside,present,exposed,write⟩ := rights.primary physical
    exact ⟨witness,node,inside,present,exposed,write_allows _ kind write,by simp⟩
  have total : 0 < GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind + if position != 0 then 1 else 0 := by
    by_cases physical : position = 0
    · obtain ⟨witness,node,inside,present,supported⟩ := eligible physical
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (rights.covers witness inside)
      have positive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth none kind []
        (empty_removal tree location protections none kind) root witness node present supported path
      rw [residual_empty] at positive
      simpa only [physical,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero,counts root] using positive
    · simp only [show (position != 0) = true by simp [physical],ite_true]
      omega
  have snapshot : Snapshot tree location protections root position none kind rights.area.contains := by
    refine ⟨?_,eligible⟩
    intro query node inside present
    have possible : ((location.perms.get query).getD node.defaultLocationState).possible = true :=
      (rights.foreign query node inside present .Write).1
    have nonabsent : relation location root query node none kind position ≠ none := by
      exact classified_some _ _ _ total
    cases classified : relation location root query node none kind position with
    | none => exact False.elim (nonabsent classified)
    | some related =>
      cases related with
      | EitherAccess => exact possible
      | ForeignAccess => exact ⟨possible,Or.inr (rights.foreign query node inside present kind)⟩
      | LocalAccess =>
        have positive := classified_local_positive _ _ _ classified
        have cardPositive : 0 < cardinality tree.nodes (effective location protections) query kind := by
          rw [←counts query]
          exact positive
        exact ⟨possible,Or.inr (local_of_count tree location protections root position rights query node inside present kind cardPositive)⟩
  exact DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree location protections root position none kind rights.area.contains
    snapshot rights.area.rooted rights.area.present rights.area.children rights.covers coherent short
    (fun removed legal => no_maximum_removal_empty tree location protections kind removed legal)

/-- Independent per-root snapshot ownership, without a borrowed Row or future
visitor result. Permission-free traversal supports may differ by physical root. -/
def ForestOwnership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  ∀ position,(valid : position < tree.roots.size) →
    Nonempty (Ownership tree location protections tree.roots[position] position)

/-- The independent graph/permission/activity packet forms the existing
wildcard borrow Row. The finite-cache runtime bound is separate from ownership. -/
theorem wildcard_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (rights : ForestOwnership tree location protections)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections none none none) := by
  refine ⟨{wildcard := fun _ => rfl,rootPath := ?_,rootPresent := ?_,cutoff := rfl,normal := ?_,callbacks := ?_}⟩
  · intro anchor impossible;cases impossible
  · intro root impossible;cases impossible
  · intro anchor impossible;cases impossible
  · intro position valid _
    obtain ⟨owned⟩ := rights position valid
    exact ⟨owned.area.contains,authorization tree location protections _ position owned depth coherent short .Read,
      authorization tree location protections _ position owned depth coherent short .Write⟩

/-- Positive wildcard borrow capability follows from independent per-byte
snapshot ownership and ordinary physical window/root facts. This bridge does
not assume Positive, Row, call success or NoUB as an input. Its ownership
hypothesis still needs an ordinary-valid-reference justification. -/
theorem wildcard_positive (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64) (nonempty : 0 < len.toNat)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (rootExists : 0 < tree.roots.size) (short : tree.nodes.size < 65536)
    (rights : GeneralRangeMapOrigins.OwnedOn (fun location => ForestOwnership tree location global.protectedTags)
      offset (offset+len) tree.locations) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len) := by
  obtain ⟨depth⟩ := runtime.formed.toGraphState.depth
  refine ⟨{positive := nonempty,bounds := bounds,sourcePresent := ?_,wildcardRoot := fun _ => rootExists,rows := ?_}⟩
  · intro anchor impossible;cases impossible
  · intro position valid positive start stop
    exact wildcard_row tree _ global.protectedTags (rights position valid positive start stop) depth
      (runtime.coherent position valid) short

end DuplicatePrefix.S05NoCutoffOwnershipBridge
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05NoCutoffOwnershipBridge.local_of_count,
      ``DuplicatePrefix.S05NoCutoffOwnershipBridge.authorization,
      ``DuplicatePrefix.S05NoCutoffOwnershipBridge.wildcard_row,
      ``DuplicatePrefix.S05NoCutoffOwnershipBridge.wildcard_positive] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
