import duplicate_prefix.DuplicatePrefixResidualWriteDFSInvariant
import duplicate_prefix.GeneralBorrowWildcardControlWitness
namespace DuplicatePrefix.DuplicatePrefixResidualWriteWitnessPlan
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowWildcardSubtreeStack GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardControlWitness DuplicatePrefixCallbackAuthorization
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open DuplicatePrefixResidualWriteDFSInvariant (seen)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

abbrev Model (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags) (maximum : Option BorTag) : Prop :=
  ∃ removed, Removal tree initial protections maximum .Write removed ∧ Matches tree initial current protections .Write removed

structure Plan (tree : BorrowTree) (initialLocation : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) where
  pending : Bool → Array GeneralBorrowWildcardSubtreeStack.Task → Prop
  initial : pending false #[(root,false)]
  finish : ∀ witness, pending witness #[] → (rootPosition != 0) = true ∨ witness = true
  pop : ∀ (current : LocationTree) (witness : Bool) (stack : Array GeneralBorrowWildcardSubtreeStack.Task) (index : UniIndex) (node : TreeNode),
    tree.nodes.get index = some node → Model tree initialLocation current protections maximum →
    GeneralBorrowExposureCardinality.LocationCoherent tree current protections → pending witness (stack.push (index,false)) →
    DuplicatePrefixCallbackVisitAuthorization.entrySkip (GeneralBorrowWildcardVirtualLeaf.effective current index node) .Write
      (relation current root index node maximum .Write rootPosition) = true → pending witness stack
  expand : ∀ witness stack index node, tree.nodes.get index = some node → pending witness (stack.push (index,false)) → pending witness (expanded stack index node.children)
  post : ∀ current witness stack index node, tree.nodes.get index = some node → Model tree initialLocation current protections maximum →
    pending witness (stack.push (index,true)) → pending (seen current index node maximum protections witness) stack

private theorem supports_allows (level : WildcardAccessLevel) : GeneralBorrowExposureCardinality.supports level .Write = level.allows .Write := by
  cases level <;> rfl

private theorem supporter_current (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (model : Model tree initial current protections none) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (supported : Supports initial protections index node none .Write) :
    Supports current protections index node none .Write := by
  obtain ⟨removed,legal,matching⟩ := model
  have empty := no_maximum_removal_empty tree initial protections .Write removed legal
  subst removed
  refine ⟨supported.1,?_,supported.2.2⟩
  have retained := matching index node present supported.1
  have equal : (GeneralBorrowExposureCardinality.effective current protections index node).allows .Write =
      (GeneralBorrowExposureCardinality.effective initial protections index node).allows .Write := by
    simpa only [levels,List.contains_nil,Bool.false_eq_true,ite_false,supports_allows] using retained
  exact equal.trans supported.2.1

private theorem count_positive (tree : BorrowTree) (current : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections) (short : tree.nodes.size < 65536)
    (query witness : UniIndex) (node : TreeNode) (present : tree.nodes.get witness = some node)
    (supported : Supports current protections witness node none .Write)
    (walk : query ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) witness) :
    0 < GeneralBorrowWildcardRelatednessBounds.count current.exposedCache query .Write := by
  rw [show GeneralBorrowWildcardRelatednessBounds.count current.exposedCache query .Write =
      GeneralBorrowExposureCardinality.cardinality tree.nodes (GeneralBorrowExposureCardinality.effective current protections) query .Write from
    GeneralBorrowExposureCardinality.nat_exact _ _ _ coherent short query .Write]
  have member : (witness,node) ∈ tree.nodes.entries.toList.filter
      (GeneralBorrowExposureCardinality.contributes tree.nodes (GeneralBorrowExposureCardinality.effective current protections) query .Write) := by
    refine List.mem_filter.mpr ⟨(GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness node).mpr present,?_⟩
    simp only [GeneralBorrowExposureCardinality.contributes,Bool.and_eq_true,List.contains_iff_mem]
    exact ⟨⟨supported.1,by rw [supports_allows];exact supported.2.1⟩,walk⟩
  exact List.length_pos_iff.mpr (by intro empty;rw [empty] at member;cases member)

/-- The no-maximum primary Write plan follows one genuine retained supporter. -/
def primary (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root witness : UniIndex) (node : TreeNode)
    (present : tree.nodes.get witness = some node) (supported : Supports initial protections witness node none .Write)
    (rootPath : Path tree root witness) (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (short : tree.nodes.size < 65536) : Plan tree initial protections root 0 none where
  pending := Pending tree witness
  initial := GeneralBorrowWildcardControlWitness.initial rootPath
  finish := by intro seen pending;exact .inr (GeneralBorrowWildcardControlWitness.empty pending)
  pop := by
    intro current seen stack index indexNode found model coherent pending skipped
    apply GeneralBorrowWildcardControlWitness.pop stack index false pending
    intro path
    have retained := supporter_current tree initial current protections model witness node present supported
    have rootPositive := count_positive tree current protections coherent short root witness node present retained (rootPath.walk depth)
    have localPositive := count_positive tree current protections coherent short index witness node present retained (path.walk depth)
    have foreign := DuplicatePrefixResidualWriteSkip.entry_skip_foreign _ _ skipped
    have rootNonzero : GeneralBorrowWildcardRelatednessBounds.count current.exposedCache root .Write ≠ 0 := by omega
    have localNonzero : GeneralBorrowWildcardRelatednessBounds.count current.exposedCache index .Write ≠ 0 := by omega
    by_cases equal : GeneralBorrowWildcardRelatednessBounds.count current.exposedCache root .Write = GeneralBorrowWildcardRelatednessBounds.count current.exposedCache index .Write
    · simp [relation,aboveMaximum,classify,rootNonzero,localNonzero,equal] at foreign
    · simp [relation,aboveMaximum,classify,rootNonzero,localNonzero,equal] at foreign
  expand := by intros;exact GeneralBorrowWildcardControlWitness.expand graph _ _ _ _ (by assumption) (by assumption)
  post := by
    intro current seen stack index indexNode found model pending
    apply GeneralBorrowWildcardControlWitness.post seen (DuplicatePrefixResidualWriteDFSInvariant.seen current index indexNode none protections seen) stack index pending
    · intro already;simp [DuplicatePrefixResidualWriteDFSInvariant.seen,already]
    · intro same
      subst index
      have sameNode := Option.some.inj (present.symm.trans found)
      subst indexNode
      have retained := supporter_current tree initial current protections model witness node present supported
      simp [DuplicatePrefixResidualWriteDFSInvariant.seen,GeneralBorrowWildcardVirtualLeaf.effective,retained.1,retained.2.1]

def virtual (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (nonzero : position ≠ 0) : Plan tree initial protections root position maximum where
  pending := fun _ _ => True
  initial := trivial
  finish := by intros;exact .inl (by simp [nonzero])
  pop := by intros;trivial
  expand := by intros;trivial
  post := by intros;trivial
end DuplicatePrefix.DuplicatePrefixResidualWriteWitnessPlan
