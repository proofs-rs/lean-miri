import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorization
import duplicate_prefix.GeneralBorrowExposureCardinality

namespace DuplicatePrefix.DuplicatePrefixResidualSupportAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality
open DuplicatePrefixCallbackAuthorization

/-! A finite, data-only candidate for callback authorization. Counts retain all
initial exposed supporters, including newer Cell and ReservedIM supporters.
Only newer Write supporters with Unique/ReservedFrz permissions may be removed.
The permitted removal sets are intended to overapproximate child-first processing; they
are not machine states, execution traces, or successful-operation certificates.
Coverage by ordinary valid inputs, preservation of this model by actual
callbacks, and composition with normal access and the full call are UNPROVED.
In particular this module does not define complete mutable-slice validity. -/

def losesWriteWhenForeign : Permission → Bool
  | .Unique | .ReservedFrz _ => true
  | .Cell | .ReservedIM | .Frozen | .Disabled => false

/-- A candidate removable contribution. A protected conflicted reservation is
not a Write supporter, and neither Cell nor ReservedIM is removable here. -/
def removable (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (kind : AccessKind) (index : UniIndex) (node : TreeNode) : Bool :=
  match kind with
  | .Read => false
  | .Write => node.isExposed && aboveMaximum node maximum &&
      supports (effective location protections index node) .Write &&
      losesWriteWhenForeign ((location.perms.get index).getD node.defaultLocationState).permission

/-- A list represents a finite subset. Duplicate-free enumeration is explicit;
membership alone determines counts. No operational order is supplied. -/
structure Removal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex) : Prop where
  distinct : removed.Nodup
  allowed : ∀ index ∈ removed, ∃ node, tree.nodes.get index = some node ∧
    removable location protections maximum kind index node = true

def residualCount (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex) (query : UniIndex) : Nat :=
  ((tree.nodes.entries.toList.filter
    (contributes tree.nodes (effective location protections) query kind)).filter
      (fun row => !removed.contains row.1)).length

def residualRelation (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag)
    (kind : AccessKind) (rootPosition : Nat) (removed : List UniIndex) :
    Option WildcardAccessRelatedness :=
  classify (residualCount tree location protections kind removed root)
    (residualCount tree location protections kind removed index)
    (rootPosition != 0) (aboveMaximum node maximum)

set_option autoImplicit false in
/-- A conservative algebraic callback candidate, on one initial location and
one root. Pairwise subset quantification includes combinations that need not
occur in the actual visitor, so necessity/valid-input coverage is NOT claimed.
Queries use the initial scalar state and exclude the current node from both
removal sets. A source simulation must separately establish that the node has
not already been visited; exclusion alone does not establish that fact. Root
geometry, cache coherence and numeric budgets are separate contracts. -/
structure Authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop) : Prop where
  rooted : support root
  present : ∀ index, support index → ∃ node, tree.nodes.get index = some node
  children : ∀ index node, support index → tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, support child
  covers : ∀ index, support index → Covers tree.nodes root index
  possible : ∀ index node, support index → tree.nodes.get index = some node →
    ((location.perms.get index).getD node.defaultLocationState).possible = true
  queries : ∀ before after, Removal tree location protections maximum kind before →
    Removal tree location protections maximum kind after →
    (∀ index ∈ before, index ∈ after) →
    ∀ index node, support index → tree.nodes.get index = some node → index ∉ after →
      DuplicatePrefixCallbackVisitAuthorization.Authorized
        ((location.perms.get index).getD node.defaultLocationState) kind (protections.contains node.tag)
        (residualRelation tree location protections root index node maximum kind rootPosition before)
        (residualRelation tree location protections root index node maximum kind rootPosition after)
  witness : rootPosition = 0 → ∃ index node, support index ∧ tree.nodes.get index = some node ∧
    Supports location protections index node maximum kind

theorem empty_removal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (kind : AccessKind) : Removal tree location protections maximum kind [] :=
  ⟨List.nodup_nil, by intro index member; cases member⟩

theorem residual_empty (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (query : UniIndex) :
    residualCount tree location protections kind [] query =
      cardinality tree.nodes (effective location protections) query kind := by
  simp [residualCount, cardinality]

theorem nondroppable_retained (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections maximum kind removed)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (retained : removable location protections maximum kind index node = false) : index ∉ removed := by
  intro member
  obtain ⟨found,lookup,allowed⟩ := legal.allowed index member
  have same : found = node := Option.some.inj (lookup.symm.trans present)
  subst found
  rw [retained] at allowed
  cases allowed

theorem read_removal_empty (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (removed : List UniIndex)
    (legal : Removal tree location protections maximum .Read removed) : removed = [] := by
  cases removed with
  | nil => rfl
  | cons index rest =>
    obtain ⟨node,present,allowed⟩ := legal.allowed index (by simp)
    simp [removable] at allowed

theorem no_maximum_removal_empty (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections none kind removed) : removed = [] := by
  cases removed with
  | nil => rfl
  | cons index rest =>
    obtain ⟨node,present,allowed⟩ := legal.allowed index (by simp)
    cases kind <;> simp [removable, aboveMaximum] at allowed

theorem cell_retained (location : LocationTree) (protections : ProtectedTags) (maximum : Option BorTag)
    (kind : AccessKind) (index : UniIndex) (node : TreeNode)
    (permission : ((location.perms.get index).getD node.defaultLocationState).permission = .Cell) :
    removable location protections maximum kind index node = false := by
  cases kind <;> simp [removable, permission, losesWriteWhenForeign]

theorem reserved_im_retained (location : LocationTree) (protections : ProtectedTags) (maximum : Option BorTag)
    (kind : AccessKind) (index : UniIndex) (node : TreeNode)
    (permission : ((location.perms.get index).getD node.defaultLocationState).permission = .ReservedIM) :
    removable location protections maximum kind index node = false := by
  cases kind <;> simp [removable, permission, losesWriteWhenForeign]

theorem initial_relation (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (rootPosition : Nat)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536) :
    residualRelation tree location protections root index node maximum kind rootPosition [] =
      relation location root index node maximum kind rootPosition := by
  have counts (query : UniIndex) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind := by
    have exactCount := nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query kind
    cases kind <;> exact exactCount
  simp only [residualRelation, residual_empty, relation, counts]

end DuplicatePrefix.DuplicatePrefixResidualSupportAuthorization
