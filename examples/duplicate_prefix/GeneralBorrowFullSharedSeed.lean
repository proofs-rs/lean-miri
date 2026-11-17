import duplicate_prefix.GeneralBorrowFullSharedStep
import duplicate_prefix.GeneralBorrowSharedGeneratorSeed
namespace DuplicatePrefix.GeneralBorrowFullSharedSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowSharedGeneratorProfile DuplicatePrefix.GeneralBorrowFullSharedRead
open DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def root : UniIndex := ⟨0⟩
def node (tag : BorTag) : TreeNode := ⟨tag,none,#[],.Disabled,.None,false,none⟩
def location : LocationTree := ⟨⟨#[some GeneralBorrowWildcardLeaf.unique]⟩,{}⟩
def tree (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : BorrowTree := BorrowTree.new tag (Size.ofBytes capacity)

/-- The actual allocation constructor, not an assumed initial graph. It already
stores Unique/accessed at the root; there is no lazy permission warm-up premise. -/
theorem tree_eq (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : tree capacity nonzero tag =
    ⟨⟨#[(tag,root)],#[]⟩,⟨#[some (node tag)]⟩,homogeneous capacity location,#[root]⟩ := by
  simp only [tree, BorrowTree.new, DedupRangeMap.new, Size.ofBytes, beq_iff_eq, nonzero, ↓reduceIte]
  with_unfolding_all rfl

private theorem node_cases (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) (query : UniIndex) (value : TreeNode)
    (present : (tree capacity nonzero tag).nodeAt query = some value) : query = root ∧ value = node tag := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid (tree capacity nonzero tag).nodes query value present
  rw [tree_eq] at valid
  change query.toNat < 1 at valid
  have same : query = root := GeneralBorrowNodeUpdate.index_injective query root (by change query.toNat=0;omega)
  subst query
  rw [tree_eq] at present
  change some (node tag) = some value at present
  exact ⟨rfl,(Option.some.inj present).symm⟩

def depth (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : ParentDepth (tree capacity nonzero tag).nodes where
  depth := fun _ => 0
  bounded := by intro query value present;omega
  parent := by
    intro query value present before edge
    obtain ⟨_,rfl⟩ := node_cases capacity nonzero tag query value present
    cases edge

theorem children (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : GeneralBorrowGraph.ChildNodes (tree capacity nonzero tag) := by
  intro query value present child member
  obtain ⟨_,rfl⟩ := node_cases capacity nonzero tag query value present
  cases member

theorem covered (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : GeneralBorrowGraph.RootsCover (tree capacity nonzero tag) := by
  intro query value present parentless
  obtain ⟨rfl,_⟩ := node_cases capacity nonzero tag query value present
  rw [tree_eq]
  simp

def normal : NormalTreeState := {
  topology := ⟨#[⟨none,[]⟩]⟩
  defaultStates := #[⟨.Disabled,false,.None⟩]
  locationStates := #[some GeneralBorrowWildcardLeaf.unique]
  protectedNodes := []
}

theorem projection (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : source_normal_projection (tree capacity nonzero tag) location {} = normal := by
  rw [tree_eq]
  unfold_general_projection
  unfold_general_topology
  with_unfolding_all rfl

def normalForest : GeneralBorrowForest.Forest normal.topology where
  rank := fun _ => 0
  parents := by
    intro index valid parent edge
    have zero : index = 0 := by change index < 1 at valid;omega
    subst index
    cases edge
  childrenDistinct := by
    intro index valid
    have zero : index = 0 := by change index < 1 at valid;omega
    subst index
    exact List.nodup_nil
  childParent := by
    intro index valid child member
    have zero : index = 0 := by change index < 1 at valid;omega
    subst index
    cases member
  parentChild := by
    intro index valid parent edge
    have zero : index = 0 := by change index < 1 at valid;omega
    subst index
    cases edge

def forest (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : GeneralBorrowForest.Forest (source_normal_projection (tree capacity nonzero tag) location {}).topology := by
  rw [projection]
  exact normalForest

theorem profile (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) : Profile (tree capacity nonzero tag) location root := by
  refine ⟨rfl,?_,?_⟩
  · intro query value present different
    exact False.elim (different (node_cases capacity nonzero tag query value present).1)
  · intro query vacant
    by_cases same : query = root
    · subst query
      rw [tree_eq] at vacant
      change some (node tag) = none at vacant
      cases vacant
    · have other : query.toNat ≠ 0 := fun equal => same (GeneralBorrowNodeUpdate.index_injective query root equal)
      simp [location,UniValMap.get,other]

set_option autoImplicit false in
/-- All generator graph/profile/allocator premises are constructed from actual
BorrowTree.new. Only the fresh child's tag being distinct from the root is input. -/
def input (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag) (different : rootTag ≠ childTag) : Input where
  tree := tree capacity nonzero rootTag
  depth := depth capacity nonzero rootTag
  children := children capacity nonzero rootTag
  covered := covered capacity nonzero rootTag
  parentTag := rootTag
  newTag := childTag
  parent := root
  parentNode := node rootTag
  parentTagPresent := by simp [tree_eq,UniKeyMap.get]
  parentPresent := by rw [tree_eq];rfl
  fresh := by
    intro row member
    rw [tree_eq] at member
    have same := Array.mem_singleton.mp member
    subst row
    exact different
  noFree := by rw [tree_eq];rfl
  aligned := by rw [tree_eq];rfl
  fits := by rw [tree_eq];change (1 : Nat) ≤ 4294967295;omega
  isProtected := false
  offset := 0
  len := capacity
  nonzero := nonzero
  well := by rw [tree_eq];simp [homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr nonzero]
  bounds := by rw [tree_eq];change (0 : Nat)+capacity.toNat ≤ capacity.toNat;omega

theorem state (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag) (different : rootTag ≠ childTag) :
    State (input capacity nonzero rootTag childTag different) location := by
  exact ⟨rfl,by change (tree capacity nonzero rootTag).locations = homogeneous capacity location;rw [tree_eq],rfl,rfl,⟨forest capacity nonzero rootTag⟩,profile capacity nonzero rootTag⟩

theorem cache_empty : location.exposedCache = {} := rfl


end DuplicatePrefix.GeneralBorrowFullSharedSeed
