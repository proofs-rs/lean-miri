import duplicate_prefix.GeneralBorrowSharedGeneratorCache
namespace DuplicatePrefix.GeneralBorrowSharedGeneratorSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowSharedGeneratorProfile DuplicatePrefix.GeneralBorrowExposeReadParentRead
open DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def root : UniIndex := ⟨0⟩
def node (tag : BorTag) : TreeNode := ⟨tag,none,#[],.Disabled,.None,false,none⟩
def location : LocationTree := ⟨⟨#[some GeneralBorrowWildcardLeaf.unique]⟩,{}⟩
def tree (tag : BorTag) : BorrowTree := BorrowTree.new tag (Size.ofBytes 1)

/-- The actual allocation constructor, not an assumed initial graph. It already
stores Unique/accessed at the root; there is no lazy permission warm-up premise. -/
theorem tree_eq (tag : BorTag) : tree tag =
    ⟨⟨#[(tag,root)],#[]⟩,⟨#[some (node tag)]⟩,homogeneous 1 location,#[root]⟩ := by
  with_unfolding_all rfl

private theorem node_cases (tag : BorTag) (query : UniIndex) (value : TreeNode)
    (present : (tree tag).nodeAt query = some value) : query = root ∧ value = node tag := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid (tree tag).nodes query value present
  rw [tree_eq] at valid
  change query.toNat < 1 at valid
  have same : query = root := GeneralBorrowNodeUpdate.index_injective query root (by change query.toNat=0;omega)
  subst query
  rw [tree_eq] at present
  change some (node tag) = some value at present
  exact ⟨rfl,(Option.some.inj present).symm⟩

def depth (tag : BorTag) : ParentDepth (tree tag).nodes where
  depth := fun _ => 0
  bounded := by intro query value present;omega
  parent := by
    intro query value present before edge
    obtain ⟨_,rfl⟩ := node_cases tag query value present
    cases edge

theorem children (tag : BorTag) : GeneralBorrowGraph.ChildNodes (tree tag) := by
  intro query value present child member
  obtain ⟨_,rfl⟩ := node_cases tag query value present
  cases member

theorem covered (tag : BorTag) : GeneralBorrowGraph.RootsCover (tree tag) := by
  intro query value present parentless
  obtain ⟨rfl,_⟩ := node_cases tag query value present
  rw [tree_eq]
  simp

def normal : NormalTreeState := {
  topology := ⟨#[⟨none,[]⟩]⟩
  defaultStates := #[⟨.Disabled,false,.None⟩]
  locationStates := #[some GeneralBorrowWildcardLeaf.unique]
  protectedNodes := []
}

theorem projection (tag : BorTag) : source_normal_projection (tree tag) location {} = normal := by
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

def forest (tag : BorTag) : GeneralBorrowForest.Forest (source_normal_projection (tree tag) location {}).topology := by
  rw [projection]
  exact normalForest

theorem profile (tag : BorTag) : Profile (tree tag) location root := by
  refine ⟨rfl,?_,?_⟩
  · intro query value present different
    exact False.elim (different (node_cases tag query value present).1)
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
def input (rootTag childTag : BorTag) (different : rootTag ≠ childTag) : Input where
  tree := tree rootTag
  depth := depth rootTag
  children := children rootTag
  covered := covered rootTag
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
  len := 1
  nonzero := by decide
  well := by rw [tree_eq];simp [homogeneous,DedupRangeMap.WellFormed]
  bounds := by rw [tree_eq];change (0 : Nat)+1 ≤ 1;omega

theorem state (rootTag childTag : BorTag) (different : rootTag ≠ childTag) :
    State (input rootTag childTag different) location := by
  exact ⟨rfl,rfl,by change (tree rootTag).locations = homogeneous 1 location;rw [tree_eq],rfl,rfl,⟨forest rootTag⟩,profile rootTag⟩

theorem cache_empty : location.exposedCache = {} := rfl

/-- Actual root Read completion is derived from the constructed allocation
seed; the result tree is exactly the internally formed afterReadInput tree. -/
theorem read_construct (rootTag childTag : BorTag) (different : rootTag ≠ childTag) :
    let seed := input rootTag childTag different
    (read seed {}).status = .Completed ∧
    (read seed {}).tree = (afterReadInput seed location {} rfl rfl).tree ∧
    State (afterReadInput seed location {} rfl rfl) (readLocation seed location {}) ∧
    (readLocation seed location {}).exposedCache = {} := by
  let seed := input rootTag childTag different
  have good := state rootTag childTag different
  have actual := GeneralBorrowSharedProfileParentRead.read_closed seed location rfl rfl
    good.locations good.roots good.parentless (forest rootTag) good.profile
  refine ⟨actual.1,actual.2.1,?_,?_⟩
  · exact ⟨rfl,rfl,rfl,rfl,rfl,⟨forest rootTag⟩,actual.2.2.1⟩
  · exact (GeneralBorrowSharedGeneratorCache.read_cache seed location good).trans cache_empty
end DuplicatePrefix.GeneralBorrowSharedGeneratorSeed
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedGeneratorSeed.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved allocation seed dependency {dependency}"
