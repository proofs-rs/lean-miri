import duplicate_prefix.GeneralBorrowTwoRootPolicySeed
import duplicate_prefix.GeneralBorrowTwoRootParentRead
namespace DuplicatePrefix.GeneralBorrowTwoRootSeedShared
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposeReadFold DuplicatePrefix.RangeMapNonempty
open DuplicatePrefix.GeneralBorrowExposeReadParentRead
open DuplicatePrefix.GeneralBorrowTwoRootConstructed (first second rootNode)
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem ordered_ne (left right : BorTag) (ordered : left.value < right.value) : left ≠ right := by
  intro same
  have values := congrArg (fun tag : BorTag => tag.value.toNat) same
  have bound := UInt64.lt_iff_toNat_lt.mp ordered
  omega

/-- Derive the complete shared-constructor metadata from the actual activated
policy seed. The only premises are the three tags' strict order. -/
def input (rootTag parentTag childTag : BorTag)
    (rootOrder : rootTag.value < parentTag.value) (childOrder : parentTag.value < childTag.value) :
    GeneralBorrowFreshMetadataChildShared.Input where
  tree := GeneralBorrowTwoRootPolicySeed.activated rootTag parentTag
  depth := GeneralBorrowTwoRootPolicySeed.depth rootTag parentTag
  children := by
    simpa only [GeneralBorrowGraph.ChildNodes,BorrowTree.nodeAt,GeneralBorrowTwoRootPolicySeed.activated] using
      GeneralBorrowTwoRootPolicySeed.children rootTag parentTag
  covered := by
    simpa only [GeneralBorrowGraph.RootsCover,BorrowTree.nodeAt,GeneralBorrowTwoRootPolicySeed.activated] using
      GeneralBorrowTwoRootPolicySeed.covered rootTag parentTag
  parentTag := parentTag
  newTag := childTag
  parent := second
  parentNode := GeneralBorrowTwoRootPolicySeed.parentNode parentTag
  parentTagPresent := by
    have different := ordered_ne rootTag parentTag rootOrder
    simp [GeneralBorrowTwoRootPolicySeed.activated,GeneralBorrowTwoRootPolicySeed.tree,UniKeyMap.get,different]
  parentPresent := rfl
  fresh := by
    have parentDifferent := ordered_ne parentTag childTag childOrder
    have rootChild : rootTag.value < childTag.value := UInt64.lt_iff_toNat_lt.mpr (by
      have left := UInt64.lt_iff_toNat_lt.mp rootOrder
      have right := UInt64.lt_iff_toNat_lt.mp childOrder
      omega)
    have rootDifferent := ordered_ne rootTag childTag rootChild
    intro row member
    change row ∈ #[(rootTag,first),(parentTag,second)] at member
    simp only [Array.mem_def,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact rootDifferent
    · exact parentDifferent
  noFree := rfl
  aligned := rfl
  fits := by change (2 : Nat) ≤ 4294967295;omega
  isProtected := false
  offset := 0
  len := 1
  nonzero := by decide
  well := by simp [GeneralBorrowTwoRootPolicySeed.activated,homogeneous,DedupRangeMap.WellFormed]
  bounds := by change (0 : Nat)+1 ≤ 1;omega

/-- Initial ordered tags suffice for the first actual parent Read/shared child
and its Ready certificate. Graph, range, ownership, foreign-root cache and
visited-event facts are all taken from the constructed policy seed. This is a
lower-level borrow protocol theorem, not a Rust-history reachability claim. -/
theorem shared_ready (rootTag parentTag childTag : BorTag)
    (rootOrder : rootTag.value < parentTag.value) (childOrder : parentTag.value < childTag.value) :
    let seed := input rootTag parentTag childTag rootOrder childOrder
    (read seed {}).status = .Completed ∧ (child seed {}).outcome = .ok () ∧
      ∃ postLocation postRoot requestNode,
        (child seed {}).tree.locations = homogeneous 1 postLocation ∧
        Ready (child seed {}).tree postLocation second postRoot
          ⟨childTag,GeneralBorrowFreshMetadataChildShared.index seed,requestNode⟩ ∧
        postLocation.exposedCache = GeneralBorrowTwoRootConstructed.location.exposedCache := by
  let seed := input rootTag parentTag childTag rootOrder childOrder
  have lower : rootTag.value ≤ parentTag.value := UInt64.le_iff_toNat_le.mpr (by
    have ordered := UInt64.lt_iff_toNat_lt.mp rootOrder
    omega)
  have built := GeneralBorrowTwoRootParentRead.read_append_ready seed GeneralBorrowTwoRootConstructed.location {}
    rfl rfl first (rootNode rootTag true) rfl rfl (by change second ≠ first;decide +kernel) rfl
    (GeneralBorrowTwoRootPolicySeed.activated_forest rootTag parentTag)
    (GeneralBorrowTwoRootPolicySeed.activated_owned rootTag parentTag .Read)
    (GeneralBorrowTwoRootPolicySeed.activated_foreign_data rootTag parentTag lower)
    (GeneralBorrowTwoRootPolicySeed.activated_read_unexposed rootTag parentTag)
  obtain ⟨readDone,childDone,location,postRoot,node,locations,ready,cache,_⟩ := built
  exact ⟨readDone,childDone,location,postRoot,node,locations,ready,cache⟩

/-- Actual policy/exposure construction, activating Write, parent Read and
shared append form the first Ready leaf from ordered tags alone. This theorem
concerns the lower-level borrow protocol, not Rust caller reachability. -/
theorem construct (rootTag parentTag childTag : BorTag)
    (rootOrder : rootTag.value < parentTag.value) (childOrder : parentTag.value < childTag.value) :
    Miri.TreeBorrows.RetagPolicy.create ⟨true,true,true⟩ .Mutable .Default ⟨false,false⟩ =
      some GeneralBorrowTwoRootPolicySeed.policy ∧
    Miri.TreeBorrows.RetagPolicy.initialLocationState GeneralBorrowTwoRootPolicySeed.policy true =
      .ok GeneralBorrowTwoRootPolicySeed.reserved ∧
    let exposed := (BorrowTree.new rootTag (Size.ofBytes 1)).exposeTag {} rootTag
    let built := exposed.tree.newChild Size.ZERO .wildcard parentTag
      (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowTwoRootPolicySeed.reserved)
      GeneralBorrowTwoRootPolicySeed.policy.outsidePermission GeneralBorrowTwoRootPolicySeed.policy.protector.isSome
    let activated := built.tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes 0) (Size.ofBytes 1)
      .Write {} .VisitChildrenOfAccessed
    let seed := input rootTag parentTag childTag rootOrder childOrder
    exposed.outcome = .ok () ∧ built.outcome = .ok () ∧ activated.status = .Completed ∧ activated.tree = seed.tree ∧
    (read seed {}).status = .Completed ∧ (child seed {}).outcome = .ok () ∧
      ∃ postLocation postRoot requestNode,
        (child seed {}).tree.locations = homogeneous 1 postLocation ∧
        Ready (child seed {}).tree postLocation second postRoot
          ⟨childTag,GeneralBorrowFreshMetadataChildShared.index seed,requestNode⟩ ∧
        postLocation.exposedCache = GeneralBorrowTwoRootConstructed.location.exposedCache := by
  have policy := GeneralBorrowTwoRootPolicySeed.construct rootTag parentTag rootOrder
  have execution := policy.2.2
  have ready := shared_ready rootTag parentTag childTag rootOrder childOrder
  dsimp only at execution ⊢
  exact ⟨policy.1,policy.2.1,execution.1,execution.2.1,execution.2.2.1,execution.2.2.2.1,ready⟩

end DuplicatePrefix.GeneralBorrowTwoRootSeedShared
