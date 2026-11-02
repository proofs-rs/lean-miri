import duplicate_prefix.GeneralBorrowExposeReadFormation
import duplicate_prefix.GeneralBorrowReadFrozen
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowReadCacheFrame
namespace DuplicatePrefix.GeneralBorrowExposeReadParentRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.RangeMapNonempty DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def read (input : GeneralBorrowFreshMetadataChildShared.Input) (protections : ProtectedTags) :=
  input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes 0) (Size.ofBytes 1)
    .Read protections .VisitChildrenOfAccessed

def readLocation (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) :=
  (input.tree.performNormalAccessAt location input.parent .Read protections .VisitChildrenOfAccessed).location

/-- The full concrete ranged Read is derived from initial single-root graph
and permission ownership. The returned location is the actual normal access. -/
theorem read_exact (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (initial : input.tree.locations = homogeneous 1 location)
    (roots : input.tree.roots = #[input.parent])
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection input.tree location protections) input.parent.toNat .Read) :
    (read input protections).status = .Completed ∧
    (read input protections).tree = {input.tree with locations := homogeneous 1 (readLocation input location protections)} := by
  have success := GeneralBorrowSingleRoot.access_at input.tree location protections input.parent input.parent .Read
    .VisitChildrenOfAccessed ⟨0,1⟩ forest owned input.depth input.children input.parentNode input.parentPresent roots input.covered
  have normal := GeneralBorrowRangePreserves.single_root_location input.tree location protections input.parent input.parent .Read
    .VisitChildrenOfAccessed ⟨0,1⟩ forest owned input.depth input.children input.parentNode input.parentPresent roots input.covered
  have tagged : input.tree.indexOfTag input.parentTag = some input.parent := input.parentTagPresent
  unfold read BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,initial]
  have zero : Size.ofBytes 0 = Size.ZERO := rfl
  rw [zero,iter_mut_homogeneous_full (1 : UInt64) location (by decide)]
  simp only [Array.size_singleton,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
  rw [setAtPos_exact (homogeneous (1 : UInt64) location) 0 (by change 0<1;decide)]
  simp only [success,normal]
  constructor
  · trivial
  · rfl

/-- Initial append data transports to the actual normal Read location using
unchanged graph metadata and the derived one-byte geometry. -/
def afterReadInput (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (offset : input.offset = 0) (length : input.len = 1) :
    GeneralBorrowFreshMetadataChildShared.Input where
  tree := {input.tree with locations := homogeneous 1 (readLocation input location protections)}
  depth := input.depth
  children := input.children
  covered := input.covered
  parentTag := input.parentTag
  newTag := input.newTag
  parent := input.parent
  parentNode := input.parentNode
  parentTagPresent := input.parentTagPresent
  parentPresent := input.parentPresent
  fresh := input.fresh
  noFree := input.noFree
  aligned := input.aligned
  fits := input.fits
  isProtected := input.isProtected
  offset := input.offset
  len := input.len
  nonzero := input.nonzero
  well := by simp [homogeneous,DedupRangeMap.WellFormed]
  bounds := by simp [offset,length,homogeneous,DedupRangeMap.size,Size.ofBytes]


/-- The preceding actual parent Read preserves every initial Ready sibling;
metadata and isExposed flags are unchanged by ranged accesses. -/
theorem read_ready (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (offset : input.offset = 0) (length : input.len = 1)
    (request : Request) (rootNode : TreeNode) (ready : Ready input.tree location input.parent rootNode request) :
    Ready (afterReadInput input location protections offset length).tree
      (readLocation input location protections) input.parent rootNode request := by
  exact ⟨ready.tagged,ready.present,ready.rootPresent,ready.different,ready.parent,ready.parentless,
    ready.unexposed,GeneralBorrowReadFrozen.normal_frozen input.tree location protections input.parent
      request.leaf request.node .VisitChildrenOfAccessed ready.present ready.frozen⟩

def child (input : GeneralBorrowFreshMetadataChildShared.Input) (protections : ProtectedTags) :=
  (read input protections).tree.newChild (Size.ofBytes 0) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected

/-- A complete actual parent Read and shared append forms a new Ready leaf,
retains the whole old Ready family, and preserves the initial exposure cache.
The singleton-root and ownership hypotheses concern only the initial state. -/
theorem read_append_ready (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (offset : input.offset = 0) (length : input.len = 1)
    (initial : input.tree.locations = homogeneous 1 location)
    (roots : input.tree.roots = #[input.parent]) (parentless : input.parentNode.parent = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection input.tree location protections) input.parent.toNat .Read)
    (unexposed : ∀ index node, input.tree.nodeAt index = some node → node.isExposed = false) :
    (read input protections).status = .Completed ∧ (child input protections).outcome = .ok () ∧
    ∃ postLocation postRoot requestNode,
      (child input protections).tree.locations = homogeneous 1 postLocation ∧
      Ready (child input protections).tree postLocation input.parent postRoot
        ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache ∧
      ∀ (request : Request) (rootNode : TreeNode),
        Ready input.tree location input.parent rootNode request →
        ∃ nextNode, Ready (child input protections).tree postLocation input.parent postRoot
          ⟨request.tag,request.leaf,nextNode⟩ ∧ nextNode.tag = request.node.tag := by
  let prepared := afterReadInput input location protections offset length
  have readFacts := read_exact input location protections initial roots forest owned
  have childEq : child input protections = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag
      (DedupRangeMap.new (Size.ofBytes prepared.len) GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    simp only [child,readFacts.2,prepared,afterReadInput,offset,length]
  have treeEq : (child input protections).tree = result prepared := by rw [childEq];rfl
  have built := GeneralBorrowExposeReadFormation.append_ready_preserves prepared
    (readLocation input location protections) offset length rfl parentless
  obtain ⟨postLocation,postRoot,newNode,locations,newReady,cacheEq,preserved⟩ := built
  have readCache := GeneralBorrowReadCacheFrame.normal_cache input.tree location input.parent .Read protections
    .VisitChildrenOfAccessed unexposed
  refine ⟨readFacts.1,?_,postLocation,postRoot,newNode,?_,?_,cacheEq.trans readCache,?_⟩
  · rw [childEq]
    exact (GeneralBorrowFreshMetadataChildShared.append prepared).success
  · rw [treeEq];exact locations
  · rw [treeEq];exact newReady
  · intro request rootNode ready
    rw [treeEq]
    exact preserved request rootNode (read_ready input location protections offset length request rootNode ready)

end DuplicatePrefix.GeneralBorrowExposeReadParentRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowExposeReadParentRead." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved parent Read dependency {dependency}"
