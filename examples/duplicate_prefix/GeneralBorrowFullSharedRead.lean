import duplicate_prefix.GeneralBorrowSharedProfileParentRead
import duplicate_prefix.GeneralBorrowExposeReadFormation
import duplicate_prefix.GeneralBorrowReadFrozen
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowReadCacheFrame
namespace DuplicatePrefix.GeneralBorrowFullSharedRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.RangeMapNonempty DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def read (input : GeneralBorrowFreshMetadataChildShared.Input) (protections : ProtectedTags) :=
  input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes 0) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed

def readLocation (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) :=
  (input.tree.performNormalAccessAt location input.parent .Read protections .VisitChildrenOfAccessed).location

/-- The full concrete ranged Read is derived from initial single-root graph
and permission ownership. The returned location is the actual normal access. -/
theorem read_exact (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (nonzero : input.len ≠ 0) (initial : input.tree.locations = homogeneous input.len location)
    (roots : input.tree.roots = #[input.parent])
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection input.tree location protections) input.parent.toNat .Read) :
    (read input protections).status = .Completed ∧
    (read input protections).tree = {input.tree with locations := homogeneous input.len (readLocation input location protections)} := by
  have success := GeneralBorrowSingleRoot.access_at input.tree location protections input.parent input.parent .Read
    .VisitChildrenOfAccessed ⟨0,input.len⟩ forest owned input.depth input.children input.parentNode input.parentPresent roots input.covered
  have normal := GeneralBorrowRangePreserves.single_root_location input.tree location protections input.parent input.parent .Read
    .VisitChildrenOfAccessed ⟨0,input.len⟩ forest owned input.depth input.children input.parentNode input.parentPresent roots input.covered
  have tagged : input.tree.indexOfTag input.parentTag = some input.parent := input.parentTagPresent
  unfold read BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,initial]
  have zero : Size.ofBytes 0 = Size.ZERO := rfl
  rw [zero,iter_mut_homogeneous_full input.len location nonzero]
  simp only [Array.size_singleton,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
  rw [setAtPos_exact (homogeneous input.len location) 0 (by change 0<1;decide)]
  simp only [success,normal]
  constructor
  · trivial
  · rfl

/-- Initial append data transports to the actual normal Read location using
unchanged graph metadata and the derived full-slice geometry. -/
def afterReadInput (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (offset : input.offset = 0)  :
    GeneralBorrowFreshMetadataChildShared.Input where
  tree := {input.tree with locations := homogeneous input.len (readLocation input location protections)}
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
  well := by simp [homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr input.nonzero]
  bounds := by
    have positive : 0 < input.len := UInt64.pos_iff_ne_zero.mpr input.nonzero
    simp [offset,homogeneous,DedupRangeMap.size,Size.ofBytes,positive]



/-- A genuine full-slice concrete single-root parent Read completes, retains the
exact generator profile (including sparse vacant Clean), and supplies ownership
for the next Read. Graph, settings and initial profile remain explicit; neither
operation success nor a poststate is an input. This does not yet include append. -/
theorem read_closed (input : Input) (location : LocationTree)
    (offset : input.offset = 0)
    (initial : input.tree.locations = RangeMapNonempty.homogeneous input.len location)
    (roots : input.tree.roots = #[input.parent])
    (parentless : input.parentNode.parent = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location {}).topology)
    (profile : Profile input.tree location input.parent) :
    (read input {}).status = .Completed ∧
    (read input {}).tree = (afterReadInput input location {} offset).tree ∧
    Profile (afterReadInput input location {} offset).tree (readLocation input location {}) input.parent ∧
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection (afterReadInput input location {} offset).tree (readLocation input location {}) {})
      input.parent.toNat .Read := by
  have owned := read_owned input location parentless profile
  have facts := read_exact input location {} input.nonzero initial roots forest owned
  have valid := owned.anchorValid
  have preserved := GeneralBorrowSharedProfileRead.normal input location {} .VisitChildrenOfAccessed profile
    (by
      intro event member
      have classified := (GeneralBorrowTraversal.traversal_data _ forest input.parent.toNat valid
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection input.tree location {}) .Read)).2 event member
      simpa only [GeneralBorrowSharedProfileParentRead.parent_path input location {} parentless,List.mem_singleton] using classified.2)
  have nextProfile : Profile (afterReadInput input location {} offset).tree
      (readLocation input location {}) input.parent :=
    ⟨preserved.rootStored,preserved.shared,preserved.vacant⟩
  exact ⟨facts.1,facts.2,nextProfile,
    read_owned (afterReadInput input location {} offset) (readLocation input location {}) parentless nextProfile⟩

def child (input : Input) (protections : ProtectedTags) :=
  (read input protections).tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected

end DuplicatePrefix.GeneralBorrowFullSharedRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved full-slice Read dependency {dependency}"
