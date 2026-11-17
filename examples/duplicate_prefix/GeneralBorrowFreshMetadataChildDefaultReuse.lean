import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowFreshMetadataChildReuseAttach
import duplicate_prefix.GeneralBorrowFreshResult
import duplicate_prefix.GeneralBorrowFreshReuseChild

namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildDefaultReuse
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowGraph DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshDefaultChild (child inside)
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Explicit data for an actual mutable vacant-slot reuse, with no assumed operation
success and no permission/ownership assumption outside the requested range. -/
structure Input where
  tree : BorrowTree
  depth : ParentDepth tree.nodes
  children : ChildNodes tree
  covered : RootsCover tree
  parentTag : BorTag
  newTag : BorTag
  parent : UniIndex
  parentNode : TreeNode
  parentTagPresent : tree.tagMapping.get parentTag = some parent
  parentPresent : tree.nodeAt parent = some parentNode
  fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  index : UniIndex
  available : tree.tagMapping.deassigned.back? = some index
  valid : index.toNat < tree.nodes.data.size
  vacant : tree.nodes.get index = none
  parentSlack : depth.depth parent < tree.nodes.size
  offset : UInt64
  len : UInt64
  nonzero : len ≠ 0
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat

def index (input : Input) : UniIndex := input.index
def mapping (input : Input) : UniKeyMap BorTag :=
  ⟨input.tree.tagMapping.mapping.push (input.newTag,index input),input.tree.tagMapping.deassigned.pop⟩
def locations (input : Input) : DedupRangeMap LocationTree :=
  (input.tree.locations.modifyRange (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location (index input) inside)).state

def result (input : Input) : BorrowTree :=
  (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) false).tree

def stage (input : Input) : BorrowTree :=
  GeneralBorrowFreshMetadataChildAttach.staged input.tree (index input) input.parent input.parentNode
    (child input.newTag input.parent) (mapping input) (locations input)

theorem tree_eq (input : Input) : result input =
    (sourceUpdateSifa (stage input) input.parent .Read).1 := by
  simpa only [result,stage,GeneralBorrowFreshMetadataChildAttach.staged,index,mapping,locations,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshMaterialization.materialized] using
    GeneralBorrowFreshDefaultChild.reuse_tree input.tree input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh (index input) input.available input.valid input.vacant
    input.offset input.len input.nonzero input.well input.bounds

theorem shape (input : Input) : treeShape (result input) = treeShape (stage input) :=
  (congrArg treeShape (tree_eq input)).trans
    (GeneralBorrowSifaView.preserves (stage input) input.parent .Read)

theorem exposure (input : Input) : GeneralBorrowFreshMetadataChildSifa.exposureShape (result input) =
    GeneralBorrowFreshMetadataChildSifa.exposureShape (stage input) :=
  (congrArg GeneralBorrowFreshMetadataChildSifa.exposureShape (tree_eq input)).trans
    (GeneralBorrowFreshMetadataChildSifa.sifa_exposure (stage input) input.parent .Read)

/-- All structural and allocator facts needed to use the fresh tag as a later
reborrow parent. The exposure flag is proved for the actual SIFA result. -/
structure Output (input : Input) where
  success : (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) false).outcome = .ok ()
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates (result input)
  mapping : (result input).tagMapping = mapping input
  roots : (result input).roots = input.tree.roots
  size : (result input).nodes.size = input.tree.nodes.size
  mappingSize : (result input).tagMapping.mapping.size = input.tree.tagMapping.mapping.size+1
  freePool : (result input).tagMapping.deassigned = input.tree.tagMapping.deassigned.pop
  freshLookup : (result input).indexOfTag input.newTag = some (index input)
  oldLookup : ∀ tag, input.newTag ≠ tag → (result input).indexOfTag tag = input.tree.indexOfTag tag
  newNode : ∃ node, (result input).nodeAt (index input) = some node ∧ node.tag = input.newTag ∧
    node.parent = some input.parent ∧ node.children = #[] ∧ node.defaultInitialPermission = .ReservedFrz false ∧ node.isExposed = false
  extension : ∀ oldLocation newLocation protections,
    GeneralBorrowFreshReuseTopology.Extension (source_normal_projection input.tree oldLocation protections).topology
      (source_normal_projection (result input) newLocation protections).topology (index input).toNat input.parent.toNat

/-- Derive metadata of the actual mutable constructor from caller data and
certificates, including its completion; operation success is not a premise. -/
def reuse (input : Input) : Output input := by
  have same := shape input
  have exposed := exposure input
  have cert : GeneralBorrowFreshMetadataChildAttach.Certificates (result input) := by
    exact GeneralBorrowFreshMetadataChildReuseAttach.reuse input.tree input.depth input.children input.covered
      (index input) input.parent input.parentNode (child input.newTag input.parent)
      input.valid input.vacant input.parentPresent rfl rfl input.parentSlack (mapping input) (locations input) (result input) same
  have data : (result input).tagMapping = mapping input ∧ (result input).roots = input.tree.roots ∧
      (result input).nodes.size = input.tree.nodes.size := by
    exact GeneralBorrowFreshMetadataChildReuseAttach.allocator input.tree (index input) input.parent input.parentNode
      (child input.newTag input.parent) input.valid input.vacant input.parentPresent (mapping input) (locations input) (result input) same
  refine {
    success := GeneralBorrowFreshDefaultChild.reuse_success input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
      input.parentTagPresent input.parentPresent input.fresh (index input) input.available input.valid input.vacant input.parentSlack input.offset input.len input.nonzero input.well input.bounds
    certificates := cert,mapping := data.1,roots := data.2.1,size := data.2.2
    mappingSize := ?_,freePool := ?_,freshLookup := ?_,oldLookup := ?_,newNode := ?_,extension := ?_ }
  · rw [data.1]
    simp only [mapping,Array.size_push]
  · rw [data.1]
    rfl
  · change (result input).tagMapping.get input.newTag = some (index input)
    rw [data.1]
    exact GeneralBorrowTagMap.pushed_get_new input.tree.tagMapping input.newTag input.fresh (index input) _
  · intro tag different
    change (result input).tagMapping.get tag = input.tree.tagMapping.get tag
    rw [data.1]
    exact GeneralBorrowTagMap.pushed_get_old input.tree.tagMapping input.newTag tag different (index input) _
  · exact GeneralBorrowFreshMetadataChildReuseAttach.new_node input.tree (index input) input.parent input.parentNode
      (child input.newTag input.parent) input.valid input.vacant input.parentPresent (mapping input) (locations input) (result input) same exposed
  · intro oldLocation newLocation protections
    exact GeneralBorrowFreshMetadataChildReuseAttach.topology_extension input.tree (index input) input.parent input.parentNode
      (child input.newTag input.parent) input.valid input.vacant input.parentPresent rfl rfl
      (mapping input) (locations input) (result input) same oldLocation newLocation protections

end DuplicatePrefix.GeneralBorrowFreshMetadataChildDefaultReuse
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildDefaultReuse." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual mutable child metadata dependency {dependency}"
