import duplicate_prefix.GeneralBorrowFreshMetadataChildAttach
import duplicate_prefix.GeneralBorrowFreshSharedChild

namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildShared
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowGraph DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshAnchor (sharedNode sharedState)
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Explicit data for an actual shared append, with no assumed operation
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
  noFree : tree.tagMapping.deassigned.back? = none
  aligned : tree.tagMapping.mapping.size = tree.nodes.data.size
  fits : tree.tagMapping.mapping.size ≤ 4294967295
  isProtected : Bool
  offset : UInt64
  len : UInt64
  nonzero : len ≠ 0
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat

def index (input : Input) : UniIndex := ⟨UInt32.ofNat input.tree.tagMapping.mapping.size⟩
def mapping (input : Input) : UniKeyMap BorTag :=
  ⟨input.tree.tagMapping.mapping.push (input.newTag,index input),input.tree.tagMapping.deassigned⟩
def locations (input : Input) : DedupRangeMap LocationTree :=
  (input.tree.locations.modifyRange (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location (index input) sharedState)).state

def result (input : Input) : BorrowTree :=
  (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) sharedState) .Frozen input.isProtected).tree

theorem at_end (input : Input) : (index input).toNat = input.tree.nodes.data.size := by
  have fits : input.tree.tagMapping.mapping.size < 2^32 := by have bound := input.fits;omega
  simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt fits]
  exact input.aligned

def stage (input : Input) : BorrowTree :=
  GeneralBorrowFreshMetadataChildAttach.staged input.tree (index input) input.parent input.parentNode
    (sharedNode input.newTag input.parent) (mapping input) (locations input)

theorem tree_eq (input : Input) : result input =
    (sourceUpdateSifa (stage input) input.parent .Read).1 := by
  simpa only [result,stage,GeneralBorrowFreshMetadataChildAttach.staged,index,mapping,locations] using
    GeneralBorrowFreshSharedChild.append_tree input.tree input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits
    input.isProtected input.offset input.len input.nonzero input.well input.bounds

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
    (DedupRangeMap.new (Size.ofBytes input.len) sharedState) .Frozen input.isProtected).outcome = .ok ()
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates (result input)
  mapping : (result input).tagMapping = mapping input
  roots : (result input).roots = input.tree.roots
  size : (result input).nodes.size = input.tree.nodes.size+1
  aligned : (result input).tagMapping.mapping.size = (result input).nodes.data.size
  noFree : (result input).tagMapping.deassigned.back? = none
  freshLookup : (result input).indexOfTag input.newTag = some (index input)
  oldLookup : ∀ tag, input.newTag ≠ tag → (result input).indexOfTag tag = input.tree.indexOfTag tag
  newNode : ∃ node, (result input).nodeAt (index input) = some node ∧ node.tag = input.newTag ∧
    node.parent = some input.parent ∧ node.children = #[] ∧ node.defaultInitialPermission = .Frozen ∧ node.isExposed = false
  extension : ∀ oldLocation newLocation protections,
    GeneralBorrowFreshTopology.Extension (source_normal_projection input.tree oldLocation protections).topology
      (source_normal_projection (result input) newLocation protections).topology input.parent.toNat

/-- Derive metadata of the actual shared constructor from caller data and
certificates, including its completion; operation success is not a premise. -/
def append (input : Input) : Output input := by
  have same := shape input
  have exposed := exposure input
  have cert : GeneralBorrowFreshMetadataChildAttach.Certificates (result input) := by
    exact GeneralBorrowFreshMetadataChildAttach.append input.tree input.depth input.children input.covered
      (index input) input.parent input.parentNode (sharedNode input.newTag input.parent)
      (at_end input) input.parentPresent rfl rfl (mapping input) (locations input) (result input) same
  have data : (result input).tagMapping = mapping input ∧ (result input).roots = input.tree.roots ∧
      (result input).nodes.size = input.tree.nodes.size+1 := by
    exact GeneralBorrowFreshMetadataChildAttach.allocator input.tree (index input) input.parent input.parentNode
      (sharedNode input.newTag input.parent) (at_end input) input.parentPresent (mapping input) (locations input) (result input) same
  refine {
    success := GeneralBorrowFreshSharedChild.append_success input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
      input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len input.nonzero input.well input.bounds
    certificates := cert,mapping := data.1,roots := data.2.1,size := data.2.2
    aligned := ?_,noFree := ?_,freshLookup := ?_,oldLookup := ?_,newNode := ?_,extension := ?_ }
  · change (result input).tagMapping.mapping.size = (result input).nodes.size
    rw [data.1,data.2.2]
    simp only [mapping,Array.size_push]
    exact congrArg (fun n => n+1) input.aligned
  · rw [data.1]
    exact input.noFree
  · change (result input).tagMapping.get input.newTag = some (index input)
    rw [data.1]
    exact GeneralBorrowTagMap.pushed_get_new input.tree.tagMapping input.newTag input.fresh (index input) _
  · intro tag different
    change (result input).tagMapping.get tag = input.tree.tagMapping.get tag
    rw [data.1]
    exact GeneralBorrowTagMap.pushed_get_old input.tree.tagMapping input.newTag tag different (index input) _
  · exact GeneralBorrowFreshMetadataChildAttach.new_node input.tree (index input) input.parent input.parentNode
      (sharedNode input.newTag input.parent) (at_end input) input.parentPresent (mapping input) (locations input) (result input) same exposed
  · intro oldLocation newLocation protections
    exact GeneralBorrowFreshMetadataChildAttach.topology_extension input.tree (index input) input.parent input.parentNode
      (sharedNode input.newTag input.parent) (at_end input) input.parentPresent rfl rfl
      (mapping input) (locations input) (result input) same oldLocation newLocation protections

end DuplicatePrefix.GeneralBorrowFreshMetadataChildShared
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildShared." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual shared child metadata dependency {dependency}"
