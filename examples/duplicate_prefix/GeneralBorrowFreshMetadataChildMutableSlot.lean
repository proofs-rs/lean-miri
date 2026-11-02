import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
import duplicate_prefix.GeneralBorrowFreshReborrowStages
import duplicate_prefix.GeneralBorrowFreshMutableGeometry
namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildMutableSlot
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowGraph DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshChild (child inside)
open DuplicatePrefix.GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def index {tree : BorrowTree} {depth : ParentDepth tree.nodes} {parent : UniIndex} : Slot tree depth parent → UniIndex
  | .append .. => ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  | .reuse child .. => child

/-- A frame equality transports allocator data without assuming an access succeeds. -/
def transport (before after : BorrowTree) (depth : ParentDepth before.nodes)
    (nextDepth : ParentDepth after.nodes) (nodes : after.nodes = before.nodes)
    (mapping : after.tagMapping = before.tagMapping) (ranks : nextDepth.depth = depth.depth)
    (parent : UniIndex) (slot : Slot before depth parent) : Slot after nextDepth parent := by
  cases slot with
  | append noFree aligned fits =>
    apply Slot.append
    · simpa only [mapping] using noFree
    · simpa only [mapping,nodes] using aligned
    · simpa only [mapping] using fits
  | reuse child available bounded vacant slack =>
    apply Slot.reuse child
    · simpa only [mapping] using available
    · simpa only [nodes] using bounded
    · simpa only [nodes] using vacant
    · simpa only [ranks,nodes] using slack

theorem transport_index (before after : BorrowTree) (depth : ParentDepth before.nodes)
    (nextDepth : ParentDepth after.nodes) (nodes : after.nodes = before.nodes)
    (mapping : after.tagMapping = before.tagMapping) (ranks : nextDepth.depth = depth.depth)
    (parent : UniIndex) (slot : Slot before depth parent) :
    index (transport before after depth nextDepth nodes mapping ranks parent slot) = index slot := by
  cases slot <;> simp only [transport,index,mapping]

def result (tree : BorrowTree) (parentTag newTag : BorTag) (offset len : UInt64) : BorrowTree :=
  (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true).tree

structure Output (tree : BorrowTree) (parentTag newTag : BorTag) (parent child : UniIndex)
    (offset len : UInt64) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates (result tree parentTag newTag offset len)
  roots : (result tree parentTag newTag offset len).roots = tree.roots
  lookup : (result tree parentTag newTag offset len).indexOfTag newTag = some child
  node : ∃ node, (result tree parentTag newTag offset len).nodeAt child = some node ∧
    node.tag = newTag ∧ node.isExposed = false
  oldLookup : ∀ tag, newTag ≠ tag → (result tree parentTag newTag offset len).indexOfTag tag = tree.indexOfTag tag
  extension : ∀ oldLocation newLocation protections,
    GeneralBorrowFreshTopology.Extension (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (result tree parentTag newTag offset len) newLocation protections).topology parent.toNat ∨
    GeneralBorrowFreshReuseTopology.Extension (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (result tree parentTag newTag offset len) newLocation protections).topology child.toNat parent.toNat
  nodeFits : (result tree parentTag newTag offset len).nodes.data.size ≤ 4294967296
  well : (result tree parentTag newTag offset len).locations.WellFormed
  capacity : (result tree parentTag newTag offset len).locations.size = tree.locations.size
  mappingSize : (result tree parentTag newTag offset len).tagMapping.mapping.size = tree.tagMapping.mapping.size+1

/-- Common metadata of either actual allocator branch, ready for a second shared reborrow. -/
def build (tree : BorrowTree) (depth : ParentDepth tree.nodes) (children : ChildNodes tree) (covered : RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (nodeFits : tree.nodes.data.size ≤ 4294967296)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    Output tree parentTag newTag parent (index slot) offset len := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutable.append input
    refine ⟨data.certificates,data.roots,data.freshLookup,?_,data.oldLookup,?_,?_,?_,?_,?_⟩
    · obtain ⟨node,lookup,tag,_,_,_,exposed⟩ := data.newNode
      exact ⟨node,lookup,tag,exposed⟩
    · intro oldLocation newLocation protections
      exact Or.inl (data.extension oldLocation newLocation protections)
    · change (GeneralBorrowFreshMetadataChildMutable.result input).nodes.size ≤ _
      rw [data.size]
      change tree.nodes.data.size+1 ≤ _
      omega
    · exact (GeneralBorrowFreshMutableGeometry.append_frame input).1
    · exact (GeneralBorrowFreshMutableGeometry.append_frame input).2
    · change (GeneralBorrowFreshMetadataChildMutable.result input).tagMapping.mapping.size = _
      rw [data.mapping]
      simp only [GeneralBorrowFreshMetadataChildMutable.mapping,Array.size_push,input]
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    refine ⟨data.certificates,data.roots,data.freshLookup,?_,data.oldLookup,?_,?_,?_,?_,?_⟩
    · obtain ⟨node,lookup,tag,_,_,_,exposed⟩ := data.newNode
      exact ⟨node,lookup,tag,exposed⟩
    · intro oldLocation newLocation protections
      exact Or.inr (data.extension oldLocation newLocation protections)
    · change (GeneralBorrowFreshMetadataChildMutableReuse.result input).nodes.size ≤ _
      rw [data.size]
      exact nodeFits
    · exact (GeneralBorrowFreshMutableGeometry.reuse_frame input).1
    · exact (GeneralBorrowFreshMutableGeometry.reuse_frame input).2
    · change (GeneralBorrowFreshMetadataChildMutableReuse.result input).tagMapping.mapping.size = _
      rw [data.mapping]
      simp only [GeneralBorrowFreshMetadataChildMutableReuse.mapping,Array.size_push,input]

end DuplicatePrefix.GeneralBorrowFreshMetadataChildMutableSlot
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildMutableSlot." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved slot metadata dependency {dependency}"
