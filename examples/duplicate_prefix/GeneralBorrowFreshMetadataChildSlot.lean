import duplicate_prefix.GeneralBorrowFreshMetadataChildShared
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse
import duplicate_prefix.GeneralBorrowFreshReborrowStages
namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildSlot
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowGraph DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshAnchor (sharedNode sharedState)
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

def result (tree : BorrowTree) (parentTag newTag : BorTag) (isProtected : Bool) (offset len : UInt64) : BorrowTree :=
  (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected).tree

structure Output (tree : BorrowTree) (parentTag newTag : BorTag) (parent child : UniIndex)
    (isProtected : Bool) (offset len : UInt64) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates (result tree parentTag newTag isProtected offset len)
  roots : (result tree parentTag newTag isProtected offset len).roots = tree.roots
  lookup : (result tree parentTag newTag isProtected offset len).indexOfTag newTag = some child
  node : ∃ node, (result tree parentTag newTag isProtected offset len).nodeAt child = some node ∧
    node.tag = newTag ∧ node.isExposed = false
  oldLookup : ∀ tag, newTag ≠ tag → (result tree parentTag newTag isProtected offset len).indexOfTag tag = tree.indexOfTag tag
  extension : ∀ oldLocation newLocation protections,
    GeneralBorrowFreshTopology.Extension (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (result tree parentTag newTag isProtected offset len) newLocation protections).topology parent.toNat ∨
    GeneralBorrowFreshReuseTopology.Extension (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (result tree parentTag newTag isProtected offset len) newLocation protections).topology child.toNat parent.toNat

/-- Common metadata of either actual allocator branch, ready for a second shared reborrow. -/
def build (tree : BorrowTree) (depth : ParentDepth tree.nodes) (children : ChildNodes tree) (covered : RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    Output tree parentTag newTag parent (index slot) isProtected offset len := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildShared.append input
    refine ⟨data.certificates,data.roots,data.freshLookup,?_,data.oldLookup,?_⟩
    · obtain ⟨node,lookup,tag,_,_,_,exposed⟩ := data.newNode
      exact ⟨node,lookup,tag,exposed⟩
    · intro oldLocation newLocation protections
      exact Or.inl (data.extension oldLocation newLocation protections)
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        child,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    refine ⟨data.certificates,data.roots,data.freshLookup,?_,data.oldLookup,?_⟩
    · obtain ⟨node,lookup,tag,_,_,_,exposed⟩ := data.newNode
      exact ⟨node,lookup,tag,exposed⟩
    · intro oldLocation newLocation protections
      exact Or.inr (data.extension oldLocation newLocation protections)

end DuplicatePrefix.GeneralBorrowFreshMetadataChildSlot
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildSlot." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved slot metadata dependency {dependency}"
