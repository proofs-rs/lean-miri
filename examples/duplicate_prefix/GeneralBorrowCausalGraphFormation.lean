import duplicate_prefix.GeneralBorrowConcreteChildCausalOrder
import duplicate_prefix.GeneralBorrowWildcardChildCausalOrder
import duplicate_prefix.GeneralBorrowParentTagRelease
namespace DuplicatePrefix.GeneralBorrowCausalGraphFormation
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Count-independent graph-formation evidence. Root/borrow/access/release/GC
rules use actual tree operations, including their error results. The node-origin
frame rule overapproximates edits retaining stored tag/parent metadata. This is NOT a definition
of all valid callers or a claim of exhaustive canonical-interpreter reachability.
The allocatedConcrete rule remembers the ORIGINAL allocated tag/runtime before
parent accesses, rather than using the already-advanced counter. In particular
canonical TypedRetag hook/global materialization lifts must still
be supplied for an arbitrary pre-call machine state. No rule assumes tag order,
access/constructor success, target execution or target safety. -/
inductive Formed : BorrowTree → Prop where
  | root (tag : BorTag) (size : Size) : Formed (BorrowTree.new tag size)
  | frame {before after : BorrowTree} (previous : Formed before)
      (origins : ∀ index node, after.nodes.get index = some node →
        ∃ old, before.nodes.get index = some old ∧ old.tag = node.tag ∧ old.parent = node.parent) : Formed after
  | concrete {tree : BorrowTree} (previous : Formed tree) (global : GlobalState)
      (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
      (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
      (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some node)
      (room : tree.nodes.size+1 ≤ 4294967295)
      (offset : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) :
      Formed (tree.newChild offset (.concrete parentTag) global.nextPointerTag inside outside held).tree
  | allocatedConcrete {before current : BorrowTree} (previous : Formed before)
      (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts before global)
      (nodes : current.nodes = before.nodes) (mapping : current.tagMapping = before.tagMapping)
      (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
      (tagged : before.indexOfTag parentTag = some parent) (present : before.nodeAt parent = some node)
      (room : before.nodes.size+1 ≤ 4294967295)
      (offset : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) :
      Formed (current.newChild offset (.concrete parentTag) global.nextPointerTag inside outside held).tree
  | wildcard {tree : BorrowTree} (previous : Formed tree) (global : GlobalState)
      (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
      (room : tree.nodes.size+1 ≤ 4294967295)
      (offset : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) :
      Formed (tree.newChild offset .wildcard global.nextPointerTag inside outside held).tree
  | access {tree : BorrowTree} (previous : Formed tree) (provenance : ProvenanceExtra)
      (offset len : Size) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) :
      Formed (tree.performBorrowAccessRange provenance offset len kind protections mode).tree
  | expose {tree : BorrowTree} (previous : Formed tree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
      (protections : ProtectedTags) (tag : BorTag) : Formed (tree.exposeTag protections tag).tree
  | release {tree : BorrowTree} (previous : Formed tree) (protections : ProtectedTags) (tag : BorTag) :
      Formed (tree.releaseProtector tag protections).tree
  | collect {tree : BorrowTree} (previous : Formed tree)
      (initial : GeneralBorrowStructuralHistoryState.State tree) (live : Array BorTag) :
      Formed (tree.removeUnreachableTags live).tree

/-- Causal order is DERIVED by induction over actual graph generation. The
initial-state candidate RuntimeFacts alone does not imply this theorem. -/
theorem order {tree : BorrowTree} (formed : Formed tree) :
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree := by
  induction formed with
  | root tag size => exact GeneralBorrowParentTagRootFrames.new_root tag size
  | frame previous origins ih =>
    intro child node present parent parentNode edge parentPresent
    obtain ⟨old,oldPresent,tag,parents⟩ := origins child node present
    obtain ⟨oldParent,oldParentPresent,parentTag,_⟩ := origins parent parentNode parentPresent
    have bounded := ih child old oldPresent parent oldParent (parents.trans edge) oldParentPresent
    simpa only [tag,parentTag] using bounded
  | concrete previous global runtime parentTag parent node tagged present room offset inside outside held ih =>
    exact GeneralBorrowConcreteChildCausalOrder.preserves _ global runtime ih parentTag parent node tagged present room offset inside outside held
  | @allocatedConcrete before current previous global runtime nodes mapping parentTag parent node tagged present room offset inside outside held ih =>
    obtain ⟨map,index,inserted,_,vacant,_⟩ := GeneralBorrowWildcardConstructorSlot.select before global runtime
      global.nextPointerTag (GeneralBorrowParentTagInvariant.fresh before global runtime) room outside .None
    have depth : GeneralBorrowExposure.ParentDepth current.nodes := by
      rw [nodes]
      exact GeneralBorrowStructuralHistoryShared.depth before runtime.formed.toState
    have taggedNow : current.indexOfTag parentTag = some parent := by
      simpa only [BorrowTree.indexOfTag,mapping] using tagged
    have presentNow : current.nodeAt parent = some node := by
      simpa only [BorrowTree.nodeAt,nodes] using present
    have insertedNow : current.tagMapping.insert global.nextPointerTag = .Inserted map index := by rw [mapping];exact inserted
    have vacantNow : current.nodes.get index = none := by rw [nodes];exact vacant
    exact GeneralBorrowConcreteChildCausalOrder.inserted_order current depth
      (GeneralBorrowParentTagInvariant.nodes_frame before current nodes ih)
      parentTag global.nextPointerTag parent node map index insertedNow vacantNow taggedNow presentNow
      (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp
        (GeneralBorrowParentTagInvariant.parent_below_fresh before global runtime parent node present))))
      offset inside outside held
  | wildcard previous global runtime room offset inside outside held ih =>
    exact GeneralBorrowWildcardChildCausalOrder.preserves _ global runtime ih room offset inside outside held
  | access previous provenance offset len kind protections mode ih =>
    exact GeneralBorrowParentTagOperations.access _ ih provenance offset len kind protections mode
  | expose previous depth protections tag ih =>
    exact GeneralBorrowParentTagOperations.expose_all _ ih depth protections tag
  | release previous protections tag ih => exact GeneralBorrowParentTagRelease.release_order _ protections tag ih
  | @collect tree previous initial live ih =>
    obtain ⟨forest⟩ := initial.forest (⟨{},{}⟩ : LocationTree) {}
    obtain ⟨depth⟩ := initial.depth
    exact GeneralBorrowParentTagInvariant.collect tree (⟨{},{}⟩ : LocationTree) {} forest depth initial.children initial.fits initial.rootNodes initial.well ih live
end DuplicatePrefix.GeneralBorrowCausalGraphFormation
