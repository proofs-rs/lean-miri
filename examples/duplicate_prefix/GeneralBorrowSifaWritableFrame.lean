import duplicate_prefix.GeneralBorrowSifaView
import duplicate_prefix.GeneralBorrowFreshMetadata
import duplicate_prefix.GeneralBorrowExposedConditionalWritePermissions
import duplicate_prefix.GeneralRangeMapState
namespace DuplicatePrefix.GeneralBorrowSifaWritableFrame
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowView GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Profile (tree : BorrowTree) (protections : ProtectedTags) (support : UniIndex→Prop)
    (location : LocationTree) : Prop :=
  ∀ query node,support query→tree.nodeAt query=some node→
    GeneralBorrowExposedConditionalWritePermissions.Compatible
      (GeneralBorrowWildcardVirtualLeaf.effective location query node)
      .LocalAccess (protections.contains node.tag)

theorem compatible_shape (before after : LocationState) (held : Bool)
    (same : stateShape after=stateShape before)
    (initial : GeneralBorrowExposedConditionalWritePermissions.Compatible before .LocalAccess held) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible after .LocalAccess held := by
  rcases before with ⟨permission,accessed,sifa⟩
  rcases after with ⟨nextPermission,nextAccessed,nextSifa⟩
  simp only [stateShape,Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl⟩
  exact initial

theorem effective_shape (before after : LocationTree) (query : UniIndex) (oldNode newNode : TreeNode)
    (same : locationShape after=locationShape before)
    (defaults : newNode.defaultInitialPermission=oldNode.defaultInitialPermission) :
    stateShape (GeneralBorrowWildcardVirtualLeaf.effective after query newNode)=
      stateShape (GeneralBorrowWildcardVirtualLeaf.effective before query oldNode) := by
  have states : (after.perms.get query).map stateShape=(before.perms.get query).map stateShape := by
    have map_get (nodes : UniValMap LocationState) :
        UniValMap.get ⟨nodes.data.map (Option.map stateShape)⟩ query=(nodes.get query).map stateShape := by
      simp only [UniValMap.get,Array.getElem?_map]
      cases nodes.data[query.toNat]? <;> rfl
    rw [←map_get after.perms,←map_get before.perms]
    exact congrArg (fun values=>UniValMap.get ⟨values⟩ query) same
  cases old : before.perms.get query <;> cases new : after.perms.get query
  · simp [GeneralBorrowWildcardVirtualLeaf.effective,old,new,stateShape,TreeNode.defaultLocationState,defaults]
  · simp only [old,new,Option.map_none,Option.map_some] at states;cases states
  · simp only [old,new,Option.map_none,Option.map_some] at states;cases states
  · simpa only [GeneralBorrowWildcardVirtualLeaf.effective,old,new,Option.getD_some]
      using Option.some.inj (by simpa only [old,new,Option.map_some] using states)

theorem transport (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags) (support : UniIndex→Prop)
    (shape : treeShape after=treeShape before)
    (locations : locationShape newLocation=locationShape oldLocation)
    (initial : Profile before protections support oldLocation) :
    Profile after protections support newLocation := by
  intro query node included present
  obtain ⟨old,found,tag,_,_,defaults⟩ :=
    GeneralBorrowFreshMetadata.node_fields after before shape.symm query node present
  apply compatible_shape _ _ _ (effective_shape oldLocation newLocation query old node locations defaults.symm)
  simpa only [tag] using initial query old included found

/-- Actual ancestor-SIFA weakening preserves writable effective old rows,
including lazy defaults, on success and error paths. No execution-success or
graph well-formedness premise is required for this metadata frame. -/
theorem sifa (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (protections : ProtectedTags) (support : UniIndex→Prop)
    (initial : Every (Profile tree protections support) tree.locations) :
    Every (Profile (sourceUpdateSifa tree start strongest).1 protections support)
      (sourceUpdateSifa tree start strongest).1.locations := by
  let after:=(sourceUpdateSifa tree start strongest).1
  have shape : treeShape after=treeShape tree:=GeneralBorrowSifaView.preserves tree start strongest
  have locations := congrArg (fun value=>value.2.2.1) shape
  change after.locations.entries.map (fun segment=>(segment.range,locationShape segment.data))=
    tree.locations.entries.map (fun segment=>(segment.range,locationShape segment.data)) at locations
  intro position valid
  change position<after.locations.entries.size at valid
  have sizes := congrArg Array.size locations
  simp only [Array.size_map] at sizes
  have previous : position<tree.locations.entries.size := by omega
  have point :=  congrArg (fun values=>values[position]?) locations
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem previous,Option.map_some] at point
  have same : locationShape (after.locations.entries[position]'valid).data=
      locationShape (tree.locations.entries[position]'previous).data := congrArg Prod.snd (Option.some.inj point)
  exact transport tree after _ _ protections support shape same (initial position previous)
end DuplicatePrefix.GeneralBorrowSifaWritableFrame
