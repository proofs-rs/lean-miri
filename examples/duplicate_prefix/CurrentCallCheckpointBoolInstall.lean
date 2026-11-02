import duplicate_prefix.CurrentCallCheckpointSharedBoolFrame
namespace DuplicatePrefix.CurrentCallCheckpointBoolInstall
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint GeneralRangeMapOrigins S05CompletedAncestryReadMutable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Install one retained Bool bank in its actual machine row. Bytes and the
original scalar destination stay fixed; no source authority is required. -/
theorem install {before tracker place} (old : Return before tracker place)
    (post : Before) (next : MachineHooks.BorrowState) (tree : BorrowTree) (C : Completion)
    (live : post.memory.live.find? (fun row=>row.1==old.id)=some (old.id,
      {old.physical.entry with allocation:=old.window.allocation.setExtra tree}))
    (addresses : post.user.addresses=before.user.addresses)
    (extras : post.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras)
    (rootTag : next.global.rootTag? old.id=tracker.global.rootTag? old.id)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree next.global)
    (parents : ParentInterpretation tree C)
    (capacity : tree.locations.size=old.window.allocation.extra.locations.size)
    (roots : tree.roots=old.window.allocation.extra.roots)
    (metadata : ∀query previous,old.window.allocation.extra.nodes.get query=some previous→∃changed,
      tree.nodes.get query=some changed ∧changed.tag=previous.tag ∧changed.parent=previous.parent ∧
      changed.isExposed=previous.isExposed ∧changed.defaultInitialPermission=previous.defaultInitialPermission)
    (edges : ∀(query origin : UniIndex),old.window.precise.completion.parents[query.toNat]?=some (some origin)→C.parents[query.toNat]?=some (some origin))
    (owned : OwnedOn (Authority tree C next.global.protectedTags old.window.pointer.grant)
      old.physical.offset (old.physical.offset+1) tree.locations)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size<65536)
    (node : TreeNode) (nodeAt : tree.nodeAt old.window.pointer.grant=some node)
    (nodeTag : node.tag=old.node.tag) (nodeParent : node.parent=old.node.parent)
    (leaf : node.children=#[]) (hidden : node.isExposed=false)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree old.window.pointer.grant .Write old.physical.offset (old.physical.offset+1)) :
    ∃current : Return post next place,current.id=old.id ∧current.offset=old.offset ∧current.window.pointer=old.window.pointer ∧
      current.original=old.original ∧current.window.allocation=old.window.allocation.setExtra tree ∧current.window.precise.completion=C ∧
      current.node.tag=old.node.tag ∧current.node.parent=old.node.parent := by
  have present : Present (ActualWorld post) old.id (old.window.allocation.setExtra tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  obtain ⟨data,Q,pointer,loan,allocation,completion⟩ := CurrentCallCheckpointSharedBoolFrame.install old.window post next tree C present rootTag
    runtime parents capacity (by intro position root found;rw [roots];exact found) metadata edges old.physical.offset old.physicalOffset owned
  have issued := CurrentCallAllocationLicense.spatial old.originalIssued post next (old.window.allocation.setExtra tree) present rootTag
    rfl rfl capacity (by intro position root found;change tree.roots[position]?=some root;rw [roots];exact found) metadata C edges
  have originalBinding : PointerBinds (old.window.allocation.setExtra tree) old.original := by
    obtain ⟨previous,found,_,provenance⟩:=old.originalBinding
    obtain ⟨changed,changedAt,tag,parent,exposure,_⟩:=metadata old.original.grant previous found
    refine ⟨changed,changedAt,runtime.formed.allocator.nodeTags _ _ changedAt,?_⟩
    cases prov : old.original.value.provenance with
    | concrete supplied suppliedTag=>simp only [prov] at provenance ⊢;exact ⟨provenance.1,provenance.2.trans tag.symm⟩
    | wildcard=>simp only [prov] at provenance ⊢;exact exposure.trans provenance
  let physical : CurrentCallBoolScalarWrite.Window post place := {old.physical with
    entry:={old.physical.entry with allocation:=old.physical.entry.allocation.setExtra tree}
    live:=by rw [old.physicalId,old.physicalAllocation];exact live
    cachedBase:=by rw [addresses];exact old.physical.cachedBase}
  have physicalAllocation : physical.entry.allocation=old.window.allocation.setExtra tree:=by
    change old.physical.entry.allocation.setExtra tree=_
    rw [old.physicalAllocation]
  have binding : CandidateCallBindings.WindowBinding post old.physical.pointer old.id old.offset 1 := by
    obtain ⟨entry,base,oldLive,cached,byteLength,room,bounds,address,nonnull,provenance⟩:=old.binding
    have physicalLive:=old.physical.live
    rw [old.physicalId] at physicalLive
    have same : entry=old.physical.entry:=congrArg Prod.snd (Option.some.inj (oldLive.symm.trans physicalLive))
    rw [same,old.physicalAllocation] at byteLength room bounds provenance
    refine ⟨{old.physical.entry with allocation:=old.window.allocation.setExtra tree},base,live,?_,byteLength,room,bounds,address,nonnull,?_⟩
    · rw [addresses];exact cached
    · rw [addresses];exact provenance
  let current : Return post next place := {
    data:=data,owner:=old.owner,id:=old.id,offset:=old.offset,window:=Q,physical:=physical,
    physicalId:=old.physicalId,physicalOffset:=old.physicalOffset,
    physicalAllocation:=physicalAllocation.trans allocation.symm,binding:=binding,
    original:=old.original,originalId:=old.originalId,originalPointer:=old.originalPointer,
    originalIssued:=by rw [allocation,completion];exact issued,
    originalBinding:=by rw [allocation];exact originalBinding,
    edge:=by rw [pointer,completion];exact edges _ _ old.edge,
    runtime:=by rw [allocation];exact runtime,
    distinct:=by rw [allocation];exact distinct,
    short:=by rw [allocation];exact short,
    node:=node,nodeAt:=by rw [allocation,pointer];exact nodeAt,
    leaf:=leaf,hidden:=hidden,activity:=by rw [allocation,pointer];exact activity,
    profile:=CurrentCallBoolProtection.WindowReady.transport old.profile extras}
  exact ⟨current,rfl,rfl,pointer,rfl,allocation,completion,nodeTag,nodeParent⟩
end
end DuplicatePrefix.CurrentCallCheckpointBoolInstall
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointBoolInstall" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Bool installation dependency {dependency}"
