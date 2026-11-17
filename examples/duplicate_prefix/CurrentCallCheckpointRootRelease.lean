import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.CurrentCallSpatialCurrentRelease

namespace DuplicatePrefix.CurrentCallCheckpointRootRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem present_id {world id other allocation}
    (present : Present world id allocation) (same : id=other) : Present world other allocation:=same ▸present

private theorem window_owned {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode) (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (lo hi : UInt64) (lower : offset≤lo.toNat) (upper : hi.toNat≤offset+length) :
    GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion
      tracker.global.protectedTags W.pointer.grant) lo hi W.allocation.extra.locations:=by
  intro position valid positive beforeUpper afterLower
  have segment:=(GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
  have member : W.allocation.extra.locations.entries[position]∈W.allocation.extra.locations.entries.toList:=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  by_cases earlier : lo.toNat≤W.allocation.extra.locations.entries[position].range.start.toNat
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,W.allocation.extra.locations.entries[position].range.start.toNat)
      ⟨rfl,by omega,by omega⟩ _ member (Nat.le_refl _) segment (runtime.formed.profile position valid) (runtime.possible position valid)
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,lo.toNat) ⟨rfl,lower,by omega⟩ _ member (by omega) afterLower
      (runtime.formed.profile position valid) (runtime.possible position valid)

private theorem bounds {before tracker ctx mode offset length} (role : RoleCover before tracker ctx mode offset length)
    (positive : 0<length) : offset+length≤role.backing.allocation.extra.locations.size.bytes.toNat:=by
  let byte:=(role.backing.id,offset+length-1)
  have hit : Window role.backing.id offset length byte:=⟨rfl,by dsimp only [byte];omega,by dsimp only [byte];omega⟩
  obtain ⟨i,inside⟩:=role.covered byte hit
  have bound:=((role.roles i ⟨byte,hit,inside⟩).available byte hit inside).1
  have cap:=(role.roles i ⟨byte,hit,inside⟩).issued.capability
  rw [cap.treeExtent,←cap.extent]
  dsimp only [byte] at bound
  omega

/-- Current positive source cells and a scalar return packet derive the
same two actual release passes, independently of the current body location. -/
theorem of_resources {machine tracker ctx offset len place}
    (Q : RoleCover machine tracker ctx .mut offset len.toNat) (target : Return machine tracker place)
    (identifiers : (machine.memory.live.toList.map Prod.fst).Nodup)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.backing.allocation.extra tracker.global)
    (distinct : Q.backing.allocation.extra.roots.toList.Nodup) (short : Q.backing.allocation.extra.nodes.size<65536)
    (nonempty : 0<len.toNat) (anchor : UniIndex) (node : TreeNode)
    (concreteSource : Q.family.value.provenance=.concrete Q.backing.id node.tag)
    (nodeAt : Q.backing.allocation.extra.nodes.get anchor=some node) (hidden : node.isExposed=false)
    (tags : node.tag≠target.node.tag)
    (absent : target.id≠Q.backing.id→∀index other,target.window.allocation.extra.nodes.get index=some other→other.tag≠node.tag)
    (frame : FrameState) (ownedFrame : frame.protectedTags=#[(Q.backing.id,node.tag),(target.id,target.node.tag)])
    (disjoint : target.id=Q.backing.id→∀byte,Window Q.backing.id offset len.toNat byte→Window target.id target.offset 1 byte→False)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin Q.backing.allocation.extra anchor .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len))
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : machine.memory.live.find? (fun row=>row.1==Q.backing.id)=some (Q.backing.id,sourceEntry))
    (sourceAllocation : sourceEntry.allocation=Q.backing.allocation) :
    Nonempty (CurrentCallResourceCurrentRelease.Released target.window frame target.original.grant target.physical.offset target.physical.entry):=by
  let B:=target.window
  have sameAllocation : target.id=Q.backing.id →B.allocation=Q.backing.allocation:=by
    intro same
    have ids : ((ActualWorld machine).toList.map Prod.fst).Nodup:=by
      simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using identifiers
    have present:=present_id B.present same
    exact CandidateCurrentUniformOwnerWindow.same_id _ ids _ _ _ present Q.backing.live
  have concrete : ∃id tag,B.pointer.value.provenance=.concrete id tag:=by
    obtain ⟨node,nodeAt,_,binding⟩:=B.binding
    have equal : node=target.node:=Option.some.inj (nodeAt.symm.trans target.nodeAt)
    subst node
    cases provenance : B.pointer.value.provenance with
    | concrete id tag => exact ⟨id,tag,rfl⟩
    | wildcard => simp only [provenance] at binding;rw [target.hidden] at binding;cases binding
  have extent:=bounds Q nonempty
  have offsetFit : offset<2^64:=by have small:=Q.backing.allocation.extra.locations.size.bytes.toNat_lt;omega
  have startEq : (UInt64.ofNat offset).toNat=offset:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFit]
  have noWrap : (UInt64.ofNat offset+len).toNat=(UInt64.ofNat offset).toNat+len.toNat:=by
    have small:=Q.backing.allocation.extra.locations.size.bytes.toNat_lt
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have positive : (UInt64.ofNat offset).toNat<(UInt64.ofNat offset+len).toNat:=by
    rw [noWrap];have positive:=nonempty;omega
  have boolNoWrap : (target.physical.offset+1).toNat=target.physical.offset.toNat+1:=by
    have bound:=target.physical.bounds
    have small:=target.physical.capacity.toNat_lt
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega : target.physical.offset.toNat+1<2^64)]
  have separate : target.id=Q.backing.id →(UInt64.ofNat offset+len).toNat≤target.physical.offset.toNat ∨
      (target.physical.offset+1).toNat≤(UInt64.ofNat offset).toNat:=by
    intro same
    apply Classical.byContradiction
    intro overlap
    rw [noWrap,startEq,boolNoWrap] at overlap
    exact disjoint same (Q.backing.id,target.physical.offset.toNat)
      ⟨rfl,by omega,by omega⟩ ⟨same.symm,by rw [←target.physicalOffset];omega,by rw [←target.physicalOffset];omega⟩
  exact CurrentCallSpatialCurrentRelease.release Q B sameAllocation runtime target.runtime
    distinct target.distinct short target.short concrete
    anchor node target.node
    concreteSource nodeAt target.nodeAt
    hidden target.hidden target.leaf
    tags
    absent
    frame ownedFrame
    target.original.grant target.edge (UInt64.ofNat offset) len target.physical.offset
    startEq rfl target.physicalOffset positive (by rw [boolNoWrap];omega) noWrap boolNoWrap separate
    activity target.activity
    (window_owned B rfl target.runtime target.physical.offset (target.physical.offset+1)
      (by rw [target.physicalOffset];exact Nat.le_refl _) (by rw [boolNoWrap,target.physicalOffset];exact Nat.le_refl _))
    sourceEntry target.physical.entry sourceLive
    (by simpa only [target.physicalId] using target.physical.live)
    sourceAllocation target.physicalAllocation


/-- The installed checkpoint is the first instance of the same resource-only
release consumer used at later body returns. -/
theorem release {options remaining span len count place}
    (checkpoint : Checkpoint options remaining span len count place) :
    Nonempty (CurrentCallResourceCurrentRelease.Released checkpoint.output.window checkpoint.borrowFrame
      checkpoint.output.original.grant checkpoint.output.physical.offset checkpoint.output.physical.entry):=by
  exact of_resources checkpoint.source.role checkpoint.output checkpoint.ids checkpoint.source.runtime checkpoint.source.distinct
    (by have margin:=checkpoint.source.nodes;omega) checkpoint.source.positive checkpoint.source.grant checkpoint.source.node
    (by rw [checkpoint.source.nodeTag];exact checkpoint.source.concrete) checkpoint.source.nodeAt checkpoint.source.hidden
    (by rw [checkpoint.source.nodeTag];exact checkpoint.sourceBoolTags)
    (by intro different index node found;rw [checkpoint.source.nodeTag];exact checkpoint.sourceTagAbsentBool different index node found)
    checkpoint.borrowFrame (by rw [checkpoint.source.nodeTag];exact checkpoint.protectors) checkpoint.separate checkpoint.source.activity
    checkpoint.sourceEntry checkpoint.sourceLive checkpoint.sourceAllocation

end
end DuplicatePrefix.CurrentCallCheckpointRootRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointRootRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common root release dependency {dependency}"
