import duplicate_prefix.CurrentCallSpatialEntryBoolCurrent
namespace DuplicatePrefix.CurrentCallSpatialEntryTagSeparation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallSpatialEntry CurrentCallSpatialEntryBoolCurrent
open GeneralBorrowFnEntryRegistration CurrentCallSpatialJointInstall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {limits count} (out : Output C limits count)

theorem tags : (sourceOutput C).tag≠out.boolOutput.tag := by
  have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag C.fresh
  intro equal
  have values:=congrArg (fun tag : BorTag=>tag.value.toNat) (equal.trans out.boolTag)
  change tracker.global.nextPointerTag.value.toNat=(TypedRetagEmpty.successorTag tracker.global.nextPointerTag C.fresh).value.toNat at values
  omega

/-- In a different Bool allocation every old key predates the actual source
fresh tag. The only new key is the distinct actual Bool tag. -/
theorem absent (different : out.physical.id≠source.backing.id) (index : UniIndex) (node : TreeNode)
    (present : out.updated.extra.nodes.get index=some node) : node.tag≠(sourceOutput C).tag := by
  let B:=parent out
  have other : ret.backing.id≠source.backing.id := by rw [←physical_id out];exact different
  let joint:=CurrentCallSpatialJointInstall.context source C.positive C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry out.allocation out.child out.models
  have coverEq:=joint.same_backing out.dst.backingAt
    (CurrentCallSpatialJointInstall.other_member source C.positive C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry out.allocation out.child out.models ret.backing ret.backingAt other)
    (out.physicalId.symm.trans (physical_id out))
  have treeEq : B.allocation.extra=ret.backing.allocation.extra := by change out.dst.backing.allocation.extra=_;rw [coverEq];rfl
  have oldRuntime:=(spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.old_runtime") out
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first:=(B.window (out.physical.id,out.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent];omega
  have short : B.allocation.extra.nodes.size<65536 := by have h:=oldRuntime.2.2;change B.allocation.extra.nodes.size+1<65536 at h;omega
  have room : B.allocation.extra.nodes.size+1≤4294967295 := by omega
  have keys:=CurrentCallResourceSourceKeyOrigin.operation B oldRuntime.1 out.sourceTracked
    ((spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.source_highwater") out) (sourceOutput C).frame out.fresh rfl oldRuntime.2.1 short room
    out.physical.offset 1 rfl rfl (by decide) bounds out.boolOutput out.boolActual
  have mapped:=out.updatedRuntime.formed.allocator.nodeTags index node present
  rw [(spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.write_tags") out] at mapped
  obtain ⟨slot,member⟩:=(spatial_install_rule ".CurrentCallResourceSourceKeyOrigin.lookup_member") _ node.tag index mapped
  rcases keys node.tag slot member with fresh | ⟨old,oldMember⟩
  · intro same;exact tags out (same.symm.trans (fresh.trans out.boolTag.symm))
  · rw [treeEq] at oldMember
    have initial:=ret.backing.live
    simp only [Present,ActualWorld,Array.toList_map] at initial
    obtain ⟨row,rowMem,rowEq⟩:=List.mem_map.mp initial
    have allocationEq:row.2.allocation=ret.backing.allocation:=(Prod.mk.inj rowEq).2
    have below:=C.highwater row rowMem
    rw [allocationEq] at below
    have older:=below.mapping (node.tag,old) oldMember
    intro same
    rw [same] at older
    change tracker.global.nextPointerTag.value.toNat<tracker.global.nextPointerTag.value.toNat at older
    omega
end
end DuplicatePrefix.CurrentCallSpatialEntryTagSeparation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialEntryTagSeparation" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial entry tag separation dependency {dependency}"
