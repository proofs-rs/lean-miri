import duplicate_prefix.CurrentCallSpatialCurrentRelease
import duplicate_prefix.CurrentCallSpatialEntryCurrent
import duplicate_prefix.CurrentCallSpatialEntryTagSeparation

namespace DuplicatePrefix.CurrentCallSpatialEntryRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
open CurrentCallSpatialEntry
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {limits count} (out : Output C limits count)

def borrowFrame : FrameState := (C.borrowFrame.addProtector source.backing.id tracker.global.nextPointerTag).addProtector
  out.physical.id (sourceOutput C).global.nextPointerTag

private theorem role_bounds {before tracker ctx mode offset length} (Q : RoleCover before tracker ctx mode offset length)
    (positive : 0<length) : offset+length≤Q.backing.allocation.extra.locations.size.bytes.toNat := by
  have last : Window Q.backing.id offset length (Q.backing.id,offset+length-1):=⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩:=Q.covered _ last
  let active : CurrentCallSpatialSourceCover.Active Q i:=⟨_,last,cell⟩
  have bound:=((Q.roles i active).available _ last cell).1
  have cap:=(Q.roles i active).issued.capability
  rw [cap.treeExtent,←cap.extent]
  omega

/-- The actual current q/B resources derive BOTH sequential releases. The
source callback is spatial; Bool uses only its own scalar completion. -/
theorem release (empty : C.borrowFrame={}) :
    ∃data owner,∃B : UniformWindow (CurrentCallSpatialEntryCurrent.machine out) (CurrentCallSpatialEntryCurrent.held out)
      data owner out.physical.id out.physical.offset.toNat 1 .ret,
      B.pointer=CurrentCallSpatialEntryBoolCurrent.pointer out ∧B.allocation=out.updated ∧
      B.precise.completion=CurrentCallSpatialEntryBoolCurrent.completion out ∧
      Nonempty (CurrentCallResourceCurrentRelease.Released B (borrowFrame out)
        (CurrentCallSpatialEntryBoolCurrent.parent out).pointer.grant out.physical.offset {out.physical.entry with allocation:=out.updated}) := by
  let Q:=CurrentCallSpatialEntryCurrent.role out
  obtain ⟨data,owner,B,bPointer,bAllocation,bCompletion⟩:=CurrentCallSpatialEntryBoolCurrent.current out
  obtain ⟨qNode,qAt,qTag,qLeaf,qHidden,qActivity⟩:=CurrentCallSpatialEntryCurrent.node out
  let bNode:=CurrentCallSpatialEntryBoolCurrent.node out
  have bAt : B.allocation.extra.nodes.get B.pointer.grant=some bNode:=by
    rw [bAllocation,bPointer]
    exact CurrentCallSpatialEntryBoolCurrent.nodeAt out
  have bTag : bNode.tag=out.boolOutput.tag:=CurrentCallSpatialEntryBoolCurrent.nodeTag out
  have bFacets:=CurrentCallSpatialEntryBoolCurrent.facets out
  have sameAllocation : out.physical.id=Q.backing.id→B.allocation=Q.backing.allocation := by
    intro same
    rw [bAllocation]
    change out.updated=CurrentCallSpatialEntryCurrent.allocation out
    have joint : out.src.backing.id=out.dst.backing.id:=same.symm.trans out.physicalId
    simp only [CurrentCallSpatialEntryCurrent.allocation,ite_eq_left joint]
  have qConcrete : Q.family.value.provenance=.concrete Q.backing.id qNode.tag:=by
    change out.src.family.value.provenance=.concrete out.src.backing.id qNode.tag
    rw [CurrentCallSpatialEntryCurrent.source_id,qTag]
    exact CurrentCallSpatialEntryCurrent.concrete out
  have bConcrete : ∃id tag,B.pointer.value.provenance=.concrete id tag:=by rw [bPointer];exact ⟨_,_,rfl⟩
  have tags : qNode.tag≠bNode.tag:=by rw [qTag,bTag];exact CurrentCallSpatialEntryTagSeparation.tags out
  have absent : out.physical.id≠Q.backing.id→∀index node,B.allocation.extra.nodes.get index=some node→node.tag≠qNode.tag:=by
    intro different index node present
    have diff : out.physical.id≠source.backing.id:=by
      simpa only [Q,CurrentCallSpatialEntryCurrent.role,CurrentCallSpatialSourceCover.assemble,CurrentCallSpatialSourceCover.backing,
        CurrentCallSpatialEntryCurrent.source_id] using different
    rw [bAllocation] at present
    simpa only [qTag] using CurrentCallSpatialEntryTagSeparation.absent out diff index node present
  have frame : (borrowFrame out).protectedTags=#[(Q.backing.id,qNode.tag),(out.physical.id,bNode.tag)] := by
    change (borrowFrame out).protectedTags=#[(out.src.backing.id,qNode.tag),(out.physical.id,bNode.tag)]
    rw [CurrentCallSpatialEntryCurrent.source_id,qTag,bTag,out.boolTag]
    simp only [borrowFrame,empty,FrameState.addProtector]
    rfl
  have sourceBounds:=role_bounds Q C.positive
  have offsetFit : offset<2^64:=by have size:=UInt64.toNat_lt Q.backing.allocation.extra.locations.size.bytes;omega
  have startEq : (UInt64.ofNat offset).toNat=offset:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFit]
  have noWrap : ((UInt64.ofNat offset)+len).toNat=(UInt64.ofNat offset).toNat+len.toNat := by
    have size:=UInt64.toNat_lt Q.backing.allocation.extra.locations.size.bytes
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have positive : (UInt64.ofNat offset).toNat<((UInt64.ofNat offset)+len).toNat:=by rw [noWrap];have p:=C.positive;omega
  have boolBounds:=CurrentCallSpatialEntryBoolCurrent.window out (out.physical.id,out.physical.offset.toNat) ⟨rfl,by omega,by omega⟩
  have boolEnd : (out.physical.offset+1).toNat=out.physical.offset.toNat+1 := by
    have fit : out.physical.offset.toNat+1<2^64:=Nat.lt_of_le_of_lt out.physical.bounds out.physical.capacity.toNat_lt
    rw [UInt64.toNat_add]
    change (out.physical.offset.toNat+1)%2^64=out.physical.offset.toNat+1
    exact Nat.mod_eq_of_lt fit
  have boolPositive : out.physical.offset.toNat<(out.physical.offset+1).toNat:=by rw [boolEnd];omega
  have disjoint : out.physical.id=Q.backing.id→((UInt64.ofNat offset)+len).toNat≤out.physical.offset.toNat ∨
      (out.physical.offset+1).toNat≤(UInt64.ofNat offset).toNat := by
    intro same
    have sameId : source.backing.id=ret.backing.id:=by
      have sid:=CurrentCallSpatialEntryCurrent.source_id out
      have bid:=CurrentCallSpatialEntryBoolCurrent.physical_id out
      change out.physical.id=out.src.backing.id at same
      exact sid.symm.trans (same.symm.trans bid)
    apply Classical.byContradiction
    intro overlap
    have lo : offset<out.physical.offset.toNat+1:=by rw [startEq,boolEnd] at overlap;omega
    have hi : out.physical.offset.toNat<offset+len.toNat:=by rw [startEq,noWrap] at overlap;omega
    have hit : Window source.backing.id offset len.toNat (source.backing.id,out.physical.offset.toNat):=⟨rfl,by omega,by omega⟩
    have bHit : Window ret.backing.id returnOffset 1 (source.backing.id,out.physical.offset.toNat):=⟨sameId,by rw [out.physicalOffset];omega,by rw [out.physicalOffset];omega⟩
    exact C.separate _ hit bHit
  obtain ⟨released⟩:=CurrentCallSpatialCurrentRelease.release Q B sameAllocation
    (CurrentCallSpatialEntryCurrent.runtime out) (by rw [bAllocation];exact out.updatedRuntime) (CurrentCallSpatialEntryCurrent.distinct out)
    (by rw [bAllocation];exact CurrentCallSpatialEntryBoolCurrent.roots out) (CurrentCallSpatialEntryCurrent.short out)
    (by rw [bAllocation];exact CurrentCallSpatialEntryBoolCurrent.short out) bConcrete out.child qNode bNode qConcrete qAt bAt
    qHidden bFacets.2.1 bFacets.1 tags absent (borrowFrame out) frame
    (CurrentCallSpatialEntryBoolCurrent.parent out).pointer.grant
    (by rw [bPointer,bCompletion];exact CurrentCallSpatialEntryBoolCurrent.edge out)
    (UInt64.ofNat offset) len out.physical.offset startEq rfl rfl positive boolPositive noWrap boolEnd disjoint
    qActivity (by rw [bAllocation,bPointer];exact bFacets.2.2)
    (by rw [bAllocation,bPointer,bCompletion];exact out.updatedOwned)
    (CurrentCallSpatialEntryCurrent.sourceEntry out) {out.physical.entry with allocation:=out.updated}
    (CurrentCallSpatialEntryCurrent.live out) (CurrentCallSpatialEntryBoolCurrent.live out)
    (CurrentCallSpatialEntryCurrent.entry_allocation out) (by rw [bAllocation])
  exact ⟨data,owner,B,bPointer,bAllocation,bCompletion,⟨released⟩⟩

end
end DuplicatePrefix.CurrentCallSpatialEntryRelease

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialEntryRelease.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial count-zero support dependency {dependency}"
