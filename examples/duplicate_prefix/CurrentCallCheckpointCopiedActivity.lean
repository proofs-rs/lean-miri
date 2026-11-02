import duplicate_prefix.CurrentCallCheckpointCopyAccess
import duplicate_prefix.CurrentCallCheckpointMutableParents
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
namespace DuplicatePrefix.CurrentCallCheckpointCopiedActivity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
noncomputable section
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (data : CurrentCallCheckpointAsMutSource.Data out done seed returned)
  (access : CurrentCallCheckpointCopyAccess.Access out done seed returned data)
  (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)

include data access in
theorem activity (within : count≤len/2) :
    GeneralBorrowFreshActiveWithin.ActiveWithin copied.allocation.extra cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) := by
  obtain ⟨pIndex,sIndex,pNode,qNode,sNode,sLookup,sAt,sTag,sParent,pAt,pTag,pParent,qAt,qTag,qHidden,qActive⟩:=CurrentCallCheckpointMutableParents.s_frame cp out.result out.source
  obtain ⟨helper,helperNode,helperLookup,helperAt,helperTag,helperHidden,helperActive,_⟩:=CurrentCallCheckpointMutableCurrent.facets cp out.result out.source
  have outputEq:=CurrentCallCheckpointAsMutControl.helper_output out done seed
  rw [←outputEq] at sLookup sAt sTag pAt qAt qActive helperLookup helperAt helperTag helperActive
  have releasedActive:=GeneralBorrowActiveWithinRelease.release seed.output.child.tree seed.output.global.protectedTags seed.output.tag helper cp.source.grant
    helperNode helperLookup helperAt helperHidden (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) helperActive qActive
  have cert:=CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (CurrentCallCheckpointAsMutRelease.present out done seed)
  rw [←outputEq] at cert
  have childCapacity : (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.locations.size=
      (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.extra.locations.size:=
    (CurrentCallCheckpointMutable.s_operation cp out.result out.source).2.2.2.2.1
  rw [←outputEq] at childCapacity
  have fullBound : (UInt64.ofNat cp.offset).toNat+len.toNat≤(CurrentCallCheckpointAsMutReturn.releasedTree seed).locations.size.bytes.toNat:=by
    change _≤(seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.locations.size.bytes.toNat
    rw [cert.2.2.2,childCapacity]
    exact (CurrentCallCheckpointMutable.prepared cp out.result out.source).bounds
  have endEq : ((UInt64.ofNat cp.offset)+len).toNat=(UInt64.ofNat cp.offset).toNat+len.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt fullBound (UInt64.toNat_lt _))]
  have numeric:=UInt64.le_iff_toNat_le.mp within
  rw [UInt64.toNat_div] at numeric
  change count.toNat≤len.toNat/2 at numeric
  have middle : ((UInt64.ofNat cp.offset)+count).toNat=(UInt64.ofNat cp.offset).toNat+count.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by have bound:=Nat.lt_of_le_of_lt fullBound (UInt64.toNat_lt _);omega)]
  have copyTree : (CurrentCallCheckpointCopyPrefix.allocation out done seed).extra=CurrentCallCheckpointAsMutReturn.releasedTree seed:=by
    have actual:=congrArg Allocation.extra data.allocation
    exact actual.symm.trans (CurrentCallCheckpointAsMutSourceMetadata.tree out done seed returned data)
  have readActive : GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len):=by
    change GeneralBorrowFreshActiveWithin.ActiveWithin ((CurrentCallCheckpointCopyPrefix.allocation out done seed).extra.performNormalAccessRange seed.output.tag (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes count) .Read (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags .VisitChildrenOfAccessed).tree cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len)
    rw [copyTree]
    exact GeneralBorrowFreshActiveWithinAccess.normal (CurrentCallCheckpointAsMutReturn.releasedTree seed) seed.output.tag (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes count) .Read
      (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags .VisitChildrenOfAccessed cp.source.grant (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len)
      (CurrentCallCheckpointAsMutSource.runtime out done seed).formed.well (by change (UInt64.ofNat cp.offset).toNat+count.toNat≤_;omega) (Nat.le_refl _) (by change (UInt64.ofNat cp.offset+count).toNat≤_;rw [middle,endEq];omega) releasedActive
  have readCapacity : (CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree.locations.size=(CurrentCallCheckpointAsMutReturn.releasedTree seed).locations.size:=by
    have capacity:=access.read.capacity
    rw [CurrentCallCheckpointCopyAccess.read_eq out done seed returned data,CurrentCallCheckpointAsMutSourceMetadata.tree out done seed returned data] at capacity
    exact capacity
  have readWell : (CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree.locations.WellFormed:=by
    have treeEq:=CurrentCallSpatialSubrangeSequence.ReadStage.tree access.read
    rw [CurrentCallCheckpointCopyAccess.read_eq out done seed returned data] at treeEq
    have well:=access.read.runtime.formed.well
    rw [treeEq] at well
    exact well
  have writeEnd : ((UInt64.ofNat cp.offset)+count+count).toNat≤((UInt64.ofNat cp.offset)+len).toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by have bound:=Nat.lt_of_le_of_lt fullBound (UInt64.toNat_lt _);omega),middle,endEq]
    omega
  have finalActive:=GeneralBorrowFreshActiveWithinAccess.normal (CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree seed.output.tag (Size.ofBytes ((UInt64.ofNat cp.offset)+count)) (Size.ofBytes count) .Write
    (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags .VisitChildrenOfAccessed cp.source.grant (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len)
    readWell (by change (UInt64.ofNat cp.offset+count).toNat+count.toNat≤_;rw [readCapacity,middle];omega) (by change (UInt64.ofNat cp.offset).toNat≤(UInt64.ofNat cp.offset+count).toNat;rw [middle];omega) writeEnd readActive
  rw [copied.tree]
  exact finalActive
end
end DuplicatePrefix.CurrentCallCheckpointCopiedActivity
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopiedActivity" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved copied activity dependency {dependency}"
