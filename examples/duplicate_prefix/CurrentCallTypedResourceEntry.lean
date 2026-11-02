import duplicate_prefix.CurrentCallResourceFnEntry
import duplicate_prefix.CurrentCallTypedSourceOperation
import duplicate_prefix.CurrentCallResourceInstallation

/-! Immediate typed consumption of the generic current borrow witness. Raw
Read/child completion is derived, never a caller validity field. This does not
adopt the candidate as Ordinary or assert a rewritten post-call denotation. -/
namespace DuplicatePrefix.CurrentCallTypedResourceEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- The actual typed interpreter installs the SAME tree/global/frame obtained
from finite issued resources, for concrete or wildcard interior pointers. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat) (len : UInt64)
    (W : UniformWindow before tracker data owner id offset len.toNat .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before W.pointer.value id offset len.toNat)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size < 65536)
    (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295) (race : before.dataRace = none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel : Nat)
    (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before))) :
    ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      before.memory.live.find? (fun row => row.1 == id) = some (id,entry) ∧
      entry.allocation = W.allocation ∧
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame id W.pointer.value.provenance (UInt64.ofNat offset) len = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global borrowFrame id room).1 ∧
      output.frame = (registered tracker.global borrowFrame id room).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child (UInt64.ofNat offset) len) ∧
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base W.pointer.value len ActualReferenceMetadata.reference)
        ActualReferenceMetadata.reference.ty .FnEntry (Storage.withCurrent frames frame before) =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (CurrentCallResourceFnEntry.child_pointer W output.tag child).value len ActualReferenceMetadata.reference))
          (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            (installed before tracker room id entry output.child.tree)) ∧
      (installed before tracker room id entry output.child.tree).borrowTracker = some ⟨output.global,tracker.retagMode⟩ ∧
      (installed before tracker room id entry output.child.tree).memory.live.find? (fun row => row.1 == id) =
        some (id,{entry with allocation := entry.allocation.setExtra output.child.tree}) := by
  obtain ⟨entry,base,sourceLive,cached,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have present : Present (ActualWorld before) id entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive),rfl⟩
  have worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup := by
    simpa [ActualWorld,List.map_map,Function.comp_def] using state.allocationIds
  have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList worldIds id entry.allocation W.allocation present W.present
  have offsetFits : offset < 2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat = offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have bounds : (UInt64.ofNat offset).toNat+len.toNat ≤ W.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,W.issued.capability.treeExtent,←W.issued.capability.extent,←allocationEq]
    exact sourceBounds
  have nonzero : len ≠ 0 := by intro zero;rw [zero] at positive;cases positive
  obtain ⟨output,child,actual,tag,global,callFrame,readDone,childDone,lookup,witness⟩ :=
    CurrentCallResourceFnEntry.correlated_borrow W runtime state highwater borrowFrame room (by simp [demandOf]) distinct short nodeRoom
      (UInt64.ofNat offset) len startEq rfl nonzero bounds
  have sourceBinding : CandidateCallBindings.WindowBinding before W.pointer.value id offset len.toNat :=
    ⟨entry,base,sourceLive,cached,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩
  have actualEntry : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global borrowFrame id W.pointer.value.provenance (UInt64.ofNat offset) len = .ok output := by
    rw [allocationEq]
    exact actual
  obtain ⟨typed,_,_,_,installedTracker,_,sourceInstalled,_,_,_⟩ := CurrentCallTypedSourceOperation.typed_of_operation
    options remaining span ctx before tracker frames frame borrowFrame state.enabled frameBorrow W.pointer.value id offset len entry sourceLive sourceBinding
    positive signedFits room race nullComparator dynamicFuel fuelEq metadata origins output actualEntry readDone childDone
  refine ⟨entry,output,child,sourceLive,allocationEq,actual,tag,global,callFrame,witness,?_,installedTracker,sourceInstalled⟩
  simpa only [CurrentCallResourceFnEntry.child_pointer,changedPointer,tag,Pointer.new] using typed

theorem installed_issuance
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (before : Before) (tracker : MachineHooks.BorrowState)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat) (len : UInt64)
    (W : UniformWindow before tracker data owner id offset len.toNat .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before W.pointer.value id offset len.toNat)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size < 65536)
    (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295) (race : before.dataRace = none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel : Nat)
    (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before))) :
    ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      before.memory.live.find? (fun row => row.1 == id) = some (id,entry) ∧
      entry.allocation = W.allocation ∧
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame id W.pointer.value.provenance (UInt64.ofNat offset) len = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global borrowFrame id room).1 ∧
      output.frame = (registered tracker.global borrowFrame id room).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child (UInt64.ofNat offset) len) ∧
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base W.pointer.value len ActualReferenceMetadata.reference)
        ActualReferenceMetadata.reference.ty .FnEntry (Storage.withCurrent frames frame before) =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (CurrentCallResourceFnEntry.child_pointer W output.tag child).value len ActualReferenceMetadata.reference))
          (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            (installed before tracker room id entry output.child.tree)) ∧
      (installed before tracker room id entry output.child.tree).borrowTracker = some ⟨output.global,tracker.retagMode⟩ ∧
      (installed before tracker room id entry output.child.tree).memory.live.find? (fun row => row.1 == id) =
        some (id,{entry with allocation := entry.allocation.setExtra output.child.tree}) ∧
      SpatialDelegation (installed before tracker room id entry output.child.tree) ⟨output.global,tracker.retagMode⟩ id
        (W.allocation.setExtra output.child.tree) (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child := by
  obtain ⟨entry,output,child,live,allocationEq,actual,tag,global,callFrame,⟨witness⟩,typed,installedTracker,installedLive⟩ :=
    invoke options remaining span ctx before tracker data owner id offset len W runtime state highwater frames frame borrowFrame frameBorrow binding
      positive signedFits room distinct short nodeRoom race nullComparator dynamicFuel fuelEq metadata origins
  let post := installed before tracker room id entry output.child.tree
  let next : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  have present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some installedLive)
    apply List.mem_map.mpr
    refine ⟨(id,{entry with allocation := entry.allocation.setExtra output.child.tree}),member,?_⟩
    simp only [allocationEq]
  have rootTag : next.global.rootTag? id = tracker.global.rootTag? id := by rw [show next.global = output.global from rfl,global];rfl
  have vacant : W.allocation.extra.nodes.get child = none := by
    cases oldAt : W.allocation.extra.nodes.get child with
    | none => rfl
    | some old =>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := witness.oldNodes child old oldAt
      have same : changed = witness.node := Option.some.inj (changedAt.symm.trans witness.nodeAt)
      have oldTag : old.tag = output.tag := changedTag.symm.trans ((congrArg TreeNode.tag same).trans witness.tag)
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global runtime child old oldAt
      rw [oldTag,tag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have parentIssued := CurrentCallResourceInstallation.spatial W.issued W.parents post next output.child.tree present rootTag
    witness.capacity witness.oldRoots witness.oldNodes child W.pointer.grant vacant
  have childIssued : SpatialDelegation post next id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child := by
    have shape := witness.constructor
    cases provenance : W.pointer.value.provenance with
    | concrete supplied tag =>
      rw [provenance] at shape
      obtain ⟨parent,parentAt,_,_⟩ := W.binding
      obtain ⟨current,currentAt,_,_,_,_⟩ := witness.oldNodes W.pointer.grant parent parentAt
      apply SpatialDelegation.concrete parentIssued
      exact .step (.refl W.pointer.grant current currentAt) witness.node witness.nodeAt shape
    | wildcard =>
      rw [provenance] at shape
      obtain ⟨position,root,rootNode,rootSlot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path output.child.tree witness.parents.graph child witness.node witness.nodeAt
      have rootEq : root = child := by
        cases path with
        | refl => rfl
        | @step predecessor target earlier node found edge =>
          have same : node = witness.node := Option.some.inj (found.symm.trans witness.nodeAt)
          rw [same,shape] at edge
          cases edge
      subst root
      have edge := S05ConcreteProtectedChildCompletion.child_edge W.precise.completion child W.pointer.grant
      obtain ⟨earlier,originRoot,newRoot,originNode,before,originSlot,newRootAt,originAt,exposed,older,originPath⟩ :=
        witness.parents.virtual position child rootSlot W.pointer.grant edge
      have same : newRoot = witness.node := Option.some.inj (newRootAt.symm.trans witness.nodeAt)
      exact SpatialDelegation.wildcard originNode newRoot earlier position originRoot parentIssued originAt exposed newRootAt
        (by rw [same];exact shape) older before originSlot rootSlot originPath edge
  exact ⟨entry,output,child,live,allocationEq,actual,tag,global,callFrame,⟨witness⟩,typed,installedTracker,installedLive,childIssued⟩

end
end DuplicatePrefix.CurrentCallTypedResourceEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallTypedResourceEntry.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved typed resource entry dependency {dependency}"
