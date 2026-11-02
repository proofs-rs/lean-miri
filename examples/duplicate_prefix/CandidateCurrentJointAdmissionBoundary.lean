import duplicate_prefix.CandidateCurrentJointRawReplacement
import duplicate_prefix.CandidateCurrentJointPacket

/-! Same-call static admission independence. The second packet changes ONLY raw
location permissions. Both packets satisfy the listed bindings, normalization,
precise joint contents and family dataflow. The second fails initial observation
and source raw Write rights. It is not claimed reachable, ordinary, coherent,
or a counterexample to the function Result or to an adopted ownership meaning. -/
namespace DuplicatePrefix.CandidateCurrentJointAdmissionBoundary
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentJointRawReplacement
open S05ZeroCellTypedGeneratedPrefix (ix tag)
open S05ZeroCellJointPacket
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-- All other source-row metadata is retained; the source's own grant is revoked. -/
def revokedLocation : LocationTree :=
  {CandidateCurrentJointPacket.sourceLocation with perms :=
    CandidateCurrentJointPacket.sourceLocation.perms.insert (ix 5) ⟨.Disabled,true,.Read⟩}
def revokedLocations : DedupRangeMap LocationTree := ⟨#[⟨⟨0,2⟩,revokedLocation⟩]⟩
def locations (id : AllocId) (allocation : Allocation Provenance BorrowTree) : DedupRangeMap LocationTree :=
  if id = sourceId then revokedLocations else allocation.extra.locations

def revokedAllocation := replaceAllocation sourceAllocation revokedLocations
noncomputable def revokedBefore := replaceBefore before locations

theorem actual_bindings : ActualBindings revokedBefore argument 2 place {}
    CandidateCurrentJointPacket.call CandidateCurrentJointPacket.identities :=
  CandidateCurrentJointRawReplacement.actual_bindings _ _ _ _ _ _ _ _ CandidateCurrentJointPacket.actual_bindings

theorem precise_joint : PreciseJoint (ActualWorld revokedBefore) {}
    CandidateCurrentJointPacket.interpretation := by
  rw [show ActualWorld revokedBefore = replaceWorld (ActualWorld before) locations from actual_world before locations]
  exact CandidateCurrentJointRawReplacement.precise_joint _ _ _ _ CandidateCurrentJointPacket.precise_joint

private theorem live_entries : revokedBefore.memory.live =
    #[(sourceId,{sourceEntry with allocation := revokedAllocation}),(destinationId,destinationEntry)] := by
  simp only [revokedBefore,replaceBefore,S05ZeroCellJointPacket.live_entries,Array.map]
  simp [locations,revokedAllocation,replaceAllocation,sourceEntry,destinationEntry,
    Ne.symm S05ZeroCellJointPacket.distinct_ids,Allocation.mapExtra]

theorem world : ActualWorld revokedBefore =
    #[(sourceId,revokedAllocation),(destinationId,destinationAllocation)] := by
  unfold ActualWorld
  rw [live_entries]
  cbv

/-- Cached address normalization is preserved, including the actual unchanged
source/return bits. The replacement changes no physical storage field. -/
theorem normalized_windows : NormalizedWindows revokedBefore argument 2 place
    CandidateCurrentJointPacket.call CandidateCurrentJointPacket.identities := by
  constructor
  · right
    refine ⟨by decide,sourcePointer,rfl,⟨0,none,0⟩,
      CandidateCurrentJointPacket.pointers[0]'(by decide),rfl,rfl,rfl,rfl,?_⟩
    refine ⟨{sourceEntry with allocation := revokedAllocation},4096,?_,source_cached,rfl,
      by decide,by decide,rfl,by decide,rfl⟩
    rw [live_entries]
    rfl
  · refine ⟨rfl,destinationPointer,rfl,⟨1,none,0⟩,
      CandidateCurrentJointPacket.pointers[1]'(by decide),rfl,rfl,rfl,rfl,?_⟩
    refine ⟨destinationEntry,8192,?_,destination_cached,rfl,by decide,by decide,rfl,by decide,rfl⟩
    rw [live_entries]
    rfl

/-- All storage/provenance/initialization facts survive metadata replacement. -/
theorem physical : OrdinaryPhysicalValidity.MutU8Slice revokedAllocation 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination destinationAllocation 0 := by
  have source := CandidateCurrentJointPacket.physical.1
  exact ⟨⟨⟨source.storage.byteLength,source.storage.maskLength,source.storage.maskCapacity,
    source.storage.provenance⟩,source.nonempty,source.signedSize,source.contained,
    source.writable,source.values⟩,CandidateCurrentJointPacket.physical.2⟩

/-- Origin identity, exposure, physical ancestry and allocation storage are
identical. The tracker/address state is also literally retained. -/
theorem unchanged : revokedAllocation.extra.nodes = sourceAllocation.extra.nodes ∧
    revokedAllocation.extra.roots = sourceAllocation.extra.roots ∧
    revokedAllocation.extra.tagMapping = sourceAllocation.extra.tagMapping ∧
    revokedAllocation.getBytesUnchecked = sourceAllocation.getBytesUnchecked ∧
    revokedAllocation.provenanceMap = sourceAllocation.provenanceMap ∧
    revokedAllocation.initializationMask = sourceAllocation.initializationMask ∧
    revokedBefore.borrowTracker = before.borrowTracker ∧
    revokedBefore.user.addresses = before.user.addresses := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem source_node : revokedAllocation.extra.nodes.get (ix 5) =
    some CandidateCurrentJointPacketGraph.w := by
  change sourceAllocation.extra.nodes.get (ix 5) = some _
  rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph]
  rfl

private theorem denied : ¬ Allows (RawState revokedLocation (ix 5) CandidateCurrentJointPacketGraph.w)
    false .Write .LocalAccess := by
  intro rights
  exact rights.2.1 (by cbv)

theorem no_initial_observation : ¬ InitialObservation (ActualWorld revokedBefore) {}
    CandidateCurrentJointPacket.interpretation := by
  intro observation
  have preciseRight : Allows (PreciseState CandidateCurrentJointPacket.sourcePrecise 0 (ix 5))
      false .Write .LocalAccess := by
    unfold Allows GeneralBorrowExposedConditionalWritePermissions.Compatible
    decide +kernel
  exact denied (observation sourceId revokedAllocation CandidateCurrentJointPacket.sourcePrecise
    (by simp [Present,world]) (by simp [CandidateCurrentJointPacket.interpretation]) 0 (by decide)
    ⟨⟨0,2⟩,revokedLocation⟩ (by simp [revokedAllocation,replaceAllocation,revokedLocations,Allocation.mapExtra])
    (by decide) (by decide) (ix 5) CandidateCurrentJointPacketGraph.w source_node .Write .LocalAccess preciseRight)

theorem no_source_raw : ¬ RawRights revokedAllocation {} CandidateCurrentJointPacket.sourcePrecise
    ⟨sourceId,sourcePointer,ix 5⟩ 0 .mut := by
  intro rights
  exact denied ((rights ⟨⟨0,2⟩,revokedLocation⟩
    (by simp [revokedAllocation,replaceAllocation,revokedLocations,Allocation.mapExtra])
    (by decide) (by decide) (ix 5) CandidateCurrentJointPacketGraph.w source_node).1 (.refl _))

/-- This conjunction is inhabited even with precise active source/return contents,
fixed current copies and exact argument/Bool-place/address bindings. A further
justified representation denotation is needed to derive raw authority. -/
theorem boundary : ActualBindings revokedBefore argument 2 place {} CandidateCurrentJointPacket.call
      CandidateCurrentJointPacket.identities ∧
    NormalizedWindows revokedBefore argument 2 place CandidateCurrentJointPacket.call CandidateCurrentJointPacket.identities ∧
    PreciseJoint (ActualWorld revokedBefore) {} CandidateCurrentJointPacket.interpretation ∧
    Claims CandidateCurrentJointPacket.interpretation CandidateCurrentJointPacket.call ∧
    CandidateCurrentJointPacket.FamilyDataflow ∧
    OrdinaryPhysicalValidity.MutU8Slice revokedAllocation 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination destinationAllocation 0 ∧
    ¬ InitialObservation (ActualWorld revokedBefore) {} CandidateCurrentJointPacket.interpretation ∧
    ¬ RawRights revokedAllocation {} CandidateCurrentJointPacket.sourcePrecise
      ⟨sourceId,sourcePointer,ix 5⟩ 0 .mut :=
  ⟨actual_bindings,normalized_windows,precise_joint,CandidateCurrentJointPacket.claims,
    CandidateCurrentJointPacket.family_dataflow,physical.1,physical.2,no_initial_observation,no_source_raw⟩

end DuplicatePrefix.CandidateCurrentJointAdmissionBoundary

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentJointAdmissionBoundary." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved admission-boundary dependency {dependency}"
