import duplicate_prefix.CandidateCurrentJointPacketGraph
import duplicate_prefix.CandidateCallBindings

/-! Closed admission test of the THREE SEPARATE candidate layers for the
accepted SIX-node call-time packet. No Ordinary/ValidInput adoption, arbitrary
representation admission, preservation or whole-call safety follows. -/
namespace DuplicatePrefix.CandidateCurrentJointPacket
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall
open S05ZeroCellTypedGeneratedPrefix (ix tag)
open S05ZeroCellJointPacket
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 2000000
set_option linter.unusedSimpArgs false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

abbrev sourcePrecise := CandidateCurrentJointPacketGraph.precise
def returnPrecise : PreciseAllocation :=
  ⟨⟨#[none],#[0]⟩,#[#[⟨.Unique,true,.None⟩]]⟩

def call : CallLoans := ⟨0,1,sourceId,0,2,destinationId,0⟩

/-- Only the source W and Bool place own active contents. D remains a raw
instance without content ownership; A/B ghost attachments share instance2. -/
noncomputable def pointers : Array PointerInstance :=
  #[⟨sourceId,sourcePointer,ix 5⟩,⟨destinationId,destinationPointer,ix 0⟩,
    ⟨sourceId,S05ZeroCellJointCertificate.wildcardFamily,ix 0⟩,
    ⟨sourceId,S05ZeroCellJointCertificate.savedRawD,ix 2⟩]

local instance windowDecidable (id : AllocId) (offset length : Nat)
    (byte : CandidateFreezeContentResources.Byte) : Decidable (Window id offset length byte) :=
  inferInstanceAs (Decidable (byte.1 = id ∧ offset ≤ byte.2 ∧ byte.2 < offset + length))

private theorem zero_index (index : UniIndex) (bound : index.toNat < 1) : index=ix 0 := by
  have self : index = ix index.toNat := by cases index; simp [ix,UniIndex.toNat]
  rw [show index.toNat=0 by omega] at self
  exact self

def content : CandidateFreezeContentResources.Fragment := fun byte owner =>
  if owner = 0 ∧ Window sourceId 0 2 byte then some ⟨.mut,.active⟩
  else if owner = 1 ∧ Window destinationId 0 1 byte then some ⟨.ret,.active⟩ else none

noncomputable def interpretation : Interpretation := {
  precise := #[(sourceId,sourcePrecise),(destinationId,returnPrecise)]
  pointers := pointers
  loans := #[⟨0,none,0⟩,⟨1,none,0⟩]
  content := content }

noncomputable def identities : Identities := {
  interpretation := interpretation
  occurrences := #[⟨0,sourcePointer⟩,⟨1,destinationPointer⟩,
    ⟨2,S05ZeroCellJointCertificate.wildcardFamily⟩,
    ⟨2,S05ZeroCellJointCertificate.wildcardFamily⟩,
    ⟨3,S05ZeroCellJointCertificate.savedRawD⟩]
  attachments := #[⟨sourceId,ix 1,2⟩,⟨sourceId,ix 3,2⟩] }

/-- These STATIC current root/family annotations are connected to the existing
finite caller's known same-source dataflow. No old typed handles or generic
claim that arbitrary annotation arrays cover all actual copies is introduced. -/
def FamilyDataflow : Prop :=
  pointers[2]? = some ⟨sourceId,S05ZeroCellJointCertificate.wildcardFamily,ix 0⟩ ∧
  identities.occurrences[2]? = some ⟨2,S05ZeroCellJointCertificate.wildcardFamily⟩ ∧
  identities.occurrences[3]? = some ⟨2,S05ZeroCellJointCertificate.wildcardFamily⟩ ∧
  identities.attachments = #[⟨sourceId,ix 1,2⟩,⟨sourceId,ix 3,2⟩] ∧
  S05ZeroCellJointCertificate.FamilyBindings ∧ S05ZeroCellJointCertificate.CastFamilyBindings

theorem family_dataflow : FamilyDataflow :=
  ⟨rfl,rfl,rfl,rfl,S05ZeroCellJointCertificate.family_bindings,
    S05ZeroCellJointCertificate.cast_family_bindings⟩

theorem world : ActualWorld before = #[(sourceId,sourceAllocation),(destinationId,destinationAllocation)] := by
  unfold ActualWorld
  rw [live_entries]
  cbv

private theorem present_cases {id : AllocId} {allocation : Allocation Provenance BorrowTree}
    (present : Present (ActualWorld before) id allocation) :
    (id = sourceId ∧ allocation = sourceAllocation) ∨
      (id = destinationId ∧ allocation = destinationAllocation) := by
  simpa only [Present,world,Array.toList, List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,Prod.mk.injEq] using present

theorem actual_bindings : ActualBindings before argument 2 place {} call identities := by
  refine ⟨no_protectors,rfl,?_,?_,?_,?_,?_⟩
  · constructor
    · intro occurrence member
      simp only [identities,Array.toList,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals exact ⟨_,rfl,rfl⟩
    · intro attachment member
      simp only [identities,Array.toList,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals refine ⟨pointers[2]'(by decide),sourcePrecise,rfl,rfl,?_,rfl⟩
      all_goals simp [identities,interpretation]
  · intro pointer member
    simp only [identities,interpretation,pointers,Array.toList,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · refine ⟨sourceAllocation,?_,?_⟩
      · simp [Present,world]
      · refine ⟨CandidateCurrentJointPacketGraph.w,?_,?_,rfl,rfl⟩
        all_goals rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph]
        all_goals rfl
    · refine ⟨destinationAllocation,?_,?_⟩
      · simp [Present,world]
      · exact ⟨_,rfl,rfl,rfl,rfl⟩
    · refine ⟨sourceAllocation,?_,?_⟩
      · simp [Present,world]
      · refine ⟨CandidateCurrentJointPacketGraph.original,?_,?_,rfl⟩
        all_goals rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph]
        all_goals rfl
    · refine ⟨sourceAllocation,?_,?_⟩
      · simp [Present,world]
      · refine ⟨CandidateCurrentJointPacketGraph.d,?_,?_,rfl,rfl⟩
        all_goals rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph]
        all_goals rfl
  · intro _
    exact ⟨⟨0,none,0⟩,⟨sourceId,sourcePointer,ix 5⟩,rfl,rfl,rfl,rfl⟩
  · rfl
  · exact ⟨⟨1,none,0⟩,⟨destinationId,destinationPointer,ix 0⟩,rfl,rfl,rfl,rfl⟩

theorem claims : Claims interpretation call := by
  refine ⟨by decide,?_,?_⟩
  · intro byte
    simp [interpretation,content,call]
  · intro byte
    simp [interpretation,content,call]

private theorem charge_cases {byte : CandidateFreezeContentResources.Byte} {owner : Nat}
    {charge : CandidateFreezeContentResources.Charge} (found : content byte owner = some charge) :
    (owner=0 ∧ Window sourceId 0 2 byte ∧ charge=⟨.mut,.active⟩) ∨
    (owner=1 ∧ Window destinationId 0 1 byte ∧ charge=⟨.ret,.active⟩) := by
  unfold content at found
  split at found
  · rename_i yes
    exact .inl ⟨yes.1,yes.2,(Option.some.inj found).symm⟩
  · split at found
    · rename_i yes
      exact .inr ⟨yes.1,yes.2,(Option.some.inj found).symm⟩
    · cases found

theorem content_valid : CandidateFreezeContentResources.Valid content := by
  intro byte left right leftCharge rightCharge different leftAt rightAt
  rcases charge_cases leftAt with ⟨rfl,leftWindow,rfl⟩ | ⟨rfl,leftWindow,rfl⟩
  all_goals rcases charge_cases rightAt with ⟨rfl,rightWindow,rfl⟩ | ⟨rfl,rightWindow,rfl⟩
  · exact False.elim (different rfl)
  · exact False.elim (distinct_ids (leftWindow.1.symm.trans rightWindow.1))
  · exact False.elim (distinct_ids (rightWindow.1.symm.trans leftWindow.1))
  · exact False.elim (different rfl)

private theorem return_completes : Completes destinationAllocation.extra returnPrecise.completion := by
  refine ⟨rfl,rfl,by decide,?_,?_,?_,?_⟩
  · intro position root listed
    have bound := (Array.getElem?_eq_some_iff.mp listed).1
    change position < 1 at bound
    have zero : position=0 := by omega
    subst position
    have same : root=ix 0 := Option.some.inj listed.symm
    subst root
    exact ⟨_,rfl,rfl⟩
  · intro index node present
    have bound := GeneralBorrowNodeUpdate.lookup_valid destinationAllocation.extra.nodes index node present
    change index.toNat < 1 at bound
    have same : index=ix 0 := zero_index index bound
    subst index
    have sameNode : node = _ := Option.some.inj present.symm
    subst node
    refine ⟨rfl,?_,?_,by decide⟩
    · intro child
      constructor
      · intro impossible; cases impossible
      · rintro ⟨childNode,found,edge⟩
        have bound := GeneralBorrowNodeUpdate.lookup_valid destinationAllocation.extra.nodes child childNode found
        change child.toNat < 1 at bound
        have same : child=ix 0 := zero_index child bound
        subst child
        have sameNode : childNode = _ := Option.some.inj found.symm
        subst childNode
        cases edge
    · intro parent impossible; cases impossible
  · intro position root listed
    have bound := (Array.getElem?_eq_some_iff.mp listed).1
    change position < 1 at bound
    have zero : position=0 := by omega
    subst position
    have same : root=ix 0 := Option.some.inj listed.symm
    subst root
    rfl
  · intro child parent edge
    have bound := (Array.getElem?_eq_some_iff.mp edge).1
    change child.toNat < 1 at bound
    have zero : child.toNat=0 := by omega
    simp [returnPrecise,zero] at edge

theorem precise_shape : PreciseShape (ActualWorld before) interpretation := by
  refine ⟨?_,?_,?_⟩
  · rw [world]; decide +kernel
  · decide +kernel
  · intro id precise member
    simp only [interpretation,Array.toList,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · refine ⟨sourceAllocation,by simp [Present,world],?_,rfl,?_⟩
      · rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph]
        exact CandidateCurrentJointPacketGraph.completes
      · intro row member
        simp [sourcePrecise,CandidateCurrentJointPacketGraph.precise] at member
        rcases member with rfl | rfl
        all_goals rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph]
        all_goals rfl
    · refine ⟨destinationAllocation,by simp [Present,world],return_completes,rfl,?_⟩
      intro row member
      simp [returnPrecise] at member
      subst row
      rfl

private theorem return_rights (byte : Nat) (bound : byte < 1) :
    LoanRights destinationAllocation {} returnPrecise ⟨destinationId,destinationPointer,ix 0⟩ byte .ret := by
  have zero : byte=0 := by omega
  subst byte
  intro index node present
  have bound := GeneralBorrowNodeUpdate.lookup_valid destinationAllocation.extra.nodes index node present
  change index.toNat < 1 at bound
  have same : index=ix 0 := zero_index index bound
  subst index
  have sameNode : node = _ := Option.some.inj present.symm
  subst node
  constructor
  · intro _; change Allows _ false .Write .LocalAccess; unfold Allows GeneralBorrowExposedConditionalWritePermissions.Compatible; decide +kernel
  · intro impossible; exact False.elim (impossible (.refl _))

theorem precise_joint : PreciseJoint (ActualWorld before) {} interpretation := by
  refine ⟨precise_shape,content_valid,?_,?_⟩
  · intro owner loan found
    have bound := (Array.getElem?_eq_some_iff.mp found).1
    change owner < 2 at bound
    have cases : owner=0 ∨ owner=1 := by omega
    rcases cases with rfl | rfl
    all_goals have same : loan = _ := Option.some.inj found.symm
    all_goals subst loan
    all_goals exact ⟨⟨_,rfl⟩,fun _ impossible => by cases impossible⟩
  · intro byte owner charge found
    change content byte owner = some charge at found
    rcases charge_cases found with ⟨rfl,window,rfl⟩ | ⟨rfl,window,rfl⟩
    · refine ⟨⟨0,none,0⟩,⟨sourceId,sourcePointer,ix 5⟩,sourceAllocation,sourcePrecise,
        rfl,rfl,window.1.symm,?_,window.2.2,?_,?_,?_⟩
      · rw [window.1]; simp [Present,world]
      · rw [window.1]; simp [interpretation]
      · intro _
        exact CandidateCurrentJointPacketGraph.source_rights sourceAllocation
          CandidateCurrentJointPacketGraph.actual_graph sourceId 4096 byte.2 window.2.2
      · intro _ impossible; cases impossible
    · refine ⟨⟨1,none,0⟩,⟨destinationId,destinationPointer,ix 0⟩,destinationAllocation,returnPrecise,
        rfl,rfl,window.1.symm,?_,window.2.2,?_,?_,?_⟩
      · rw [window.1]; simp [Present,world]
      · rw [window.1]; simp [interpretation]
      · intro _; exact return_rights byte.2 window.2.2
      · intro _ impossible; cases impossible

def sourceLocation : LocationTree :=
  ((sourceAllocation.extra.locations.entries[0]?).map (·.data)).getD default

private theorem source_segments : sourceAllocation.extra.locations.entries =
    #[⟨⟨0,2⟩,sourceLocation⟩] := by cbv

private theorem source_permissions : sourceLocation.perms =
    ⟨#[some ⟨.Unique,true,.None⟩,some ⟨.Cell,true,.Write⟩,
      some ⟨.Disabled,true,.Read⟩,some ⟨.Cell,true,.None⟩,none,
      some ⟨.ReservedFrz false,true,.Read⟩]⟩ := by cbv

/-- Exact scalar equality holds here, including accessed bits and SIFA. This
is an initial packet fact, not a universal representation-preservation claim. -/
theorem source_scalar_identity (byte : Nat) (bound : byte < 2) (index : UniIndex)
    (node : TreeNode) (present : sourceAllocation.extra.nodes.get index = some node) :
    PreciseState sourcePrecise byte index = RawState sourceLocation index node := by
  rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph] at present
  unfold RawState
  rw [source_permissions]
  rcases (show byte=0 ∨ byte=1 by omega) with rfl | rfl
  all_goals rcases CandidateCurrentJointPacketGraph.nodes index node present with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rfl

theorem initial_observation : InitialObservation (ActualWorld before) {} interpretation := by
  intro id allocation precise present member byte bound segment stored lower upper index node nodeAt kind relation rights
  rcases present_cases present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have same : precise=sourcePrecise := by
      simpa [interpretation,distinct_ids,Ne.symm distinct_ids] using member
    subst precise
    rw [source_segments] at stored
    have same : segment=⟨⟨0,2⟩,sourceLocation⟩ := by simpa using stored
    subst segment
    rw [source_scalar_identity byte bound index node nodeAt] at rights
    exact rights
  · have same : precise=returnPrecise := by
      simpa [interpretation,distinct_ids,Ne.symm distinct_ids] using member
    subst precise
    have zero : byte=0 := by change byte < 1 at bound; omega
    subst byte
    have segmentSame : segment = (destinationAllocation.extra.locations.entries[0]'(by decide +kernel)) := by
      change segment ∈ [destinationAllocation.extra.locations.entries[0]'(by decide +kernel)] at stored
      simpa using stored
    subst segment
    have indexSame : index=ix 0 := zero_index index (GeneralBorrowNodeUpdate.lookup_valid _ _ _ nodeAt)
    subst index
    have nodeSame : node = _ := Option.some.inj nodeAt.symm
    subst node
    exact rights

/-- Address normalization is an explicit representation fact, separate from
precise ownership and the scalar observation relation. No blanket cache-empty
condition is imposed. -/
theorem normalized_windows : NormalizedWindows before argument 2 place call identities := by
  constructor
  · right
    refine ⟨by decide,sourcePointer,rfl,⟨0,none,0⟩,pointers[0]'(by decide),rfl,rfl,rfl,rfl,?_⟩
    exact ⟨sourceEntry,4096,source_present,source_cached,rfl,by decide,by decide,rfl,by decide,rfl⟩
  · refine ⟨rfl,destinationPointer,rfl,⟨1,none,0⟩,pointers[1]'(by decide),rfl,rfl,rfl,rfl,?_⟩
    exact ⟨destinationEntry,8192,destination_present,destination_cached,rfl,by decide,by decide,rfl,by decide,rfl⟩

/-- Positive physical source and writable Bool storage are independently
checked. BoolDestination never requires the old byte initialized. -/
theorem physical : OrdinaryPhysicalValidity.MutU8Slice sourceAllocation 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination destinationAllocation 0 :=
  ⟨S05ZeroCellJointPhysical.source_physical,S05ZeroCellJointPhysical.destination_physical⟩

/-- Actual accepted packet satisfies all three candidate layers, plus explicit
normalization and physical storage. Still NOT ordinary-input coverage. -/
theorem packet : ActualBindings before argument 2 place {} call identities ∧
    NormalizedWindows before argument 2 place call identities ∧
    PreciseJoint (ActualWorld before) {} interpretation ∧ Claims interpretation call ∧
    InitialObservation (ActualWorld before) {} interpretation ∧ FamilyDataflow ∧
    OrdinaryPhysicalValidity.MutU8Slice sourceAllocation 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination destinationAllocation 0 :=
  ⟨actual_bindings,normalized_windows,precise_joint,claims,initial_observation,
    family_dataflow,physical⟩

end DuplicatePrefix.CandidateCurrentJointPacket

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentJointPacket." ||
        name.toString.startsWith "DuplicatePrefix.CandidateCurrentJointPacketGraph." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current-joint packet dependency {dependency}"
