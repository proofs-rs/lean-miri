import duplicate_prefix.CandidateCurrentGrantResources
import duplicate_prefix.CandidateCurrentJointAdmissionBoundary

/-! Admission of the finite resource proposal at the actual accepted packet.
This does not adopt the proposal as Ordinary or prove arbitrary input coverage.
The raw-revoked admission-boundary packet fails the local resource embedding. -/
namespace DuplicatePrefix.CandidateCurrentJointResourcePacket
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CandidateCurrentJointRawReplacement
open S05ZeroCellTypedGeneratedPrefix (ix tag)
open S05ZeroCellJointPacket
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def branch (index : UniIndex) : Nat := if index=ix 1 ∨ index=ix 2 ∨ index=ix 4 then 1 else 0
private theorem edge_branch (child parent : UniIndex)
    (edge : CandidateCurrentJointPacketGraph.completion.parents[child.toNat]? = some (some parent)) :
    branch parent ≤ branch child := by
  have bound := (Array.getElem?_eq_some_iff.mp edge).1
  change child.toNat < 6 at bound
  have choices : child.toNat=0 ∨ child.toNat=1 ∨ child.toNat=2 ∨
      child.toNat=3 ∨ child.toNat=4 ∨ child.toNat=5 := by omega
  have self : child = ix child.toNat := by cases child; simp [ix,UniIndex.toNat]
  rcases choices with h | h | h | h | h | h
  all_goals rw [h] at self
  all_goals subst child
  all_goals simp [CandidateCurrentJointPacketGraph.completion,ix,UniIndex.toNat] at edge
  all_goals subst parent
  all_goals decide
private theorem below_branch {ancestor child : UniIndex}
    (path : Below CandidateCurrentJointPacketGraph.completion ancestor child) :
    branch ancestor ≤ branch child := by
  induction path with
  | refl => exact Nat.le_refl _
  | step edge _ earlier => exact Nat.le_trans earlier (edge_branch _ _ edge)

/-- Actual raw rows admit source exclusivity and revocable competing grants.
This proof decodes the concrete rows; it does not consume InitialObservation,
precise operational rights, a successful access or raw authority as a premise. -/
theorem source_resources (index : UniIndex) (node : TreeNode)
    (present : sourceAllocation.extra.nodes.get index = some node) :
    let resource := denote (RawState CandidateCurrentJointPacket.sourceLocation index node) false
    Realized (RawState CandidateCurrentJointPacket.sourceLocation index node) false ∧
    (Below CandidateCurrentJointPacketGraph.completion index (ix 5) → .exclusive ∈ tokens resource) ∧
    (∀ demand, Competing resource demand) := by
  rw [← CandidateCurrentJointPacket.source_scalar_identity 0 (by decide) index node present]
  rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph] at present
  rcases CandidateCurrentJointPacketGraph.nodes index node present with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (intro path; have impossible := below_branch path; change 1 ≤ 0 at impossible; omega)
    | (intro demand; rfl)
    | (intro _; trivial)
    | (unfold Realized WellFormed denote PreciseState; decide +kernel)

/-- The existing scalar adequacy lemmas consume the admitted resource data. -/
theorem source_authority (index : UniIndex) (node : TreeNode)
    (present : sourceAllocation.extra.nodes.get index = some node) :
    (Below CandidateCurrentJointPacketGraph.completion index (ix 5) →
      OrdinaryBorrowAuthority.LocalWrite (RawState CandidateCurrentJointPacket.sourceLocation index node) false) ∧
    (¬ Below CandidateCurrentJointPacketGraph.completion index (ix 5) →
      OrdinaryBorrowAuthority.ForeignWrite (RawState CandidateCurrentJointPacket.sourceLocation index node) false) := by
  have resources := source_resources index node present
  exact ⟨fun localPath => local_write _ _ resources.1 (token_local _ _ (resources.2.1 localPath)),
    fun _ => foreign_write _ _ resources.1 (resources.2.2 .exclusive)⟩

/-- The unchanged Bool destination has an activated, accessed, unprotected
exclusive resource. This concerns its current grant, not its previous byte. -/
def returnLocation : LocationTree :=
  ((destinationAllocation.extra.locations.entries[0]?).map (·.data)).getD default

def returnNode : TreeNode := ⟨tag 7,none,#[],.Disabled,.None,false,none⟩

theorem return_resources :
    let state := RawState returnLocation (ix 0)
      returnNode
    Realized state false ∧ Local (denote state false) .exclusive := by
  cbv
  simp

private theorem source_segments : sourceAllocation.extra.locations.entries =
    #[⟨⟨0,2⟩,CandidateCurrentJointPacket.sourceLocation⟩] := by cbv
private theorem return_segments : destinationAllocation.extra.locations.entries =
    #[⟨⟨0,1⟩,returnLocation⟩] := by cbv

private theorem return_node (index : UniIndex) (node : TreeNode)
    (present : destinationAllocation.extra.nodes.get index = some node) :
    index = ix 0 ∧ node = returnNode := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  change index.toNat < 1 at bound
  have self : index = ix index.toNat := by cases index; simp [ix,UniIndex.toNat]
  rw [show index.toNat=0 by omega] at self
  subst index
  have actual : destinationAllocation.extra.nodes.get (ix 0) = some returnNode := by cbv
  rw [actual] at present
  exact ⟨rfl,(Option.some.inj present).symm⟩

theorem actual_realized : ActualRealized (ActualWorld before) {} := by
  intro id allocation live segment member index node nodeAt
  simp only [Present,CandidateCurrentJointPacket.world,List.mem_cons,
    List.not_mem_nil,or_false,Prod.mk.injEq] at live
  rcases live with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [source_segments] at member
    have same : segment=⟨⟨0,2⟩,CandidateCurrentJointPacket.sourceLocation⟩ := by simpa using member
    subst segment
    exact (source_resources index node nodeAt).1
  · rw [return_segments] at member
    have same : segment=⟨⟨0,1⟩,returnLocation⟩ := by simpa using member
    subst segment
    obtain ⟨rfl,rfl⟩ := return_node index node nodeAt
    exact return_resources.1

theorem source_embedding (byte : Nat) :
    Embeds sourceAllocation {} CandidateCurrentJointPacket.sourcePrecise.completion (ix 5) byte .exclusive := by
  intro segment member lower upper index node nodeAt
  rw [source_segments] at member
  have same : segment=⟨⟨0,2⟩,CandidateCurrentJointPacket.sourceLocation⟩ := by simpa using member
  subst segment
  constructor
  · exact (source_resources index node nodeAt).2.1
  · intro conflict
    change False at conflict
    exact False.elim conflict

theorem return_embedding (byte : Nat) :
    Embeds destinationAllocation {} CandidateCurrentJointPacket.returnPrecise.completion (ix 0) byte .exclusive := by
  intro segment member lower upper index node nodeAt
  rw [return_segments] at member
  have same : segment=⟨⟨0,1⟩,returnLocation⟩ := by simpa using member
  subst segment
  obtain ⟨rfl,rfl⟩ := return_node index node nodeAt
  constructor
  · intro _
    change Demand.exclusive ∈ [Demand.shared,Demand.exclusive]
    simp
  · intro conflict
    change False at conflict
    exact False.elim conflict

private theorem charge_cases {byte : CandidateFreezeContentResources.Byte} {owner : Nat}
    {charge : CandidateFreezeContentResources.Charge}
    (found : CandidateCurrentJointPacket.content byte owner = some charge) :
    (owner=0 ∧ Window sourceId 0 2 byte ∧ charge=⟨.mut,.active⟩) ∨
    (owner=1 ∧ Window destinationId 0 1 byte ∧ charge=⟨.ret,.active⟩) := by
  unfold CandidateCurrentJointPacket.content at found
  split at found
  · rename_i yes
    exact .inl ⟨yes.1,yes.2,(Option.some.inj found).symm⟩
  · split at found
    · rename_i yes
      exact .inr ⟨yes.1,yes.2,(Option.some.inj found).symm⟩
    · cases found

/-- The actual accepted packet embeds both independent active content charges
in one completion with all automatically decoded current protector guards.
InitialObservation and operation-success are absent from this admission proof. -/
theorem joint : Joint (ActualWorld before) {} CandidateCurrentJointPacket.interpretation := by
  refine ⟨CandidateCurrentJointPacket.precise_shape,CandidateCurrentJointPacket.content_valid,actual_realized,?_⟩
  intro byte owner mode found
  change CandidateCurrentJointPacket.content byte owner = some ⟨mode,.active⟩ at found
  rcases charge_cases found with ⟨rfl,window,charge⟩ | ⟨rfl,window,charge⟩
  · have same : mode = .mut := (CandidateFreezeContentResources.Charge.mk.inj charge).1
    subst mode
    refine ⟨⟨0,none,0⟩,⟨sourceId,sourcePointer,ix 5⟩,sourceAllocation,CandidateCurrentJointPacket.sourcePrecise,
      rfl,rfl,window.1.symm,?_,window.2.2,?_,source_embedding byte.2⟩
    · rw [window.1];simp [Present,CandidateCurrentJointPacket.world]
    · rw [window.1];simp [CandidateCurrentJointPacket.interpretation]
  · have same : mode = .ret := (CandidateFreezeContentResources.Charge.mk.inj charge).1
    subst mode
    refine ⟨⟨1,none,0⟩,⟨destinationId,destinationPointer,ix 0⟩,destinationAllocation,CandidateCurrentJointPacket.returnPrecise,
      rfl,rfl,window.1.symm,?_,window.2.2,?_,return_embedding byte.2⟩
    · rw [window.1];simp [Present,CandidateCurrentJointPacket.world]
    · rw [window.1];simp [CandidateCurrentJointPacket.interpretation]

/-- Revoking the actual source grant is rejected by the resource proposal,
without adding InitialObservation as an ownership clause. -/
theorem revoked_rejected : ¬ Local
    (denote (RawState CandidateCurrentJointAdmissionBoundary.revokedLocation (ix 5)
      CandidateCurrentJointPacketGraph.w) false) .exclusive := by
  intro embedded
  have state : RawState CandidateCurrentJointAdmissionBoundary.revokedLocation (ix 5)
      CandidateCurrentJointPacketGraph.w = ⟨.Disabled,true,.Read⟩ := by cbv
  rw [state] at embedded
  exact embedded

/-- The resource proposal rejects the SAME revoked current-call packet that
still inhabits all preceding independent binding and precise-content layers. -/
theorem revoked_not_joint : ¬ Joint (ActualWorld CandidateCurrentJointAdmissionBoundary.revokedBefore) {}
    CandidateCurrentJointPacket.interpretation := by
  intro admitted
  obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,_,live,_,preciseAt,embedding⟩ :=
    admitted.active (sourceId,0) 0 .mut (by simp [CandidateCurrentJointPacket.interpretation,
      CandidateCurrentJointPacket.content,Window])
  change some ⟨0,none,0⟩ = some loan at loanAt
  have loanEq := Option.some.inj loanAt
  subst loan
  change some ⟨sourceId,sourcePointer,ix 5⟩ = some pointer at pointerAt
  have pointerEq := Option.some.inj pointerAt
  subst pointer
  have allocationEq : allocation = CandidateCurrentJointAdmissionBoundary.revokedAllocation := by
    simpa [Present,CandidateCurrentJointAdmissionBoundary.world,distinct_ids,Ne.symm distinct_ids] using live
  subst allocation
  have preciseEq : precise = CandidateCurrentJointPacket.sourcePrecise := by
    simpa [CandidateCurrentJointPacket.interpretation,distinct_ids,Ne.symm distinct_ids] using preciseAt
  subst precise
  have nodeAt : CandidateCurrentJointAdmissionBoundary.revokedAllocation.extra.nodes.get (ix 5) =
      some CandidateCurrentJointPacketGraph.w := by
    change sourceAllocation.extra.nodes.get (ix 5) = some _
    rw [show sourceAllocation.extra = CandidateCurrentJointPacketGraph.tree from CandidateCurrentJointPacketGraph.actual_graph]
    rfl
  have token := (embedding ⟨⟨0,2⟩,CandidateCurrentJointAdmissionBoundary.revokedLocation⟩
    (by simp [CandidateCurrentJointAdmissionBoundary.revokedAllocation,replaceAllocation,
      CandidateCurrentJointAdmissionBoundary.revokedLocations,Allocation.mapExtra])
    (by decide) (by decide) (ix 5) CandidateCurrentJointPacketGraph.w nodeAt).1 (.refl _)
  have status : RawState CandidateCurrentJointAdmissionBoundary.revokedLocation (ix 5)
      CandidateCurrentJointPacketGraph.w = ⟨.Disabled,true,.Read⟩ := by cbv
  change Demand.exclusive ∈ tokens (denote (RawState CandidateCurrentJointAdmissionBoundary.revokedLocation
    (ix 5) CandidateCurrentJointPacketGraph.w) false) at token
  rw [status] at token
  exact List.not_mem_nil token

end DuplicatePrefix.CandidateCurrentJointResourcePacket

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentJointResourcePacket." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved resource packet dependency {dependency}"
