import duplicate_prefix.CandidateCurrentJointCall
import duplicate_prefix.OrdinaryBorrowAuthority
import duplicate_prefix.GeneralBorrowProtectedReadCompatible

/-! UNADOPTED finite current grant resource denotation. A grant describes
availability and a retained commitment, not ownership automatically created by
pointer existence. Scalar adequacy is lifted to a joint configuration of actual auto protector
commitments and existing active contents. This is not ordinary-input admission
or an origin-family reconstruction. StableChoices/ActualBindings, loan-parent
coherence, suspended-loan identities, protector lifetime admission and SIFA
representation and covering raw segments remain separate obligations. The
resource interpretation is proposed; these adequacy proofs do not establish
independent semantic admission. -/
namespace DuplicatePrefix.CandidateCurrentGrantResources
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false

inductive Demand where | shared | exclusive deriving DecidableEq, Repr
inductive Status where
  | revoked | readOnly | reservation (interfered : Bool)
  | interiorReservation | activated | interiorAmbient
  deriving DecidableEq, Repr
inductive Commitment where | revocable | dormant | retained deriving DecidableEq, Repr

structure Resource where
  status : Status
  commitment : Commitment
  held : Bool
  accessed : Bool
  deriving DecidableEq, Repr

/-- Revocation remains observable even after the grant loses local contents.
In particular, protected accessed Disabled is a retained tombstone, not empty. -/
def denote (state : LocationState) (held : Bool) : Resource :=
  ⟨(match state.permission with
    | .Disabled => .revoked | .Frozen => .readOnly
    | .ReservedFrz c => .reservation c | .ReservedIM => .interiorReservation
    | .Unique => .activated | .Cell => .interiorAmbient),
    if !held then .revocable else if state.accessed then .retained else .dormant,
    held, state.accessed⟩

/-- Activated grants must have been accessed. Interior-mutable reservations
cannot carry a protector (a distinct representation invariant). -/
def WellFormed (resource : Resource) : Prop :=
  (resource.status = .activated → resource.accessed = true) ∧
  (resource.status = .interiorReservation → resource.held = false)

/-- Adequacy is restricted to decoded actual states; arbitrary Resource values
need not have their commitment consistent with held/accessed. -/
def Realized (state : LocationState) (held : Bool) : Prop :=
  WellFormed (denote state held)

/-- Local contents can be embedded in a live status. A protected reservation
that suffered interference retains read contents but cannot activate exclusivity. -/
def Local (resource : Resource) (demand : Demand) : Prop :=
  match resource.status, demand with
  | .revoked, _ => False
  | .readOnly, .exclusive => False
  | .reservation true, .exclusive => resource.held = false
  | _, _ => True

/-- Revocable and dormant competing grants impose no retained protector commitment.
A retained ambient interior-mutable gateway carries no Freeze charge. Retained
read/reservation contents share with readers; activated and revoked commitments
cannot be displaced even by a reader. -/
def Competing (resource : Resource) (demand : Demand) : Prop :=
  match resource.commitment with
  | .revocable | .dormant => True
  | .retained => match resource.status, demand with
    | .interiorAmbient, _ => True
    | .readOnly, .shared | .reservation _, .shared => True
    | _, _ => False

private theorem possible (state : LocationState) (held : Bool)
    (realized : Realized state held) : state.possible = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission <;> cases accessed <;>
    simp_all [Realized,WellFormed,denote,LocationState.possible,Permission.isUnique]

/-- Finite scalar adequacy: no operational Allows or success predicate occurs
in the resource definitions. The conclusion is the existing raw Write table. -/
theorem local_write (state : LocationState) (held : Bool)
    (realized : Realized state held) (embedded : Local (denote state held) .exclusive) :
    OrdinaryBorrowAuthority.LocalWrite state held := by
  have valid := possible state held realized
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz c => cases c <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Local,denote]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Local,denote]

theorem foreign_write (state : LocationState) (held : Bool)
    (realized : Realized state held) (embedded : Competing (denote state held) .exclusive) :
    OrdinaryBorrowAuthority.ForeignWrite state held := by
  have valid := possible state held realized
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz c => cases c <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Competing,denote,Realized,WellFormed]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Competing,denote,Realized,WellFormed]

/-- Shared contents use the same resource interpretation, without introducing
an independent four-action observation premise. -/
theorem local_read (state : LocationState) (held : Bool)
    (realized : Realized state held) (embedded : Local (denote state held) .shared) :
    GeneralBorrowProtectedReadCompatible.Compatible state .LocalAccess held := by
  have valid := possible state held realized
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission <;>
    simp_all [GeneralBorrowProtectedReadCompatible.Compatible,Local,denote]

theorem foreign_read (state : LocationState) (held : Bool)
    (realized : Realized state held) (embedded : Competing (denote state held) .shared) :
    GeneralBorrowProtectedReadCompatible.Compatible state .ForeignAccess held := by
  have valid := possible state held realized
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz c => cases c <;> cases accessed <;> cases held <;>
      simp_all [GeneralBorrowProtectedReadCompatible.Compatible,Competing,denote,Realized,WellFormed]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases accessed <;> cases held <;>
      simp_all [GeneralBorrowProtectedReadCompatible.Compatible,Competing,denote,Realized,WellFormed]

/-- A retained revoked grant is an obstruction despite having no local content. -/
theorem retained_revoked_blocks (sifa : IdempotentForeignAccess) (demand : Demand) :
    ¬ Competing (denote ⟨.Disabled,true,sifa⟩ true) demand := by
  cases demand <;> simp [Competing,denote]

/-- Ambient Cell status itself never creates a competing Freeze content charge. -/
theorem ambient_competing (accessed held : Bool) (sifa : IdempotentForeignAccess)
    (demand : Demand) : Competing (denote ⟨.Cell,accessed,sifa⟩ held) demand := by
  cases accessed <;> cases held <;> cases demand <;> simp [Competing,denote]

/-! A joint resource configuration. Protector commitments are automatically
extracted from actual grant rows: the configuration cannot omit a protector
commitment from the supplied rows and held table. Unlisted logical loans and
copy-family facts are not reconstructed.
The existing finite content fragment supplies independently assigned active
contents. Ancestry only locates their support; ambient Cell presence contributes
no Freeze content ownership. No ordinary-input admission is asserted. -/
open Miri Miri.Memory
open CandidateStableCallOwnership CandidateCurrentJointCall

inductive Guard where | none | freeze | exclusion | tombstone
  deriving DecidableEq, Repr

/-- A revoked retained commitment remains a tombstone. Unprotected grants are
revocable, and protected unaccessed grants have no current protector charge. -/
def guard (resource : Resource) : Guard :=
  match resource.commitment with
  | .revocable | .dormant => .none
  | .retained => match resource.status with
    | .interiorAmbient | .interiorReservation => .none
    | .readOnly | .reservation _ => .freeze
    | .activated => .exclusion
    | .revoked => .tombstone

/-- Binary content incompatibility between the two resource species. Whether
one writes it as claim/guard or guard/claim does not alter the conflict. -/
def Clash (commitment : Guard) (demand : Demand) : Prop :=
  match commitment, demand with
  | .none, _ | .freeze, .shared => False
  | _, _ => True

/-- Explicit local entitlement tokens. Reading and activating exclusivity are
separate resources; interference withdraws activation under protection. -/
def tokens (resource : Resource) : List Demand :=
  match resource.status with
  | .revoked => []
  | .readOnly => [.shared]
  | .reservation true => if resource.held then [.shared] else [.shared,.exclusive]
  | _ => [.shared,.exclusive]

theorem token_local (resource : Resource) (demand : Demand)
    (present : demand ∈ tokens resource) : Local resource demand := by
  rcases resource with ⟨status,commitment,held,accessed⟩
  cases status with
  | reservation c => cases c <;> cases held <;> cases demand <;> simp_all [tokens,Local]
  | revoked | readOnly | interiorReservation | activated | interiorAmbient =>
      cases demand <;> simp_all [tokens,Local]

theorem no_clash_competing (state : LocationState) (held : Bool) (demand : Demand)
    (realized : Realized state held) (compatible : ¬ Clash (guard (denote state held)) demand) :
    Competing (denote state held) demand := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz c => cases c <;> cases accessed <;> cases held <;> cases demand <;>
      simp_all [Realized,WellFormed,denote,guard,Clash,Competing]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases accessed <;> cases held <;> cases demand <;>
      simp_all [Realized,WellFormed,denote,guard,Clash,Competing]

def demandOf (mode : CandidateFreezeContentResources.Mode) : Demand :=
  if mode = .read then .shared else .exclusive

/-- Every actual row contributes its automatically decoded protector resource.
This invariant includes rows without any listed active content loan. -/
def ActualRealized (world : World) (held : ProtectedTags) : Prop :=
  ∀ id allocation, Present world id allocation →
    ∀ segment ∈ allocation.extra.locations.entries.toList,
    ∀ index node, allocation.extra.nodes.get index = some node →
      Realized (RawState segment.data index node) (held.contains node.tag)

/-- ONE completed origin assignment interprets each charge in all current raw
segments. Local token occupancy and conflicts with automatically present guards
are resource statements; neither an Allows table nor observation inclusion is
an input. Suspended charges need no active embedding. -/
def Embeds (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (completion : Completion) (grant : UniIndex) (byte : Nat) (demand : Demand) : Prop :=
  ∀ segment ∈ allocation.extra.locations.entries.toList,
    segment.range.start.toNat ≤ byte → byte < segment.range.stop.toNat →
    ∀ index node, allocation.extra.nodes.get index = some node →
      (Below completion index grant →
        demand ∈ tokens (denote (RawState segment.data index node) (held.contains node.tag))) ∧
      (Clash (guard (denote (RawState segment.data index node) (held.contains node.tag))) demand →
        Below completion index grant)

/-- A sufficient initial resource configuration, not complete loan well-formedness.
Actual machine/pointer bindings and stable occurrence/family correspondence are
separate. Suspended claims impose no active demand here, including no identity
or parent-coherence assertion. Realization covers all actual rows. -/
structure Joint (world : World) (held : ProtectedTags) (interpretation : Interpretation) : Prop where
  shape : PreciseShape world interpretation
  contents : CandidateFreezeContentResources.Valid interpretation.content
  actual : ActualRealized world held
  active : ∀ byte owner mode,
    interpretation.content byte owner = some ⟨mode,.active⟩ →
    ∃ loan pointer allocation precise,
      interpretation.loans[owner]? = some loan ∧
      interpretation.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present world byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ interpretation.precise.toList ∧
      Embeds allocation held precise.completion pointer.grant byte.2 (demandOf mode)

/-- Composition of current resource tokens and all auto protector commitments
supplies the initial raw tables. It makes no observation-inclusion assumption. -/
theorem embedding_raw (world : World) (held : ProtectedTags)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (present : Present world id allocation) (actual : ActualRealized world held)
    (precise : PreciseAllocation) (pointer : PointerInstance) (byte : Nat)
    (mode : CandidateFreezeContentResources.Mode)
    (embedding : Embeds allocation held precise.completion pointer.grant byte (demandOf mode)) :
    RawRights allocation held precise pointer byte mode := by
  intro segment member lower upper index node nodeAt
  have realized := actual id allocation present segment member index node nodeAt
  obtain ⟨support,compatible⟩ := embedding segment member lower upper index node nodeAt
  constructor
  · intro ancestor
    have entitlement := token_local _ _ (support ancestor)
    cases mode with
    | read => exact local_read _ _ realized entitlement
    | «mut» | ret =>
      exact local_write _ _ realized entitlement
  · intro outside
    have competing := no_clash_competing _ _ _ realized (fun conflict => outside (compatible conflict))
    cases mode with
    | read => exact foreign_read _ _ realized competing
    | «mut» | ret => exact foreign_write _ _ realized competing

theorem active_raw (world : World) (held : ProtectedTags) (interpretation : Interpretation)
    (joint : Joint world held interpretation)
    (byte : CandidateFreezeContentResources.Byte) (owner : Nat)
    (mode : CandidateFreezeContentResources.Mode)
    (active : interpretation.content byte owner = some ⟨mode,.active⟩) :
    ∃ loan pointer allocation precise,
      interpretation.loans[owner]? = some loan ∧ interpretation.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present world byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ interpretation.precise.toList ∧ RawRights allocation held precise pointer byte.2 mode := by
  obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,id,present,bound,preciseAt,embedding⟩ :=
    joint.active byte owner mode active
  exact ⟨loan,pointer,allocation,precise,loanAt,pointerAt,id,present,bound,preciseAt,
    embedding_raw world held allocation byte.1 present joint.actual precise pointer byte.2 mode embedding⟩

end DuplicatePrefix.CandidateCurrentGrantResources

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentGrantResources." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current grant resource dependency {dependency}"
