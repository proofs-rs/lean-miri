import duplicate_prefix.CandidateFreezeContentResources
import duplicate_prefix.OrdinaryBorrowAuthority
import duplicate_prefix.GeneralBorrowExposedConditionalWritePermissions
import duplicate_prefix.GeneralBorrowProtectedReadCompatible
import duplicate_prefix.GeneralBorrowExposureCardinality
import duplicate_prefix.GeneralBorrowLocationSifaConsistency
import duplicate_prefix.OrdinaryPhysicalValidity

/-! UNADOPTED ownership-clause proposal, not ordinary validity or completed S05.
Pinned machine.rs:280–295 motivates ONE existential, stable pointer origin;
tree.rs:293–303 motivates older exposed attachments in earlier components.
The explicit scalar inclusion choices below are CANDIDATES, not a
proved abstraction relation. Either-related accesses leave raw states unchanged,
so precise permissions may differ. Current raw fields do not identify the exact
correlated family, exposure-at-origin time, or pointer-instance identities.
Initialization/transition adequacy and ordinary-input coverage remain UNPROVED.
No interpreter semantics, historical execution or success condition is added.
-/
namespace DuplicatePrefix.CandidateStableCallOwnership
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false

abbrev World := Array (AllocId × Allocation Provenance BorrowTree)

/-- The same world contains source and return storage, whether their IDs agree
or differ. Global protectors are supplied separately, not chosen per loan. -/
def Present (world : World) (id : AllocId) (allocation : Allocation Provenance BorrowTree) : Prop :=
  (id, allocation) ∈ world.toList

def RawState (location : LocationTree) (index : UniIndex)
    (node : TreeNode) : LocationState :=
  (location.perms.get index).getD node.defaultLocationState

/-- Actual permission/protector/accessed tables, without invoking an operation. -/
def Allows (state : LocationState) (held : Bool) (kind : AccessKind)
    (relation : AccessRelatedness) : Prop :=
  match kind with
  | .Read => GeneralBorrowProtectedReadCompatible.Compatible state relation held
  | .Write => GeneralBorrowExposedConditionalWritePermissions.Compatible state relation held

/-- Parent map and depth are finite, shared across every byte of this allocation. -/
structure Completion where
  parents : Array (Option UniIndex)
  depths : Array Nat

/-- Finite completed ancestry, including reflexivity. -/
inductive Below (completion : Completion) : UniIndex → UniIndex → Prop
  | refl (index : UniIndex) : Below completion index index
  | step {ancestor parent child : UniIndex} :
      completion.parents[child.toNat]? = some (some parent) →
      Below completion ancestor parent → Below completion ancestor child

/-- Explicit physical and virtual edge constraints; no grant accessibility claim. -/
def Completes (tree : BorrowTree) (completion : Completion) : Prop :=
  completion.parents.size = tree.nodes.data.size ∧
  completion.depths.size = tree.nodes.data.size ∧
  tree.roots.toList.Nodup ∧
  (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root →
    ∃ node, tree.nodes.get root = some node ∧ node.parent = none) ∧
  (∀ index node, tree.nodes.get index = some node →
    tree.tagMapping.get node.tag = some index ∧
    (∀ child, child ∈ node.children.toList ↔
      ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index) ∧
    (∀ parent, node.parent = some parent → completion.parents[index.toNat]? = some (some parent)) ∧
    (node.parent = none ↔ index ∈ tree.roots.toList)) ∧
  (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root →
    if position = 0 then completion.parents[root.toNat]? = some none
    else ∃ (earlier : Nat) (originRoot origin : UniIndex) (rootNode originNode : TreeNode),
      earlier < position ∧ tree.roots[earlier]? = some originRoot ∧
      tree.nodes.get root = some rootNode ∧ tree.nodes.get origin = some originNode ∧
      originNode.isExposed = true ∧ originNode.tag.value < rootNode.tag.value ∧
      Path tree originRoot origin ∧ completion.parents[root.toNat]? = some (some origin)) ∧
  (∀ child parent, completion.parents[child.toNat]? = some (some parent) →
    (∃ childNode, tree.nodes.get child = some childNode) ∧
    (∃ parentNode, tree.nodes.get parent = some parentNode) ∧
    completion.depths[parent.toNat]?.getD 0 < completion.depths[child.toNat]?.getD 0)

/-- Byte rows and node columns are bounded by the actual allocation dimensions. -/
structure PreciseAllocation where
  completion : Completion
  states : Array (Array LocationState)

def PreciseState (precise : PreciseAllocation) (byte : Nat) (index : UniIndex) : LocationState :=
  ((precise.states[byte]?.getD #[])[index.toNat]?).getD ⟨.Disabled, false, .None⟩

/-- Raw exposure cardinalities and SIFA bounds constrain the RAW representation.
They are not equations identifying the selected precise alternative. The
four-way scalar inclusion is a proposed abstraction; precise activity is
retained without imposing an unsupported direction against raw activity. These clauses
do not establish successor correlation or the admissible origin family. -/
def Refines (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (precise : PreciseAllocation) : Prop :=
  Completes allocation.extra precise.completion ∧
  precise.states.size = allocation.len ∧
  (∀ row ∈ precise.states.toList, row.size = allocation.extra.nodes.data.size) ∧
  (∀ byte, byte < allocation.len → ∃ segment,
    segment ∈ allocation.extra.locations.entries.toList ∧
    segment.range.start.toNat ≤ byte ∧ byte < segment.range.stop.toNat) ∧
  (∀ segment ∈ allocation.extra.locations.entries.toList,
    segment.range.start.toNat < segment.range.stop.toNat ∧
    segment.range.stop.toNat ≤ allocation.len ∧
    GeneralBorrowExposureCardinality.LocationCoherent allocation.extra segment.data held ∧
    GeneralBorrowLocationSifaConsistency.Profile allocation.extra segment.data held ∧
    ∀ byte, segment.range.start.toNat ≤ byte → byte < segment.range.stop.toNat →
    ∀ index node, allocation.extra.nodes.get index = some node →
      let raw := RawState segment.data index node
      let selected := PreciseState precise byte index
      selected.possible = true ∧ raw.possible = true ∧
      ∀ kind relation, Allows selected (held.contains node.tag) kind relation →
        Allows raw (held.contains node.tag) kind relation)

/-- Array position is the logical pointer-instance identity. Equal pointer bits
need not mean the same instance; copies that must share a choice need an explicit
binding outside this ownership clause. Empty-only pointers may be omitted from
this array entirely, including dangling/no-provenance/dead-allocation values. No exposure-time fact is reconstructed. -/
structure PointerInstance where
  allocation : AllocId
  value : Pointer Provenance
  grant : UniIndex

structure Loan where
  pointer : Nat
  parent : Option Nat
  depth : Nat

structure Interpretation where
  precise : Array (AllocId × PreciseAllocation)
  pointers : Array PointerInstance
  loans : Array Loan
  content : CandidateFreezeContentResources.Fragment

/-- A fixed pointer-origin assignment; concrete tags cannot be replaced.
Wildcard origins must be actually exposed in the named allocation. -/
def PointerBinds (allocation : Allocation Provenance BorrowTree) (pointer : PointerInstance) : Prop :=
  ∃ node, allocation.extra.nodes.get pointer.grant = some node ∧
    allocation.extra.tagMapping.get node.tag = some pointer.grant ∧
    match pointer.value.provenance with
    | .concrete id tag => id = pointer.allocation ∧ tag = node.tag
    | .wildcard => node.isExposed = true

/-- Active contents use local rights on completed ancestry and foreign rights
elsewhere. Cell is not a duplicable Freeze-content mode: actual Cell states
remain possible in the permission tables for ambient grants. -/
def LoanRights (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (precise : PreciseAllocation) (pointer : PointerInstance) (byte : Nat)
    (mode : CandidateFreezeContentResources.Mode) : Prop :=
  ∀ index node, allocation.extra.nodes.get index = some node →
    (Below precise.completion index pointer.grant →
      Allows (PreciseState precise byte index) (held.contains node.tag)
        (if mode = .read then .Read else .Write) .LocalAccess) ∧
    (¬ Below precise.completion index pointer.grant →
      Allows (PreciseState precise byte index) (held.contains node.tag)
        (if mode = .read then .Read else .Write) .ForeignAccess)

/-- Entirely current data: exact lookup coverage, fixed origins, finite loan
links, compatible byte resources and raw/precise scalar constraints. This is
NOT a faithful-realization theorem. Suspended content demands no active right. -/
def Interprets (world : World) (held : ProtectedTags) (interpretation : Interpretation) : Prop :=
  (world.toList.map Prod.fst).Nodup ∧
  (interpretation.precise.toList.map Prod.fst).Nodup ∧
  (∀ id allocation, Present world id allocation →
    ∃ precise, (id, precise) ∈ interpretation.precise.toList ∧ Refines allocation held precise) ∧
  (∀ id precise, (id, precise) ∈ interpretation.precise.toList →
    ∃ allocation, Present world id allocation ∧ Refines allocation held precise) ∧
  (∀ pointer ∈ interpretation.pointers.toList, ∃ allocation,
    Present world pointer.allocation allocation ∧ PointerBinds allocation pointer) ∧
  CandidateFreezeContentResources.Valid interpretation.content ∧
  (∀ (owner : Nat) (loan : Loan), interpretation.loans[owner]? = some loan →
    (∃ pointer, interpretation.pointers[loan.pointer]? = some pointer) ∧
    ∀ parent, loan.parent = some parent → ∃ (earlier : Loan),
      interpretation.loans[parent]? = some earlier ∧ earlier.depth < loan.depth) ∧
  (∀ byte owner charge, interpretation.content byte owner = some charge →
    ∃ loan pointer allocation precise,
      interpretation.loans[owner]? = some loan ∧
      interpretation.pointers[loan.pointer]? = some pointer ∧ pointer.allocation = byte.1 ∧
      Present world byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1, precise) ∈ interpretation.precise.toList ∧
      (charge.role = .active → LoanRights allocation held precise pointer byte.2 charge.mode) ∧
      (∀ parent, loan.parent = some parent →
        ∃ parentLoan parentInstance,
          interpretation.loans[parent]? = some parentLoan ∧
          interpretation.pointers[parentLoan.pointer]? = some parentInstance ∧
          parentInstance.allocation = byte.1 ∧
          Below precise.completion parentInstance.grant pointer.grant ∧
          ∃ parentCharge, interpretation.content byte parent = some parentCharge ∧
            parentCharge.role = .suspended ∧ CandidateFreezeContentResources.MayDelegate parentCharge.mode charge.mode))

/-- Allocation-ID footprints distinguish equal offsets in different allocations. -/
def Window (id : AllocId) (offset length : Nat) (byte : CandidateFreezeContentResources.Byte) : Prop :=
  byte.1 = id ∧ offset ≤ byte.2 ∧ byte.2 < offset + length

structure CallLoans where
  sourceOwner : Nat
  returnOwner : Nat
  sourceId : AllocId
  sourceOffset : Nat
  length : Nat
  returnId : AllocId
  returnOffset : Nat

/-- Empty source footprint is empty; return remains one byte. Distinct owners
are ABI-role identities, not a requirement that the underlying tags differ.
The two footprints are not assumed disjoint: resource validity must imply it. -/
def Claims (interpretation : Interpretation) (call : CallLoans) : Prop :=
  call.sourceOwner ≠ call.returnOwner ∧
  (∀ byte, interpretation.content byte call.sourceOwner = some ⟨.mut, .active⟩ ↔
    Window call.sourceId call.sourceOffset call.length byte) ∧
  (∀ byte, interpretation.content byte call.returnOwner = some ⟨.ret, .active⟩ ↔
    Window call.returnId call.returnOffset 1 byte)

/-- Stable existential candidate, UNADOPTED. No universal quantification over
all syntactic attachment choices, and no fresh per-access or per-byte origins. -/
def ProposedStableOwnership (world : World) (held : ProtectedTags) (call : CallLoans) : Prop :=
  ∃ interpretation, Interprets world held interpretation ∧ Claims interpretation call

/-! Remaining bindings are deliberately NOT packaged into a fake full-input
predicate: world ↔ actual Before live allocations; global protectors ↔ frames;
pointer instances ↔ argument/return bits and copy identity; cached address/base
resolution; nonnull empty values; positive initialized u8 storage and writable
return storage; fixed compiler/configuration, metadata, resources and harness.
Then candidate coverage and its implication to the existing ConsistentContract
must be proved or revised. There is NO GoalImplication theorem/axiom here.
In particular pointwise Refines is not claimed to preserve correlated choices.
-/
end DuplicatePrefix.CandidateStableCallOwnership

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateStableCallOwnership." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved candidate ownership dependency {dependency}"
