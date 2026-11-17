import duplicate_prefix.CurrentCallSpatialSourceCover
import duplicate_prefix.CurrentCallResourceInstallation
import duplicate_prefix.CandidateCurrentGrantRuntime

/-! Source-only transport of the OLD concrete family after an unprotected
shared-reader constructor and associated Read. The actual producer supplies
current presence and metadata; every retained cell uses its fixed extension.
This is a technical mutable parent bank before any future Strong protection,
not simultaneous ownership of independent source/observer content fragments. -/
namespace DuplicatePrefix.CurrentCallSpatialSharedCover
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]

variable {before tracker ctx offset length}
    (role : RoleCover before tracker ctx .mut offset length)
    {post : Before} {next : MachineHooks.BorrowState} {tree : BorrowTree}
    {tag : BorTag} {parent reader : UniIndex}

/-- Concrete binding fixes the OLD grant; it does not identify whole cell
views or choose one completion for the source window. -/
theorem grant_eq (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (tagged : role.backing.allocation.extra.indexOfTag tag=some parent)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) :
    (role.roles i overlap).grant=parent := by
  obtain ⟨node,nodeAt,mapping,value⟩ := (role.roles i overlap).binding
  change (match role.family.value.provenance with
    | .concrete id tag=>id=role.family.allocation ∧tag=node.tag
    | .wildcard=>node.isExposed=true) at value
  rw [concrete] at value
  have mapped : role.backing.allocation.extra.indexOfTag tag=some (role.roles i overlap).grant := by
    change role.backing.allocation.extra.tagMapping.get tag=some (role.roles i overlap).grant
    rw [value.2]
    exact mapping
  exact Option.some.inj (mapped.symm.trans tagged)

/-- All metadata are about the actual installed allocation. The OLD family
and cell geometry stay fixed; only the explicit common observer edge is added.
Raw row certificates cover request/cell intersections, never unrelated bytes. -/
def updates
    (live : Present (ActualWorld post) role.backing.id (role.backing.allocation.setExtra tree))
    (rootTag : next.global.rootTag? role.backing.id=tracker.global.rootTag? role.backing.id)
    (capacity : tree.locations.size=role.backing.allocation.extra.locations.size)
    (roots : ∀ (position : Nat) (root : UniIndex),role.backing.allocation.extra.roots[position]?=some root→tree.roots[position]?=some root)
    (metadata : ∀ index node,role.backing.allocation.extra.nodes.get index=some node→
      ∃changed,tree.nodes.get index=some changed ∧changed.tag=node.tag ∧changed.parent=node.parent ∧
        changed.isExposed=node.isExposed ∧changed.defaultInitialPermission=node.defaultInitialPermission)
    (vacant : role.backing.allocation.extra.nodes.get reader=none)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree next.global)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (tagged : role.backing.allocation.extra.indexOfTag tag=some parent)
    (cells : ∀(i : Fin role.backing.cells.size) (_overlap : CurrentCallSpatialSourceCover.Active role i)
      (lower upper : UInt64),offset≤lower.toNat→upper.toNat≤offset+length→
      role.backing.cells[i].offset≤lower.toNat→upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length→
      ParentInterpretation tree (extend role.backing.cells[i].completion reader parent) ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority tree (extend role.backing.cells[i].completion reader parent)
        next.global.protectedTags parent) lower upper tree.locations)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) :
    CurrentCallSpatialSourceCover.Update role post next (role.backing.allocation.setExtra tree) role.family parent i overlap := by
  classical
  have sameGrant := grant_eq role concrete tagged i overlap
  have atByte (byte : AllocId×Nat) (request : Window role.backing.id offset length byte)
      (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte) :
      ParentInterpretation tree (extend role.backing.cells[i].completion reader parent) ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority tree (extend role.backing.cells[i].completion reader parent)
        next.global.protectedTags parent) (UInt64.ofNat byte.2) (UInt64.ofNat (byte.2+1)) tree.locations := by
    have bound := ((role.roles i overlap).available byte request cell).1
    rw [(role.roles i overlap).issued.capability.extent] at bound
    have sizeFit := role.backing.allocation.byteSize.bytes.toNat_lt
    have fit : byte.2+1<2^64 := by omega
    have lowerEq : (UInt64.ofNat byte.2).toNat=byte.2 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : byte.2<2^64)]
    have upperEq : (UInt64.ofNat (byte.2+1)).toNat=byte.2+1 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fit]
    exact cells i overlap _ _ (by rw [lowerEq];exact request.2.1) (by rw [upperEq];have := request.2.2;omega)
      (by rw [lowerEq];exact cell.2.1) (by rw [upperEq];have := cell.2.2;omega)
  let witness := Classical.choose overlap
  have witnessRequest := (Classical.choose_spec overlap).1
  have witnessCell := (Classical.choose_spec overlap).2
  let parents := (atByte witness witnessRequest witnessCell).1
  refine ⟨⟨role.backing.cells[i].offset,role.backing.cells[i].length,
    extend role.backing.cells[i].completion reader parent,parents⟩,rfl,rfl,?_,?_,?_⟩
  · obtain ⟨node,nodeAt,mapping,value⟩ := (role.roles i overlap).binding
    rw [sameGrant] at nodeAt
    obtain ⟨changed,changedAt,changedTag,_,changedExposure,_⟩ := metadata parent node nodeAt
    refine ⟨changed,changedAt,runtime.formed.allocator.nodeTags _ _ changedAt,?_⟩
    change (match role.family.value.provenance with
      | .concrete id tag=>id=role.family.allocation ∧tag=changed.tag
      | .wildcard=>changed.isExposed=true)
    change (match role.family.value.provenance with
      | .concrete id tag=>id=role.family.allocation ∧tag=node.tag
      | .wildcard=>node.isExposed=true) at value
    rw [concrete] at value ⊢
    exact ⟨value.1,value.2.trans changedTag.symm⟩
  · have issued := CurrentCallResourceInstallation.spatial (role.roles i overlap).issued
      role.backing.cells[i].parents post next tree live rootTag capacity roots metadata reader parent vacant
    simpa only [sameGrant] using issued
  · intro point request cell
    refine ⟨((role.roles i overlap).available point request cell).1,?_⟩
    have owned := (atByte point request cell).2
    intro segment member lower upper index node nodeAt
    simp only [Allocation.setExtra,Allocation.mapExtra] at member lower upper nodeAt ⊢
    obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have bound := ((role.roles i overlap).available point request cell).1
    rw [(role.roles i overlap).issued.capability.extent] at bound
    have sizeFit := role.backing.allocation.byteSize.bytes.toNat_lt
    have fit : point.2+1<2^64 := by omega
    have lowerEq : (UInt64.ofNat point.2).toNat=point.2 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : point.2<2^64)]
    have upperEq : (UInt64.ofNat (point.2+1)).toNat=point.2+1 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fit]
    have rights := owned position valid (by omega) (by rw [upperEq];omega) (by rw [lowerEq];omega) index node nodeAt
    have realized := CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node nodeAt)
      ((runtime.formed.profile position valid).present index node nodeAt)
    constructor
    · intro below
      exact local_token _ _ realized (rights.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact foreign_no_clash _ _ realized (rights.2 outside) clash

end
end DuplicatePrefix.CurrentCallSpatialSharedCover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialSharedCover" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial shared cover dependency {dependency}"
