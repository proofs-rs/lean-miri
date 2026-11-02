import duplicate_prefix.OrdinaryBorrowAuthority
import duplicate_prefix.GeneralBorrowFreshChild
import duplicate_prefix.GeneralBorrowWildcardParentTagOrder

namespace DuplicatePrefix.OrdinaryJointAliasBoundary
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open OrdinaryBorrowAuthority
set_option autoImplicit false

/-- The pinned foreign-Write table cannot tolerate an accessed, protected
non-Cell grant. This is a contradiction between raw permission clauses,
not an assumption that any Write executes successfully. -/
theorem active_noncell_incompatible (state : LocationState) (held : Bool)
    (active : ActiveProtected state held) (noncell : state.permission ≠ .Cell) :
    ¬ ForeignWrite state held := by
  intro authority
  rcases authority.2 active.1 with cell | dormant
  · exact noncell cell
  · have impossible := active.2.1.symm.trans dormant.2
    cases impossible

/-- The actual mutable FnEntry inside profile is accessed and non-Cell.
Its protection must be supplied by the separately tracked call-frame tags. -/
theorem fresh_inside_incompatible : ¬ ForeignWrite GeneralBorrowFreshChild.inside true := by
  exact active_noncell_incompatible _ _ ⟨rfl,rfl,by decide⟩ (by decide)

/-- A concrete return grant's raw Write authority excludes an overlapping
active protected non-Cell source grant off its ancestry, in the same physical
component. `locations` and the topology/protector data describe one explicit
projected state: no transition, callback success, or final authority is assumed.

The joint semantic obligation is `returnAuthority` in that SAME state, together
with the source grant's activity/protection and off-ancestry fact. Deriving
these jointly from a pre-call ordinary domain remains a separate obligation.
Physical slice/destination validity alone supplies none of that authority.
The theorem does not cover wildcard cross-root origin selection. -/
theorem concrete_disjoint
    (tree : BorrowTree) (locations : Nat → LocationTree) (protections : ProtectedTags)
    (source returnGrant : UniIndex) (sourceNode : TreeNode) (returnTag : BorTag)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (returnMapped : tree.tagMapping.get returnTag = some returnGrant)
    (component : SameComponent tree returnGrant source)
    (offAncestry : ¬ Ancestor tree source returnGrant)
    (sourceOffset sourceLength destination : Nat)
    (sourceProfile : ∀ byte, sourceOffset ≤ byte → byte < sourceOffset+sourceLength →
      let state := ((locations byte).perms.get source).getD sourceNode.defaultLocationState
      ActiveProtected state (protections.contains sourceNode.tag) ∧ state.permission ≠ .Cell)
    (returnAuthority : ConcreteComponentAuthority tree (locations destination) protections returnTag) :
    sourceOffset+sourceLength ≤ destination ∨ destination+1 ≤ sourceOffset := by
  by_cases overlap : sourceOffset ≤ destination ∧ destination < sourceOffset+sourceLength
  · obtain ⟨anchor,node,mapped,_present,_tag,_local,foreign⟩ := returnAuthority
    have same : anchor = returnGrant := Option.some.inj (mapped.symm.trans returnMapped)
    subst anchor
    obtain ⟨active,noncell⟩ := sourceProfile destination overlap.1 overlap.2
    exact False.elim (active_noncell_incompatible _ _ active noncell
      (foreign source sourceNode sourcePresent component offAncestry active))
  · omega

/-- Specialization to the literal inside state installed for protected mutable
FnEntry. The caller supplies its current projection equation and the raw
return grant authority, rather than any successful retag/uninit equation. -/
theorem fresh_concrete_disjoint
    (tree : BorrowTree) (locations : Nat → LocationTree) (protections : ProtectedTags)
    (source returnGrant : UniIndex) (sourceNode : TreeNode) (returnTag : BorTag)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (returnMapped : tree.tagMapping.get returnTag = some returnGrant)
    (held : protections.contains sourceNode.tag = true)
    (component : SameComponent tree returnGrant source)
    (offAncestry : ¬ Ancestor tree source returnGrant)
    (sourceOffset sourceLength destination : Nat)
    (sourceInside : ∀ byte, sourceOffset ≤ byte → byte < sourceOffset+sourceLength →
      ((locations byte).perms.get source).getD sourceNode.defaultLocationState = GeneralBorrowFreshChild.inside)
    (returnAuthority : ConcreteComponentAuthority tree (locations destination) protections returnTag) :
    sourceOffset+sourceLength ≤ destination ∨ destination+1 ≤ sourceOffset := by
  apply concrete_disjoint tree locations protections source returnGrant sourceNode returnTag
    sourcePresent returnMapped component offAncestry sourceOffset sourceLength destination _ returnAuthority
  intro byte lower upper
  rw [sourceInside byte lower upper,held]
  exact ⟨⟨rfl,rfl,by decide⟩,by decide⟩

/-- Same-allocation byte exclusion gives the exact numeric address alternatives
used by Contract.separated after pointer/base binding is substituted. A common
base and nonwrapping addresses are explicit; distinct allocations require a
separate managed-address interval invariant. No different-allocation rule is
inferred merely from allocation identity. -/
theorem address_separated (base sourceOffset sourceLength destination : UInt64)
    (sourceFits : base.toNat+sourceOffset.toNat < 2^64)
    (destinationFits : base.toNat+destination.toNat < 2^64)
    (disjoint : sourceOffset.toNat+sourceLength.toNat ≤ destination.toNat ∨
      destination.toNat+1 ≤ sourceOffset.toNat) :
    (base+sourceOffset).toNat+sourceLength.toNat ≤ (base+destination).toNat ∨
      (base+destination).toNat+1 ≤ (base+sourceOffset).toNat := by
  rw [UInt64.toNat_add,UInt64.toNat_add,Nat.mod_eq_of_lt sourceFits,Nat.mod_eq_of_lt destinationFits]
  omega


/-- Direct Contract.separated-shaped bridge for one common allocation/base.
The unresolved semantic input is raw joint return authority at the explicit
source-protector projection, not a successful uninit or a final Write result.
Parent-tag order and the fresh source tag eliminate a separate ancestry premise. -/
theorem fresh_call_separated
    (tree : BorrowTree) (locations : Nat → LocationTree) (protections : ProtectedTags)
    (source returnGrant : UniIndex) (sourceNode : TreeNode) (returnTag : BorTag)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (returnMapped : tree.tagMapping.get returnTag = some returnGrant)
    (held : protections.contains sourceNode.tag = true)
    (component : SameComponent tree returnGrant source)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (newer : returnTag.value < sourceNode.tag.value)
    (base sourceOffset sourceLength destination sourceAddress destinationAddress : UInt64)
    (sourceBinding : sourceAddress = base+sourceOffset)
    (destinationBinding : destinationAddress = base+destination)
    (sourceFits : base.toNat+sourceOffset.toNat < 2^64)
    (destinationFits : base.toNat+destination.toNat < 2^64)
    (sourceInside : ∀ byte, sourceOffset.toNat ≤ byte → byte < sourceOffset.toNat+sourceLength.toNat →
      ((locations byte).perms.get source).getD sourceNode.defaultLocationState = GeneralBorrowFreshChild.inside)
    (returnAuthority : ConcreteComponentAuthority tree (locations destination.toNat) protections returnTag) :
    sourceLength = 0 ∨ sourceAddress.toNat+sourceLength.toNat ≤ destinationAddress.toNat ∨
      destinationAddress.toNat+1 ≤ sourceAddress.toNat := by
  have rawAuthority := returnAuthority
  obtain ⟨anchor,returnNode,mapped,returnPresent,returnSame,_⟩ := rawAuthority
  have anchorEq : anchor = returnGrant := Option.some.inj (mapped.symm.trans returnMapped)
  subst anchor
  have offAncestry : ¬ Ancestor tree source returnGrant := by
    intro path
    have ordered := GeneralBorrowWildcardParentTagOrder.path_tag_le tree order source returnGrant path
      sourceNode returnNode sourcePresent returnPresent
    rw [returnSame] at ordered
    have low := UInt64.le_iff_toNat_le.mp ordered
    have high := UInt64.lt_iff_toNat_lt.mp newer
    omega
  have disjoint := fresh_concrete_disjoint tree locations protections source returnGrant sourceNode returnTag
    sourcePresent returnMapped held component offAncestry sourceOffset.toNat sourceLength.toNat destination.toNat sourceInside returnAuthority
  apply Or.inr
  rw [sourceBinding,destinationBinding]
  exact address_separated base sourceOffset sourceLength destination sourceFits destinationFits disjoint

end DuplicatePrefix.OrdinaryJointAliasBoundary
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.OrdinaryJointAliasBoundary." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved joint alias boundary dependency {dependency}"
