import duplicate_prefix.OrdinaryBorrowAuthority
import duplicate_prefix.DuplicatePrefixScalarAuthorization

namespace DuplicatePrefix.OrdinaryBorrowAuthorityBridge
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open OrdinaryBorrowAuthority GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false

/-- The raw ancestor clause implies the existing exact scalar tables for both
access kinds. No successful transition is a premise. -/
theorem local_scalar (state : LocationState) (held : Bool)
    (raw : LocalWrite state held) (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible state kind .LocalAccess held := by
  cases kind with
  | Read => exact ⟨raw.1, raw.2.1⟩
  | Write => exact raw

/-- An active protected competitor tolerated by the raw clause must be Cell,
so it satisfies both exact scalar tables. This does not cover inactive loans. -/
theorem active_foreign_scalar (state : LocationState) (held : Bool)
    (active : ActiveProtected state held) (raw : ForeignWrite state held)
    (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible state kind .ForeignAccess held := by
  have cell : state.permission = .Cell := by
    rcases raw.2 active.1 with cell | dormant
    · exact cell
    · have impossible := active.2.1.symm.trans dormant.2
      cases impossible
  cases kind with
  | Write => exact raw
  | Read =>
    exact ⟨raw.1, by intro _; simp [cell]⟩

/-- Explicit byte representation consistency, separate from mutable authority.
`possible` excludes lazy Unique (LocationState.lean:64-67). Protected ReservedIM
is excluded by pinned perms.rs:97-103,116-117,164-168. Active protected Disabled
is excluded by the protector check in LocationState.performAccess (the pinned
tree.rs:157-158 perform_access check of initialized/protected disabling transitions).
These are call-time data clauses; no caller-history construction is asserted. -/
def Representation (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) : Prop :=
  ∀ index node, tree.nodes.get index = some node →
    let state := (location.perms.get index).getD node.defaultLocationState
    state.possible = true ∧
      (protections.contains node.tag = true → state.permission ≠ .ReservedIM) ∧
      (protections.contains node.tag = true → state.permission = .Disabled → state.accessed = false)

/-- The previously omitted inactive/Disabled cases follow from explicit
representation clauses. Active live competitors are governed by authority. -/
theorem foreign_scalar (state : LocationState) (held : Bool)
    (possible : state.possible = true)
    (noIM : held = true → state.permission ≠ .ReservedIM)
    (disabled : held = true → state.permission = .Disabled → state.accessed = false)
    (authority : ActiveProtected state held → ForeignWrite state held)
    (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible state kind .ForeignAccess held := by
  by_cases active : ActiveProtected state held
  · exact active_foreign_scalar state held active (authority active) kind
  have dormant : held = true → state.accessed = false := by
    intro heldTrue
    by_cases dead : state.permission = .Disabled
    · exact disabled heldTrue dead
    · cases accessed : state.accessed with
      | false => rfl
      | true => exact False.elim (active ⟨heldTrue,accessed,dead⟩)
  cases kind with
  | Write => exact ⟨possible,fun heldTrue => Or.inr ⟨noIM heldTrue,dormant heldTrue⟩⟩
  | Read =>
    refine ⟨possible,fun heldTrue => ⟨?_,noIM heldTrue,disabled heldTrue⟩⟩
    intro unique
    have impossible := possible
    simp [LocationState.possible,unique,dormant heldTrue,Permission.isUnique] at impossible

/-- Exact scalar permissions on every off-ancestry byte of the same physical
component, including dormant heldTrue grants. Projection/topology and other
physical roots are not supplied by this theorem. -/
theorem concrete_foreign_scalars (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (tag : BorTag)
    (raw : ConcreteComponentAuthority tree location protections tag)
    (representation : Representation tree location protections) :
    ∃ anchor, tree.tagMapping.get tag = some anchor ∧
      ∀ index competitor, tree.nodes.get index = some competitor →
        SameComponent tree anchor index → ¬ Ancestor tree index anchor →
        ∀ kind, DuplicatePrefixScalarAuthorization.Compatible
          ((location.perms.get index).getD competitor.defaultLocationState) kind .ForeignAccess
          (protections.contains competitor.tag) := by
  obtain ⟨anchor,node,mapped,_,_,_,foreign⟩ := raw
  refine ⟨anchor,mapped,?_⟩
  intro index competitor present component unrelated kind
  obtain ⟨possible,noIM,disabled⟩ := representation index competitor present
  exact foreign_scalar _ _ possible noIM disabled
    (foreign index competitor present component unrelated) kind

/-- Direct extraction of exact scalar authorization along the raw physical
ancestor chain. The grant is the actual tag-mapped node, not a chosen cache root.
Connecting physical paths to projected Normal support remains separate. -/
theorem concrete_ancestor_scalars (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (tag : BorTag)
    (raw : ConcreteComponentAuthority tree location protections tag) :
    ∃ anchor node, tree.tagMapping.get tag = some anchor ∧
      tree.nodes.get anchor = some node ∧ node.tag = tag ∧
      ∀ index ancestor, tree.nodes.get index = some ancestor → Ancestor tree index anchor →
        ∀ kind, DuplicatePrefixScalarAuthorization.Compatible
          ((location.perms.get index).getD ancestor.defaultLocationState) kind .LocalAccess
          (protections.contains ancestor.tag) := by
  obtain ⟨anchor,node,mapped,present,tagged,ancestors,_⟩ := raw
  exact ⟨anchor,node,mapped,present,tagged,fun index ancestor present path kind =>
    local_scalar _ _ (ancestors index ancestor present path) kind⟩

end DuplicatePrefix.OrdinaryBorrowAuthorityBridge
