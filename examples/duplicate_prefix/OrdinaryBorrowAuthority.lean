import duplicate_prefix.GeneralBorrowExposedNonleafPrimaryPath

namespace DuplicatePrefix.OrdinaryBorrowAuthority
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false

/-- Raw permission for mutable use through this tag or its descendants.
This records the pinned child-Write permission/protector table. It does not
assert that the tag is the provenance of a reference or that aliases agree. -/
def LocalWrite (state : LocationState) (held : Bool) : Prop :=
  state.possible = true ∧ state.permission ≠ .Disabled ∧ state.permission ≠ .Frozen ∧
    (held = true → state.permission ≠ .ReservedFrz true)

/-- Raw obligation of a competing grant when mutable authority is exercised
outside its ancestry. Unprotected aliases may be invalidated; protected Cell
and dormant non-ReservedIM grants do not obstruct this authority. -/
def ForeignWrite (state : LocationState) (held : Bool) : Prop :=
  state.possible = true ∧ (held = true → state.permission = .Cell ∨
    (state.permission ≠ .ReservedIM ∧ state.accessed = false))

/-- An active protected grant carries an accessed, non-Disabled byte, rather
than a dead permission or a lazy outside-range permission. -/
def ActiveProtected (state : LocationState) (held : Bool) : Prop :=
  held = true ∧ state.accessed = true ∧ state.permission ≠ .Disabled

/-- Actual physical ancestry, independent of cached paths or exposed counts. -/
def Ancestor (tree : BorrowTree) (ancestor grant : UniIndex) : Prop :=
  Path tree ancestor grant

/-- Membership in the same physical tree, without choosing a cached root. -/
def SameComponent (tree : BorrowTree) (first second : UniIndex) : Prop :=
  ∃ root, Path tree root first ∧ Path tree root second

/-- Concrete authority INSIDE the named tag's physical component, at one byte.
The pointer's actual tag determines the grant. Its ancestors are usable local
Write authority; an active protected grant off that ancestry must tolerate a
foreign Write. Unprotected aliases and inactive loans are not excluded.

This is a raw component clause, NOT complete reference validity. Representation
WF must separately exclude impossible protected ReservedIM states and supply
actual pointer/allocation identity. Cross-root obligations are SPEC OPEN below.
No cache, callback counts, residual sets or execution result occurs here. -/
def ConcreteComponentAuthority (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (tag : BorTag) : Prop :=
  ∃ anchor node, tree.tagMapping.get tag = some anchor ∧
    tree.nodes.get anchor = some node ∧ node.tag = tag ∧
    (∀ index ancestor, tree.nodes.get index = some ancestor → Ancestor tree index anchor →
      LocalWrite ((location.perms.get index).getD ancestor.defaultLocationState)
        (protections.contains ancestor.tag)) ∧
    (∀ index competitor, tree.nodes.get index = some competitor → SameComponent tree anchor index →
      ¬ Ancestor tree index anchor →
      ActiveProtected ((location.perms.get index).getD competitor.defaultLocationState)
        (protections.contains competitor.tag) →
      ForeignWrite ((location.perms.get index).getD competitor.defaultLocationState)
        (protections.contains competitor.tag))

/-- An exposed physical provenance grant available at this byte has usable
concrete authority through its real ancestor chain. Exposure of a syntactic
node alone does not make its latent permissions below a barrier available.
The grant witness may vary with the byte; no global selected root is required.

This is only the justified physical-grant clause. It is NOT a complete wildcard
authority predicate: compatibility between grants in distinct physical roots
and the allocation's virtual-origin alternatives remains SPEC OPEN. -/
def AvailableExposedPhysicalGrant (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (tag : BorTag) : Prop :=
  ConcreteComponentAuthority tree location protections tag ∧
    ∃ index node, tree.tagMapping.get tag = some index ∧
      tree.nodes.get index = some node ∧ node.tag = tag ∧ node.isExposed = true

/-! SPEC OPEN: `newChild` with wildcard provenance installs a parentless node;
TreeNode retains no chosen exposed-origin edge. A physical ancestor relation
therefore cannot recover a unique cross-root origin family. The raw denotation
must explain multiple exposed origins, newer competing grants and their actual
selected-physical-root tag bound, while admitting latent inaccessible rows.
Neither a ghost relation nor an opaque proposition is introduced here to hide
this missing clause. These definitions establish no whole-call domain theorem.
-/

end DuplicatePrefix.OrdinaryBorrowAuthority
