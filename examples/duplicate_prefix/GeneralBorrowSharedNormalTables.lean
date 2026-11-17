import duplicate_prefix.GeneralBorrowFreshNormalComponent
import duplicate_prefix.DuplicatePrefixConstructorNormalShape
namespace DuplicatePrefix.GeneralBorrowSharedNormalTables
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNormalComponent GeneralBorrowSharedNormalRelations
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- One operation's raw exact normal permission table. This internal helper
also represents the shared source's Read-only table. -/
def Table (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind) (support : Nat → Prop) : Prop :=
  ∀ index, support index → index < tree.topology.nodes.size → ∃ state, tree.stateAt index = some state ∧
    DuplicatePrefixScalarAuthorization.Compatible state kind (GeneralBorrowAnchor.relation tree anchor index)
      (tree.protectedNodes.contains index)

/-- Raw projected state/protector facts of inside shared materialization.
Every field is a lookup/topology fact, never an operation-success certificate. -/
structure Extension (before after : NormalTreeState) (parent child : Nat) : Prop where
  patch : Patch before.topology after.topology parent child
  paths : GeneralBorrowFreshSharedPaths.Attach before.topology after.topology parent child
  oldValid : ∀ index, index < after.topology.nodes.size → index ≠ child → index < before.topology.nodes.size
  oldState : ∀ index, index < before.topology.nodes.size → index ≠ child → after.stateAt index = before.stateAt index
  newState : after.stateAt child = some GeneralBorrowFreshAnchor.sharedState
  oldProtected : ∀ index, index < before.topology.nodes.size → index ≠ child → after.protectedNodes.contains index = before.protectedNodes.contains index
  freshUnprotected : after.protectedNodes.contains child = false

/-- Exact Read table extension to the new Frozen shared source. -/
theorem child_read (before after : NormalTreeState) (parent child : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology parent)
    (extension : Extension before after parent child)
    (permissions : Table before parent .Read old.support) :
    Table after child .Read (extended old.support child) := by
  intro index included valid
  by_cases fresh : index = child
  · subst index
    refine ⟨GeneralBorrowFreshAnchor.sharedState,extension.newState,?_⟩
    rw [child_self]
    exact DuplicatePrefixConstructorNormalShape.shared_local_read _
  · have oldValid := extension.oldValid index valid fresh
    obtain ⟨state,present,compatible⟩ := permissions index (included.resolve_left fresh) oldValid
    refine ⟨state,(extension.oldState index oldValid fresh).trans present,?_⟩
    rw [child_old before after parent child index extension.paths fresh,extension.oldProtected index oldValid fresh]
    exact compatible

/-- The original mutable source retains its exact table for BOTH kinds;
the new unprotected shared child is foreign and otherwise no table changes. -/
theorem original (before after : NormalTreeState) (parent child : Nat) (kind : AccessKind)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology parent)
    (extension : Extension before after parent child)
    (permissions : Table before parent kind old.support) :
    Table after parent kind (extended old.support child) := by
  intro index included valid
  by_cases fresh : index = child
  · subst index
    refine ⟨GeneralBorrowFreshAnchor.sharedState,extension.newState,?_⟩
    rw [original_child_foreign before after parent child parent extension.paths extension.paths.parentValid extension.paths.parentDifferent,
      extension.freshUnprotected]
    exact DuplicatePrefixConstructorNormalShape.shared_foreign_both kind
  · have oldValid := extension.oldValid index valid fresh
    obtain ⟨state,present,compatible⟩ := permissions index (included.resolve_left fresh) oldValid
    refine ⟨state,(extension.oldState index oldValid fresh).trans present,?_⟩
    rw [GeneralBorrowSharedNormalRelations.original before after parent child parent index extension.paths extension.paths.parentValid extension.paths.parentDifferent,
      extension.oldProtected index oldValid fresh]
    exact compatible

/-- Data-only component and exact permission outputs are explicitly coupled. -/
theorem certificates (before after : NormalTreeState) (parent child : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology parent)
    (extension : Extension before after parent child)
    (permissions : ∀ kind, Table before parent kind old.support) :
    ∃ original : GeneralBorrowExposedScopedNormal.Component after.topology parent,
      ∃ shared : GeneralBorrowExposedScopedNormal.Component after.topology child,
        original.support = extended old.support child ∧ shared.support = extended old.support child ∧
        (∀ kind, Table after parent kind original.support) ∧ Table after child .Read shared.support := by
  let original := component before.topology after.topology parent child old extension.patch parent (.inl rfl)
  let shared := component before.topology after.topology parent child old extension.patch child (.inr rfl)
  exact ⟨original,shared,rfl,rfl,(fun kind => GeneralBorrowSharedNormalTables.original before after parent child kind old extension (permissions kind)),
    child_read before after parent child old extension (permissions .Read)⟩

end DuplicatePrefix.GeneralBorrowSharedNormalTables
