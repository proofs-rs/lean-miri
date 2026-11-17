import duplicate_prefix.GeneralBorrowFreshNormalComponent
import duplicate_prefix.GeneralBorrowFreshChild
import duplicate_prefix.DuplicatePrefixDefaultConstructorNormalShape
namespace DuplicatePrefix.GeneralBorrowProtectedNormalTables
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNormalComponent GeneralBorrowSharedNormalRelations
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- One operation's raw exact normal permission table. This internal helper
also represents the mutable source's Both table. -/
def Table (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind) (support : Nat → Prop) : Prop :=
  ∀ index, support index → index < tree.topology.nodes.size → ∃ state, tree.stateAt index = some state ∧
    DuplicatePrefixScalarAuthorization.Compatible state kind (GeneralBorrowAnchor.relation tree anchor index)
      (tree.protectedNodes.contains index)

/-- Raw projected state/protector facts of inside mutable materialization.
Every field is a lookup/topology fact, never an operation-success certificate. -/
structure Extension (before after : NormalTreeState) (parent child : Nat) : Prop where
  patch : Patch before.topology after.topology parent child
  paths : GeneralBorrowFreshSharedPaths.Attach before.topology after.topology parent child
  oldValid : ∀ index, index < after.topology.nodes.size → index ≠ child → index < before.topology.nodes.size
  oldState : ∀ index, index < before.topology.nodes.size → index ≠ child → after.stateAt index = before.stateAt index
  newState : after.stateAt child = some GeneralBorrowFreshChild.inside
  oldProtected : ∀ index, index < before.topology.nodes.size → index ≠ child → after.protectedNodes.contains index = before.protectedNodes.contains index
  freshProtected : after.protectedNodes.contains child = true

/-- Exact per-kind table extension to the protected mutable reservation. -/
theorem child (before after : NormalTreeState) (parent child : Nat) (kind : AccessKind)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology parent)
    (extension : Extension before after parent child)
    (permissions : Table before parent kind old.support) :
    Table after child kind (extended old.support child) := by
  intro index included valid
  by_cases fresh : index = child
  · subst index
    refine ⟨GeneralBorrowFreshChild.inside,extension.newState,?_⟩
    rw [child_self,extension.freshProtected]
    cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowFreshChild.inside,LocationState.possible]
  · have oldValid := extension.oldValid index valid fresh
    obtain ⟨state,present,compatible⟩ := permissions index (included.resolve_left fresh) oldValid
    refine ⟨state,(extension.oldState index oldValid fresh).trans present,?_⟩
    rw [child_old before after parent child index extension.paths fresh,extension.oldProtected index oldValid fresh]
    exact compatible

/-- Actual fresh-child component with its exact Both table. -/
theorem certificate (before after : NormalTreeState) (parent child : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology parent)
    (extension : Extension before after parent child)
    (permissions : ∀ kind, Table before parent kind old.support) :
    ∃ current : GeneralBorrowExposedScopedNormal.Component after.topology child,
      ∀ kind, Table after child kind current.support := by
  let current := component before.topology after.topology parent child old extension.patch child (.inr rfl)
  exact ⟨current,fun kind => GeneralBorrowProtectedNormalTables.child before after parent child kind old extension (permissions kind)⟩
end DuplicatePrefix.GeneralBorrowProtectedNormalTables
