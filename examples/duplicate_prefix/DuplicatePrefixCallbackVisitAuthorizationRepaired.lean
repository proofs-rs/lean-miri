import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorization
import duplicate_prefix.GeneralBorrowWildcardVirtualLeaf

/-! Source-aligned authorization for the postchildren guard's complete held-sensitive
Write no-op class. Old candidate definitions and theorem statements are
retained. These local rules are not
ordinary-input validity or an actual-call Result premise. -/
namespace DuplicatePrefix.DuplicatePrefixCallbackVisitAuthorizationRepaired
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackVisitAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Exactly the additional source branch, on the CURRENT postchildren state. -/
def PostchildrenNoop (state : LocationState) (kind : AccessKind) (held : Bool)
    (exit : Option WildcardAccessRelatedness) : Prop :=
  exit = some .ForeignAccess ∧
  state.foreignWriteNoop held = true ∧
  state.skipIfKnownNoop kind .ForeignAccess = .SkipSelfAndChildren

/-- Transparent data meaning of the shared core guard; no access outcome is
used to define eligibility. -/
theorem postchildren_noop_iff_data (state : LocationState) (kind : AccessKind) (held : Bool)
    (exit : Option WildcardAccessRelatedness) :
    PostchildrenNoop state kind held exit ↔
      exit = some .ForeignAccess ∧
      (state.permission = .Cell ∨
        (state.permission = .Disabled ∧ (held = false ∨ state.accessed = false)) ∨
        (state.permission = .ReservedIM ∧ held = false)) ∧
      state.skipIfKnownNoop kind .ForeignAccess = .SkipSelfAndChildren := by
  simp only [PostchildrenNoop,LocationState.foreignWriteNoop_iff]

def Authorized (state : LocationState) (kind : AccessKind) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness) : Prop :=
  DuplicatePrefixCallbackVisitAuthorization.Authorized state kind held entry exit ∨
    (state.possible = true ∧ PostchildrenNoop state kind held exit)

theorem old_inclusion (state : LocationState) (kind : AccessKind) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness)
    (old : DuplicatePrefixCallbackVisitAuthorization.Authorized state kind held entry exit) :
    Authorized state kind held entry exit := .inl old

/-- Three source outcomes, without assuming any operation succeeds. -/
inductive ExitAction (state : LocationState) (kind : AccessKind) (held : Bool)
    (exit : Option WildcardAccessRelatedness) : Prop
  | either (related : exit = some .EitherAccess)
  | noop (guard : PostchildrenNoop state kind held exit)
  | recorded (related : WildcardAccessRelatedness) (exact : AccessRelatedness)
      (recorded next : LocationState) (delta : PermTransition)
      (classification : exit = some related) (exactness : exactRelation related = some exact)
      (record : state.recordNewAccess kind exact = .Recorded recorded)
      (access : recorded.performAccess kind exact held = .Success next delta)

theorem exit_action (state : LocationState) (kind : AccessKind) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness)
    (authorized : Authorized state kind held entry exit)
    (notSkipped : entrySkip state kind entry = false) : ExitAction state kind held exit := by
  rcases authorized with old | repaired
  · obtain ⟨related,classification,either | ⟨exact,recorded,next,delta,exactness,record,access⟩⟩ :=
      exit_transition state kind held entry exit old notSkipped
    · exact .either (classification.trans (congrArg some either))
    · exact .recorded related exact recorded next delta classification exactness record access
  · exact .noop repaired.2

/-- The complete held-sensitive Write no-op class is exactly the core Boolean
branch, together with the CURRENT postchildren skip condition. -/
theorem guard_source (state : LocationState) (kind : AccessKind) (held : Bool)
    (guard : PostchildrenNoop state kind held (some .ForeignAccess)) :
    ((AccessRelatedness.ForeignAccess == .ForeignAccess) && state.foreignWriteNoop held &&
      (state.skipIfKnownNoop kind .ForeignAccess == .SkipSelfAndChildren)) = true := by
  simp [guard.2.1,guard.2.2]

/-- The core all-held scalar classification justifies the omitted transition
for either access kind. No successful operation is a premise. -/
theorem guard_noop (state : LocationState) (kind : AccessKind) (held : Bool)
    (guard : PostchildrenNoop state kind held (some .ForeignAccess)) :
    state.performAccess kind .ForeignAccess held =
      .Success state ⟨state.permission,state.permission⟩ :=
  LocationState.performAccess_foreignWriteNoop state kind held guard.2.1

/-- Exposes the actual core loop body, not a replacement interpreter. Starting
from a pending postvisit preserves CURRENT child effects and cache, materializes
the current node, updates the witness at the original source timing, and pops
only that pending task. No whole-component completion is asserted. -/
theorem actual_postchildren (tree : BorrowTree) (initial : LocationTree) (root : UniIndex)
    (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (wildcard : Bool) :
    ∃ scan : Unit → (LocationTree × Bool × BorrowTree.WildcardAccessStatus ×
        Array (UniIndex × Bool) × Nat) → Id (ForInStep (LocationTree × Bool ×
        BorrowTree.WildcardAccessStatus × Array (UniIndex × Bool) × Nat)),
      (tree.performWildcardAccessAt initial root maximum kind protections wildcard =
        let final := Lean.Loop.forIn {} (initial,false,.Completed,#[(root,false)],0) scan
        ⟨final.1, if final.2.2.1 == .Completed && !final.2.1 && !wildcard then
          .NoValidExposedReferences root none else final.2.2.1⟩) ∧
      ∀ (current : LocationTree) (index : UniIndex) (node : TreeNode)
        (stack : Array (UniIndex × Bool)) (steps : Nat) (witness : Bool),
        tree.nodes.get index = some node →
        ¬ steps + 1 > tree.nodes.size * 2 + 1 →
        current.exposedCache.accessRelatedness root index kind wildcard
          (match maximum with | some tag => tag.value < node.tag.value | none => false) =
          some .ForeignAccess →
        PostchildrenNoop ((current.perms.get index).getD node.defaultLocationState)
          kind (protections.contains node.tag) (some .ForeignAccess) →
        scan () (current,witness,.Completed,stack.push (index,true),steps) =
          .yield (GeneralBorrowWildcardVirtualLeaf.materialized current index node,
            witness || (node.isExposed &&
              (((current.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
                (protections.contains node.tag)).allows kind &&
              (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value))),
            .Completed,stack,steps+1) := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  refine ⟨scan,?_,?_⟩
  · split <;> rfl
  ·
    intro current index node stack steps witness present budget related guard
    have skipped := guard.2.2
    have sourceGuard := guard_source _ _ _ guard
    simp only [scan]
    unfold_leaf_helpers
    simp [present,budget,related,skipped,sourceGuard,GeneralBorrowWildcardVirtualLeaf.materialized,
      Id.run,bind,pure]
    all_goals try unfold_leaf_helpers
    all_goals try rw [related]
    all_goals cases stored : current.perms.get index <;>
      simp_all [UniValMap.orInsert]
    all_goals cases maximum <;> simp_all
    all_goals split <;> simp_all
    all_goals cases witness <;> simp_all [Bool.and_eq_false_iff]
    all_goals cases exposed : node.isExposed <;> simp_all
    all_goals cases allowed : (((current.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind <;> simp_all

    all_goals congr 3
    all_goals symm
    all_goals apply decide_eq_false_iff_not.mpr
    all_goals exact UInt64.not_le.mpr (by assumption)

end DuplicatePrefix.DuplicatePrefixCallbackVisitAuthorizationRepaired
