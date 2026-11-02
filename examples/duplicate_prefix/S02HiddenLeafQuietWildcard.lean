import duplicate_prefix.S03EmptyPopFactsCallback
import duplicate_prefix.S02HiddenLeafQuietNormal

namespace DuplicatePrefix.S02HiddenLeafQuietWildcard
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowWildcardVirtualLeaf GeneralBorrowWildcardSubtreeState
open S02HiddenLeafQuietNormal
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

private theorem record_quiet (state recorded : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (quiet : Quiet state) (record : state.recordNewAccess kind related = .Recorded recorded) : Quiet recorded := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;exact quiet
  · cases record

private theorem foreign_quiet (state : LocationState) (kind : AccessKind) (held : Bool)
    (quiet : Quiet state) : Quiet (state.performAccess kind .ForeignAccess held).resultingState := by
  rcases state with ⟨permission,accessed,cache⟩
  rcases quiet with inactive | cell
  · change accessed = false at inactive
    subst accessed
    cases permission with
    | ReservedFrz conflicted => cases conflicted <;> cases held <;> cases cache <;> cases kind <;> exact Or.inl rfl
    | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> cases cache <;> cases kind <;> exact Or.inl rfl
  · change permission = .Cell at cell
    subst permission
    cases accessed <;> cases held <;> cases cache <;> cases kind <;> exact Or.inr rfl

private def Good (query : UniIndex) (node : TreeNode) (kind : AccessKind) (location : LocationTree) : Prop :=
  Quiet (GeneralBorrowWildcardVirtualLeaf.effective location query node) ∧ counter location.exposedCache query kind = 0

private theorem insert_good (query index : UniIndex) (node : TreeNode) (kind : AccessKind)
    (location : LocationTree) (state : LocationState) (good : Good query node kind location)
    (same : index = query → Quiet state) :
    Good query node kind {location with perms := location.perms.insert index state} := by
  refine ⟨?_,good.2⟩
  by_cases equal : query = index
  · subst index
    simp only [GeneralBorrowWildcardVirtualLeaf.effective,GeneralBorrowFreshLocation.get_same,Option.getD_some]
    exact same rfl
  · simpa only [GeneralBorrowWildcardVirtualLeaf.effective,GeneralBorrowFreshLocation.get_other _ index query state equal] using good.1

private theorem materialized_good (query index : UniIndex) (node value : TreeNode) (kind : AccessKind)
    (location : LocationTree) (good : Good query node kind location) :
    Good query node kind (materialized location index value) := by
  unfold materialized UniValMap.orInsert
  split
  · exact good
  · exact insert_good query index node kind location value.defaultLocationState good (by intro _;exact Or.inl rfl)

private theorem cache_good (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (query index : UniIndex) (node value : TreeNode) (kind : AccessKind)
    (present : tree.nodeAt query = some node) (found : tree.nodeAt index = some value)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (exposed : value.isExposed = true)
    (location : LocationTree) (before after : WildcardAccessLevel) (good : Good query node kind location) :
    Good query node kind {location with exposedCache := (location.exposedCache.updateExposure tree.nodes index before after).cache} :=
  ⟨good.1,(S03EmptyPopFactsCallback.cache_frame tree graph query node present leaf hidden location.exposedCache index value found exposed before after kind).trans good.2⟩

private theorem write_good (tree : BorrowTree) (query index root : UniIndex) (node value : TreeNode)
    (kind : AccessKind) (protections : ProtectedTags) (virtual foreign : Bool)
    (present : tree.nodeAt query = some node) (found : tree.nodeAt index = some value)
    (location : LocationTree) (good : Good query node kind location)
    (relation : WildcardAccessRelatedness) (exact : AccessRelatedness)
    (classified : location.exposedCache.accessRelatedness root index kind virtual foreign = some relation)
    (isExact : DuplicatePrefixCallbackAuthorization.exactRelation relation = some exact)
    (recorded : LocationState)
    (record : (GeneralBorrowWildcardVirtualLeaf.effective location index value).recordNewAccess kind exact = .Recorded recorded) :
    Good query node kind (write location index value recorded
      (recorded.performAccess kind exact (protections.contains value.tag)).resultingState) := by
  have recordInactive : index = query → Quiet recorded := by
    intro equal
    subst index
    have same : value = node := Option.some.inj (found.symm.trans present)
    subst value
    exact record_quiet _ recorded kind exact good.1 record
  have resultInactive : index = query →
      Quiet (recorded.performAccess kind exact (protections.contains value.tag)).resultingState := by
    intro equal
    have fresh := recordInactive equal
    subst index
    have classifiedQuery := S03EmptyPopFactsCallback.not_local location.exposedCache root query kind virtual foreign good.2
    have rel : relation = .ForeignAccess := by
      rcases classifiedQuery with missing | foreign
      · rw [missing] at classified;cases classified
      · exact Option.some.inj (classified.symm.trans foreign)
    subst relation
    have exactEq : exact = .ForeignAccess := Option.some.inj isExact.symm
    subst exact
    exact foreign_quiet recorded kind _ fresh
  unfold write
  exact insert_good query index node kind _ _
    (insert_good query index node kind _ recorded
      (materialized_good query index node value kind location good) recordInactive) resultInactive

private theorem write_result_good (tree : BorrowTree) (query index root : UniIndex) (node value : TreeNode)
    (kind : AccessKind) (protections : ProtectedTags) (virtual foreign : Bool)
    (present : tree.nodeAt query = some node) (found : tree.nodeAt index = some value)
    (location : LocationTree) (good : Good query node kind location)
    (relation : WildcardAccessRelatedness) (exact : AccessRelatedness)
    (classified : location.exposedCache.accessRelatedness root index kind virtual foreign = some relation)
    (isExact : DuplicatePrefixCallbackAuthorization.exactRelation relation = some exact)
    (recorded : LocationState)
    (record : (GeneralBorrowWildcardVirtualLeaf.effective location index value).recordNewAccess kind exact = .Recorded recorded)
    (result : LocationState.AccessResult) (next : LocationState)
    (performed : recorded.performAccess kind exact (protections.contains value.tag) = result)
    (stateEq : result.resultingState = next) :
    Good query node kind (write location index value recorded next) := by
  have known := write_good tree query index root node value kind protections virtual foreign present found location good
    relation exact classified isExact recorded record
  rw [performed,stateEq] at known
  exact known

private theorem cache_write_good (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (query index root : UniIndex) (node value : TreeNode) (kind : AccessKind)
    (protections : ProtectedTags) (virtual foreign : Bool)
    (present : tree.nodeAt query = some node) (found : tree.nodeAt index = some value)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (exposed : value.isExposed = true)
    (location : LocationTree) (good : Good query node kind location)
    (relation : WildcardAccessRelatedness) (exact : AccessRelatedness)
    (classified : location.exposedCache.accessRelatedness root index kind virtual foreign = some relation)
    (isExact : DuplicatePrefixCallbackAuthorization.exactRelation relation = some exact)
    (recorded : LocationState)
    (record : (GeneralBorrowWildcardVirtualLeaf.effective location index value).recordNewAccess kind exact = .Recorded recorded)
    (result : LocationState.AccessResult) (next : LocationState)
    (performed : recorded.performAccess kind exact (protections.contains value.tag) = result)
    (stateEq : result.resultingState = next) (before after : WildcardAccessLevel) :
    Good query node kind {write location index value recorded next with
      exposedCache := (location.exposedCache.updateExposure tree.nodes index before after).cache} :=
  cache_good tree graph query index node value kind present found leaf hidden exposed
    (write location index value recorded next) before after
    (write_result_good tree query index root node value kind protections virtual foreign present found location good
      relation exact classified isExact recorded record result next performed stateEq)

/-- Every actual wildcard callback retains an initially inactive hidden leaf.
The original error outcomes are retained; no successful callback is assumed. -/
theorem access (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (location : LocationTree) (root : UniIndex) (maximum : Option BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (virtual : Bool)
    (inactive : Quiet (GeneralBorrowWildcardVirtualLeaf.effective location query node))
    (zero : counter location.exposedCache query kind = 0) :
    Quiet (GeneralBorrowWildcardVirtualLeaf.effective
      (tree.performWildcardAccessAt location root maximum kind protections virtual).location query node) ∧
    counter (tree.performWildcardAccessAt location root maximum kind protections virtual).location.exposedCache query kind = 0 := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  let property := fun (state : LocationTree × Bool × BorrowTree.WildcardAccessStatus × Array (UniIndex × Bool) × Nat) =>
    Good query node kind state.1 ∧ (state.2.2.1 = .Completed → state.2.2.2.2 ≤ tree.nodes.size*2+1)
  let measure := fun (state : LocationTree × Bool × BorrowTree.WildcardAccessStatus × Array (UniIndex × Bool) × Nat) =>
    if state.2.2.1 = .Completed ∧ state.2.2.2.1 ≠ #[] then tree.nodes.size*2+2-state.2.2.2.2 else 0
  have step : ∀ state, property state →
      (∃ final, scan () state = .done final ∧ property final) ∨
      ∃ next, scan () state = .yield next ∧ property next ∧ measure next < measure state := by
    intro state maintained
    rcases state with ⟨current,witness,status,stack,steps⟩
    by_cases completed : status = .Completed
    · subst status
      by_cases empty : stack = #[]
      · subst stack
        exact .inl ⟨_,by simp [scan],maintained⟩
      · obtain ⟨base,⟨index,afterChildren⟩,rfl⟩ := Array.exists_push_of_ne_empty empty
        by_cases past : steps+1 > tree.nodes.size*2+1
        · refine .inr ⟨(current,witness,.ParentCycle root,base.push (index,afterChildren),steps+1),?_,⟨maintained.1,by simp⟩,?_⟩
          · simp only [scan,Array.isEmpty_push,Bool.not_false,beq_self_eq_true,Bool.true_and,past,↓reduceIte]
          · have bound : steps ≤ tree.nodes.size*2+1 := maintained.2 rfl
            simp [measure]
            omega
        · have bound : steps ≤ tree.nodes.size*2+1 := maintained.2 rfl
          cases found : tree.nodes.get index with
          | none =>
            refine .inr ⟨(current,witness,.MissingNode index,(if afterChildren then base else base.push (index,afterChildren)),steps+1),?_,⟨maintained.1,by simp⟩,?_⟩
            · simp only [scan]
              unfold_leaf_helpers
              cases afterChildren <;> simp only [Array.isEmpty_push,Array.back?_push,Array.pop_push,
                Bool.not_false,Bool.not_true,Bool.false_eq_true,beq_self_eq_true,Bool.true_and,past,found,↓reduceIte]
            · simp [measure];omega
          | some value =>
            have finish (nextLocation : LocationTree) (nextWitness : Bool)
                (nextStatus : BorrowTree.WildcardAccessStatus) (nextStack : Array (UniIndex × Bool))
                (kept : Good query node kind nextLocation) :
                (∃ final, (ForInStep.yield (nextLocation,nextWitness,nextStatus,nextStack,steps+1)) = .done final ∧ property final) ∨
                ∃ next, (ForInStep.yield (nextLocation,nextWitness,nextStatus,nextStack,steps+1)) = .yield next ∧
                  property next ∧ measure next < measure (current,witness,.Completed,base.push (index,afterChildren),steps) := by
              refine .inr ⟨_,rfl,⟨kept,by intro _;exact Nat.le_of_not_gt past⟩,?_⟩
              change (if nextStatus = .Completed ∧ nextStack ≠ #[] then tree.nodes.size*2+2-(steps+1) else 0) <
                (if (BorrowTree.WildcardAccessStatus.Completed = .Completed ∧ base.push (index,afterChildren) ≠ #[]) then tree.nodes.size*2+2-steps else 0)
              have old : (if (BorrowTree.WildcardAccessStatus.Completed = .Completed ∧ base.push (index,afterChildren) ≠ #[]) then tree.nodes.size*2+2-steps else 0) = tree.nodes.size*2+2-steps := by simp
              rw [old]
              split <;> omega
            cases afterChildren
            · simp only [scan]
              unfold_leaf_helpers
              simp only [Array.isEmpty_push,Array.back?_push,Array.pop_push,Bool.not_false,Bool.not_true,
                Bool.false_eq_true,beq_self_eq_true,Bool.true_and,past,found,↓reduceIte]
              repeat' split
              all_goals exact finish current witness .Completed _ maintained.1
            · simp only [scan]
              unfold_leaf_helpers
              simp only [Array.isEmpty_push,Array.back?_push,Array.pop_push,Bool.not_false,Bool.not_true,
                Bool.false_eq_true,beq_self_eq_true,Bool.true_and,past,found,↓reduceIte]
              repeat' first | split | simp_all only [Option.bind_some,Option.bind_none,or_insert_snd,Bool.and_eq_true]
              all_goals apply finish
              all_goals first
                | exact maintained.1
                | exact materialized_good query index node value kind current maintained.1
                | (apply write_result_good tree query index root node value kind protections virtual (onlyForeign value maximum)
                    present found current maintained.1
                   all_goals first | assumption | rfl)
                | (apply cache_write_good tree graph query index root node value kind protections virtual (onlyForeign value maximum)
                    present found leaf hidden (by solve_by_elim (maxDepth := 6) [And.left,And.right]) current maintained.1
                   all_goals first | assumption | rfl | exact maintained.1 | solve_by_elim (maxDepth := 3) [And.left,And.right])
    · exact .inl ⟨_,by simp [scan,completed],maintained⟩
  have retained := GeneralBorrowLoop.invariant scan measure property step (location,false,.Completed,#[(root,false)],0) ⟨⟨inactive,zero⟩,by simp⟩
  split <;> exact retained.1

end DuplicatePrefix.S02HiddenLeafQuietWildcard

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02HiddenLeafQuietWildcard.access) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
