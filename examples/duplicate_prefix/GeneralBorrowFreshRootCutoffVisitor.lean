import duplicate_prefix.GeneralBorrowFreshRootCutoff
import duplicate_prefix.GeneralBorrowWildcardSubtreeState
namespace DuplicatePrefix.GeneralBorrowFreshRootCutoffVisitor
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Lean Elab Tactic
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Give the second literal source loop a local name; the first one was named
by name_range_scan. This tactic only constructs ordinary kernel-checked terms. -/
elab "name_cutoff_other_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some first := target.find? (fun expr => expr.isAppOf ``Lean.Loop.forIn)
      | throwError "no first source Loop.forIn found"
    let arity := first.getAppArgs.size
    let some loop := target.find? (fun expr => expr.isAppOf ``Lean.Loop.forIn && expr.getAppArgs.size == arity && !(expr.getAppArgs.back!).isFVar)
      | throwError "no second source Loop.forIn found"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `noCutoffScan (← Lean.Meta.inferType body) body
    let (scan,goal) ← goal.intro1P
    let target ← goal.getType
    let target := target.replace fun expr => if expr == body then some (mkFVar scan) else none
    return [←goal.change target]

/-- Exact pinned wildcard DFS equivalence for a cutoff above EVERY current
node. Access kind, actual protection table and the virtual-root flag are kept
identical. Both entry pruning and the successful-exposed-witness test agree. -/
theorem access (tree : BorrowTree) (maximum : BorTag) (bound : GeneralBorrowFreshRootCutoff.Bound tree maximum)
    (location : LocationTree) (root : UniIndex) (kind : AccessKind) (protections : ProtectedTags) (virtual : Bool) :
    tree.performWildcardAccessAt location root (some maximum) kind protections virtual =
      tree.performWildcardAccessAt location root none kind protections virtual := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  name_cutoff_other_scan
  have equal : scan = noCutoffScan := by
    funext token current
    cases token
    rcases current with ⟨current,witness,status,stack,steps⟩
    by_cases running : (!stack.isEmpty && status == .Completed) = true
    · simp only [scan,noCutoffScan,running,↓reduceIte]
      by_cases past : steps+1 > tree.nodes.size*2+1
      · simp only [past,↓reduceIte]
      · simp only [past,↓reduceIte]
        cases back : stack.back? with
        | none => simp only [back]
        | some task =>
          rcases task with ⟨index,post⟩
          simp only [back]
          cases found : tree.nodes.get index with
          | none => cases post <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,found]
          | some node =>
            have nodeBound := bound index node found
            have noForeign : (decide (maximum.value < node.tag.value) : Bool) = false := by
              simpa only [DuplicatePrefixCallbackAuthorization.aboveMaximum] using GeneralBorrowFreshRootCutoff.above node maximum nodeBound
            have canWitness : (decide (node.tag.value ≤ maximum.value) : Bool) = true := by simpa only [decide_eq_true_eq] using nodeBound
            cases post <;>
              simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,found,noForeign,
                Option.isNone_some,Option.isNone_none,Option.any_some,Option.any_none,Bool.false_or,Bool.true_or,canWitness]
    · simp only [scan,noCutoffScan,running,Bool.false_eq_true,↓reduceIte]
  rw [equal]
end DuplicatePrefix.GeneralBorrowFreshRootCutoffVisitor
