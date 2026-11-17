import Lean
import Miri.TreeBorrows.TreeState
import Init.Internal.Order.While
namespace WildcardPostorderDisabled
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def orig : TreeNode := ⟨⟨1,by decide⟩,none,#[],.Disabled,.None,true,none⟩
def a : TreeNode := ⟨⟨2,by decide⟩,none,#[ix 2],.Cell,.Read,false,none⟩
def d : TreeNode := ⟨⟨3,by decide⟩,some (ix 1),#[ix 3],.ReservedFrz false,.Read,false,none⟩
def v : TreeNode := ⟨⟨5,by decide⟩,some (ix 2),#[],.ReservedFrz false,.Read,true,none⟩
def loc : LocationTree := ⟨⟨#[some ⟨.Unique,true,.None⟩,some ⟨.Cell,true,.Write⟩,some ⟨.Disabled,true,.Read⟩,none]⟩,⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩]⟩⟩⟩
def t : BorrowTree := ⟨⟨#[(orig.tag,ix 0),(a.tag,ix 1),(d.tag,ix 2),(v.tag,ix 3)],#[]⟩,⟨#[some orig,some a,some d,some v]⟩,DedupRangeMap.new (Size.ofBytes 2) loc,#[ix 0,ix 1]⟩

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def disabledSubtree := t.performWildcardAccessAt loc (ix 2) (some ⟨4,by decide⟩) .Write {} true
def fullRoot := t.performWildcardAccessAt loc (ix 1) (some ⟨4,by decide⟩) .Write {} true

theorem disabled_transition_noop : (⟨.Disabled,.Disabled⟩ : PermTransition).isNoop = true := rfl
theorem disabled_possible (accessed : Bool) (sifa : IdempotentForeignAccess) :
    (⟨.Disabled,accessed,sifa⟩ : LocationState).possible = true := by cases accessed <;> rfl
theorem disabled_no_local_exposure : Permission.strongestAllowedLocalAccess .Disabled false = .None := rfl

/-- The targeted Disabled subtree completes and retains the child transition. -/
theorem disabled_subtree_completed : disabledSubtree.status = .Completed := by cbv
theorem child_effect_retained : disabledSubtree.location.perms.get (ix 3) = some ⟨.Disabled,false,.Write⟩ := by cbv
theorem child_cache_retained : disabledSubtree.location.exposedCache.nodes.get (ix 2) = some ⟨0,0⟩ := by cbv
theorem disabled_sifa_retained : disabledSubtree.location.perms.get (ix 2) = some ⟨.Disabled,true,.Read⟩ := by cbv

/-- The reviewed Cell extension also retains the completed child effects.
The earlier Disabled-only residual assertion is saved in ignored check output
and documented in STATUS; it is not asserted for this revised visitor. -/
theorem cell_parent_completed : fullRoot.status = .Completed := by cbv
theorem full_child_effect_retained : fullRoot.location.perms.get (ix 3) = some ⟨.Disabled,false,.Write⟩ := by cbv
theorem cell_sifa_retained : fullRoot.location.perms.get (ix 1) = some ⟨.Cell,true,.Write⟩ := by cbv

/-- A Cell that needs a new SIFA record still follows the original record path. -/
theorem cell_record_success_preserved :
    (⟨.Cell,true,.Read⟩ : LocationState).skipIfKnownNoop .Write .ForeignAccess = .Recurse ∧
    (⟨.Cell,true,.Read⟩ : LocationState).recordNewAccess .Write .ForeignAccess =
      .Recorded ⟨.Cell,true,.Write⟩ := by constructor <;> rfl

/-- Guard boundaries retain local UB and the protected Disabled error. -/
theorem local_disabled_error : (⟨.Disabled,true,.Read⟩ : LocationState).performAccess .Write .LocalAccess false =
    .Error ⟨.Disabled,true,.Read⟩ (.ChildAccessForbidden .Disabled) := rfl
theorem protected_disabled_error : (⟨.Disabled,true,.Read⟩ : LocationState).performAccess .Write .ForeignAccess true =
    .Error ⟨.Disabled,true,.Read⟩ (.ProtectedDisabled .Disabled) := rfl

/-- The actual wildcard visitor still reports a protected child transition. -/
def protectedLocation : LocationTree :=
  {loc with perms := loc.perms.insert (ix 3) ⟨.Unique,true,.None⟩}
def protectV : ProtectedTags := ({} : ProtectedTags).insert v.tag .StrongProtector
theorem visitor_protected_child_error :
    (t.performWildcardAccessAt protectedLocation (ix 1) (some ⟨4,by decide⟩) .Write protectV true).status =
      .TransitionError (ix 3) (.ProtectedDisabled .Unique) := by cbv
/-- Protected ReservedIM is outside the no-op class and retains its invariant error. -/
def protectedIMLocation : LocationTree :=
  {loc with perms := loc.perms.insert (ix 3) ⟨.ReservedIM,true,.None⟩}
theorem visitor_other_permission_error :
    (t.performWildcardAccessAt protectedIMLocation (ix 1) (some ⟨4,by decide⟩) .Write protectV true).status =
      .PermissionInvariantFailure (ix 3) := by cbv

/-- A held Cell is still a genuine no-op; child updates survive its postvisit. -/
def protectA : ProtectedTags := ({} : ProtectedTags).insert a.tag .StrongProtector
def protectedCellRoot := t.performWildcardAccessAt loc (ix 1) (some ⟨4,by decide⟩) .Write protectA true
theorem protected_cell_parent_completed : protectedCellRoot.status = .Completed := by cbv
theorem protected_cell_child_cache_retained :
    protectedCellRoot.location.perms.get (ix 3) = some ⟨.Disabled,false,.Write⟩ ∧
    protectedCellRoot.location.exposedCache.nodes.get (ix 1) = some ⟨0,0⟩ := by cbv

/-- A held Disabled location that was never accessed is also a source no-op. -/
def lazyProtectedLocation : LocationTree :=
  {loc with perms := loc.perms.insert (ix 2) ⟨.Disabled,false,.Read⟩}
def protectD : ProtectedTags := ({} : ProtectedTags).insert d.tag .StrongProtector
def lazyProtectedRoot := t.performWildcardAccessAt lazyProtectedLocation (ix 2)
  (some ⟨4,by decide⟩) .Write protectD true
theorem lazy_protected_disabled_completed : lazyProtectedRoot.status = .Completed := by cbv
theorem lazy_protected_disabled_state_retained :
    lazyProtectedRoot.location.perms.get (ix 2) = some ⟨.Disabled,false,.Read⟩ := by cbv
theorem lazy_protected_child_effect_retained :
    lazyProtectedRoot.location.perms.get (ix 3) = some ⟨.Disabled,false,.Write⟩ := by cbv

/-- The excluded accessed/protected case keeps its old visitor assertion.
This is an error-preservation test, not a claim that the visitor reports UB. -/
theorem excluded_protected_accessed_old_path :
    (t.performWildcardAccessAt loc (ix 2) (some ⟨4,by decide⟩) .Write protectD true).status =
      .RecordDebugAssertion (ix 2) := by cbv
end WildcardPostorderDisabled
open Lean Elab Command in
run_cmd do
 for (name,_) in (← getEnv).constants.toList do
  if name.toString.startsWith "WildcardPostorderDisabled." then
   for dependency in (← collectAxioms name) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
     throwError "unapproved regression axiom {dependency}"
