import duplicate_prefix.GeneralBorrowExposedConditionalWriteInvariant
import duplicate_prefix.GeneralBorrowWildcardForestWeights

namespace DuplicatePrefix.GeneralBorrowExposedConditionalWriteLoop
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized onlyForeign)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardSubtreeState (or_insert_snd write)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowExposedConditionalWriteState GeneralBorrowExposedConditionalWriteInvariant
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

def seen (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (maximum : Option Miri.Memory.BorTag) (protections : ProtectedTags) (witness : Bool) : Bool :=
  if node.isExposed && ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write &&
    (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value)) then true else witness

/-- The actual virtual-root postorder source visitor completes on an arbitrary
ranked exposed subtree from initial coherent counters and universal protected
Read permissions. Exact Read counters and later Read compatibility survive. -/
theorem access_from (tree : BorrowTree) (initial : LocationTree) (root : UniIndex)
    (maximum : Option Miri.Memory.BorTag) (protections : ProtectedTags)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (data : Data tree initial root protections) (current : LocationTree)
    (currentFrame : WriteFrame initial current) (currentProfile : Profile tree current protections)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (noCutoff : maximum = none) :
    let result := tree.performWildcardAccessAt current root maximum .Write protections true
    result.status = .Completed ∧ WriteFrame initial result.location ∧ Profile tree result.location protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step : ∀ state, Invariant weights data maximum state →
      (∃ final, scan () state = .done final ∧ Invariant weights data maximum final) ∨
      ∃ next, scan () state = .yield next ∧ Invariant weights data maximum next ∧
        potential weights.weight next.2.2.2.1 < potential weights.weight state.2.2.2.1 := by
    intro state valid
    rcases state with ⟨location,witness,status,stack,steps⟩
    have statusEq := valid.status
    dsimp only at statusEq
    subst status
    by_cases empty : stack = #[]
    · subst stack
      exact .inl ⟨_,by simp [scan],valid⟩
    · obtain ⟨baseStack,⟨index,afterChildren⟩,rfl⟩ := Array.exists_push_of_ne_empty empty
      have supported : data.support index := valid.known (index,afterChildren) (by simp)
      obtain ⟨node,present⟩ := data.present index supported
      have notPast : ¬steps+1 > tree.nodes.size*2+1 := by
        have bound := valid.budget
        dsimp only at bound
        omega
      have related := classify data location valid.frame index node supported maximum
      cases afterChildren with
      | false =>
        have positive : 1 ≤ weights.weight index := by
          have bound := weights.children index node present
          omega
        cases isForeign : foreign initial index node maximum with
        | false =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write true (onlyForeign node maximum) = some .EitherAccess := by simpa [isForeign] using related
          unfold onlyForeign at exactRel
          have pushing := children_loop node.children (baseStack.push (index,true))
          simp only [forIn'_eq_forIn,pure] at pushing
          refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,exactRel,effective,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp [exactRel,effective,pushing,expanded]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals cases maximum <;> simp_all [pushing,expanded,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [pushing,expanded,Id.run,bind,pure]
          · exact expand weights data maximum location witness baseStack index node steps valid present (by simp [isForeign])
          · rw [expanded_potential,potential_push]
            simp only [cost,Bool.false_eq_true,↓reduceIte]
            have bounded := weights.children index node present
            omega
        | true =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write true (onlyForeign node maximum) = some .ForeignAccess := by simpa [isForeign] using related
          unfold onlyForeign at exactRel
          cases skipped : (effective location index node).skipIfKnownNoop .Write .ForeignAccess with
          | SkipSelfAndChildren =>
            dsimp only [effective] at skipped
            refine .inr ⟨(location,witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
            · simp only [scan]
              unfold_leaf_helpers
              simp [notPast,present,exactRel,skipped,effective,Id.run,bind,pure]
              try unfold_leaf_helpers
              try simp [exactRel,skipped,effective]
              all_goals try rw [exactRel]
              all_goals try unfold_leaf_helpers
              all_goals cases maximum <;> simp_all [onlyForeign,skipped,effective,Id.run,bind,pure]
              all_goals try unfold_leaf_helpers
              all_goals try simp_all [skipped,effective,Id.run,bind,pure]
            · exact pop weights data maximum location witness baseStack (index,false) steps valid (by simp [cost];omega)
            · rw [potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              omega
          | Recurse =>
            dsimp only [effective] at skipped
            have pushing := children_loop node.children (baseStack.push (index,true))
            simp only [forIn'_eq_forIn,pure] at pushing
            refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
            · simp only [scan]
              unfold_leaf_helpers
              simp [notPast,present,exactRel,skipped,effective,Id.run,bind,pure]
              try unfold_leaf_helpers
              simp [exactRel,skipped,effective,pushing,expanded]
              all_goals try rw [exactRel]
              all_goals try unfold_leaf_helpers
              all_goals cases maximum <;> simp_all [onlyForeign,skipped,effective,pushing,expanded,Id.run,bind,pure]
              all_goals try unfold_leaf_helpers
              all_goals try simp_all [skipped,effective,pushing,expanded,Id.run,bind,pure]
            · exact expand weights data maximum location witness baseStack index node steps valid present (fun _ => skipped)
            · rw [expanded_potential,potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              have bounded := weights.children index node present
              omega
      | true =>
        cases isForeign : foreign initial index node maximum with
        | false =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write true (onlyForeign node maximum) = some .EitherAccess := by simpa [isForeign] using related
          unfold onlyForeign at exactRel
          refine .inr ⟨(materialized location index node,seen location index node maximum protections witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,exactRel,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp [exactRel,materialized,seen,effective]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals cases maximum <;> simp_all [onlyForeign,materialized,seen,effective,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [materialized,seen,effective,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective]
            all_goals try
              have no : ¬ node.tag.value ≤ _ := UInt64.not_le.mpr (by assumption)
              simp_all only [no,decide_false,Bool.false_or]
          · apply post weights data maximum location _ witness _ baseStack index steps valid
            · intro query;rfl
            · exact materialized_profile tree location index node protections present valid.profile
            · intro query different
              unfold materialized Miri.TreeBorrows.UniValMap.orInsert
              split
              · rfl
              · exact GeneralBorrowFreshLocation.get_other _ index query node.defaultLocationState different
            · exact GeneralBorrowExposedNonleafCoherence.materialized_coherent tree location index node protections present valid.coherent
          · rw [potential_push]
            simp [cost]
        | true =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write true (onlyForeign node maximum) = some .ForeignAccess := by simpa [isForeign] using related
          unfold onlyForeign at exactRel
          have recurse := valid.pending index node (by simp) present isForeign
          have zeroInitial : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write = 0 := by
            simpa [foreign,noCutoff,onlyForeign] using isForeign
          have compatible := foreign_compatible tree initial location protections valid.frame valid.profile index node present zeroInitial
          obtain ⟨recorded,next,delta,record,access,good,localSupport,noSupport⟩ := GeneralBorrowExposedConditionalWritePermissions.visit
            (effective location index node) .ForeignAccess (protections.contains node.tag)
            compatible (GeneralBorrowEvents.recurse_scheduled _ _ _ recurse)
          have currentZero : zero location index = true := by rw [zero_frame initial location valid.frame index];simp [zero,zeroInitial]
          have nextGood : GeneralBorrowExposedConditionalWritePermissions.Condition (zero location index) next (protections.contains node.tag) := by
            simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,currentZero,ite_true] using good
          have support : node.isExposed = true → GeneralBorrowExposedConditionalWritePermissions.support next (protections.contains node.tag) =
              GeneralBorrowExposedConditionalWritePermissions.support (effective location index node) (protections.contains node.tag) := by
            intro exposed
            have zeroCurrent : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write = 0 := by
              have eq : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write = GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write := congrArg UInt16.toNat (valid.frame index)
              rw [eq,zeroInitial]
            have oldZero := GeneralBorrowExposedConditionalAccessSupport.exposed_zero tree location protections valid.coherent data.short index node present exposed .Write zeroCurrent
            exact (noSupport oldZero).trans oldZero.symm
          have cacheOK : ∀ oldLevel newLevel, (location.exposedCache.updateExposure tree.nodes index oldLevel newLevel).outcome = .ok () :=
            fun oldLevel newLevel => GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes data.depth index node present oldLevel newLevel
          refine .inr ⟨(updated tree location index node protections recorded next delta,
            seen location index node maximum protections witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,exactRel,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp only [exactRel,or_insert_snd,record,access,LocationState.AccessResult.resultingState]
            simp [updated,write,materialized,seen,effective,cacheOK]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals cases maximum <;> simp_all [onlyForeign,record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective]
            all_goals try
              have no : ¬ node.tag.value ≤ _ := UInt64.not_le.mpr (by assumption)
              simp_all only [no,decide_false,Bool.false_or]
            all_goals try split <;> simp_all [Bool.and_eq_false_iff]
          · apply post weights data maximum location _ witness _ baseStack index steps valid
            · exact updated_frame tree location index node protections recorded next delta data.depth present support
            · exact updated_profile tree location index node protections recorded next delta present valid.profile (updated_frame tree location index node protections recorded next delta data.depth present support) nextGood
            · exact fun query different => updated_other tree location index query node protections recorded next delta different
            · exact GeneralBorrowExposedConditionalWriteCoherence.updated_coherent tree location index node protections recorded next delta .ForeignAccess data.depth present valid.coherent record access
          · rw [potential_push]
            simp [cost]
  have retained := GeneralBorrowLoop.invariant scan
    (fun state : LoopState => potential weights.weight state.2.2.2.1)
    (Invariant weights data maximum) step (current,false,.Completed,#[(root,false)],0)
    (GeneralBorrowExposedConditionalWriteInvariant.initial_from weights data maximum current currentFrame currentProfile currentCoherent)
  simp only [Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
  exact ⟨retained.status,retained.frame,retained.profile,retained.coherent⟩

end DuplicatePrefix.GeneralBorrowExposedConditionalWriteLoop
