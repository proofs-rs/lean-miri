import duplicate_prefix.GeneralBorrowExposedScopedWriteFramePrimaryInvariant
import duplicate_prefix.GeneralBorrowWildcardForestWeights

namespace DuplicatePrefix.GeneralBorrowExposedScopedWriteFramePrimaryLoop
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized onlyForeign)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardSubtreeState (or_insert_snd write)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowExposedKnownRootWriteState
open GeneralBorrowExposedKnownRootWriteInvariant (LoopState)
open GeneralBorrowExposedScopedWriteFramePrimaryInvariant
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def seen (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (maximum : Option Miri.Memory.BorTag) (protections : ProtectedTags) (witness : Bool) : Bool :=
  if node.isExposed && ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write &&
    (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value)) then true else witness

/-- The actual primary-root postorder visitor completes on an arbitrary
ranked exposed subtree. Initial coherent counters and an exposed supporting
descendant derive positive path counters and its actual visit. Exact Read
counters and universal protected Read compatibility survive. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (root : UniIndex)
    (maximumTag : Miri.Memory.BorTag) (protections : ProtectedTags) (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (data : GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree initial root protections)
    (tags : ∀ index node, area.support index → tree.nodes.get index = some node → node.tag.value ≤ maximumTag.value) :
    let result := tree.performWildcardAccessAt initial root (some maximumTag) .Write protections false
    result.status = .Completed ∧ WriteFrame initial result.location ∧ Profile tree result.location protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬area.support query → result.location.perms.get query = initial.perms.get query) := by
  have rootPositive := GeneralBorrowExposedKnownRootWritePrimaryPath.positive data.base data.witness data.node data.present data.exposed data.support root data.path
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step : ∀ state, Invariant weights data state →
      (∃ final, scan () state = .done final ∧ Invariant weights data final ∧ final.2.1 = true) ∨
      ∃ next, scan () state = .yield next ∧ Invariant weights data next ∧
        potential weights.weight next.2.2.2.1 < potential weights.weight state.2.2.2.1 := by
    intro state valid
    rcases state with ⟨location,witness,status,stack,steps⟩
    have statusEq := valid.base.status
    dsimp only at statusEq
    subst status
    by_cases empty : stack = #[]
    · subst stack
      exact .inl ⟨_,by simp [scan],valid,GeneralBorrowExposedKnownRootWritePrimaryWitness.empty valid.witness⟩
    · obtain ⟨baseStack,⟨index,afterChildren⟩,rfl⟩ := Array.exists_push_of_ne_empty empty
      have supported : data.base.support index := valid.base.known (index,afterChildren) (by simp)
      obtain ⟨node,present⟩ := data.base.present index supported
      have tagBound := tags index node (data.base.included index supported) present
      have notForeign : ¬ maximumTag.value < node.tag.value := UInt64.not_lt.mpr tagBound
      have notPast : ¬steps+1 > tree.nodes.size*2+1 := by
        have bound := valid.base.budget
        dsimp only at bound
        omega
      have classified := GeneralBorrowExposedKnownRootWriteState.primary_classify initial location root index valid.base.frame rootPositive
      cases afterChildren with
      | false =>
        have positive : 1 ≤ weights.weight index := by
          have bound := weights.children index node present
          omega
        cases relation : GeneralBorrowExposedKnownRootWriteState.related initial root index with
        | EitherAccess =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write false false = some .EitherAccess := by simpa only [relation] using classified
          have isForeign : foreign initial index node none = false := by
            have nz : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write ≠ 0 := by
              intro zero
              have impossible := relation
              simp [GeneralBorrowExposedKnownRootWriteState.related,zero,Nat.ne_of_gt rootPositive] at impossible
            simp [foreign,onlyForeign,nz]
          unfold onlyForeign at exactRel
          have pushing := children_loop node.children (baseStack.push (index,true))
          simp only [forIn'_eq_forIn,pure] at pushing
          refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
          · simp only [scan,notForeign,tagBound]
            unfold_leaf_helpers
            simp [notPast,present,tagBound,notForeign,exactRel,effective,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp [exactRel,effective,pushing,expanded]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals simp_all [pushing,expanded,Id.run,bind,pure,LocationState.skipIfKnownNoop,AccessRelatedness.isForeign]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [pushing,expanded,Id.run,bind,pure,LocationState.skipIfKnownNoop,AccessRelatedness.isForeign]
          · exact expand weights data location witness baseStack index node steps valid present (by simp [isForeign])
          · rw [expanded_potential,potential_push]
            simp only [cost,Bool.false_eq_true,↓reduceIte]
            have bounded := weights.children index node present
            omega
        | LocalAccess =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write false false = some .LocalAccess := by simpa only [relation] using classified
          have isForeign : foreign initial index node none = false := by
            have nz : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write ≠ 0 := by
              intro zero
              have impossible := relation
              simp [GeneralBorrowExposedKnownRootWriteState.related,zero,Nat.ne_of_gt rootPositive] at impossible
            simp [foreign,onlyForeign,nz]
          unfold onlyForeign at exactRel
          have pushing := children_loop node.children (baseStack.push (index,true))
          simp only [forIn'_eq_forIn,pure] at pushing
          refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
          · simp only [scan,notForeign,tagBound]
            unfold_leaf_helpers
            simp [notPast,present,tagBound,notForeign,exactRel,effective,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp [exactRel,effective,pushing,expanded]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals simp_all [pushing,expanded,Id.run,bind,pure,LocationState.skipIfKnownNoop,AccessRelatedness.isForeign]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [pushing,expanded,Id.run,bind,pure,LocationState.skipIfKnownNoop,AccessRelatedness.isForeign]
          · exact expand weights data location witness baseStack index node steps valid present (by simp [isForeign])
          · rw [expanded_potential,potential_push]
            simp only [cost,Bool.false_eq_true,↓reduceIte]
            have bounded := weights.children index node present
            omega
        | ForeignAccess =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write false false = some .ForeignAccess := by simpa only [relation] using classified
          have zero := GeneralBorrowExposedKnownRootWriteState.foreign_zero initial root index relation
          have isForeign : foreign initial index node none = true := by simp [foreign,onlyForeign,zero]
          unfold onlyForeign at exactRel
          cases skipped : (effective location index node).skipIfKnownNoop .Write .ForeignAccess with
          | SkipSelfAndChildren =>
            dsimp only [effective] at skipped
            refine .inr ⟨(location,witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
            · simp only [scan,notForeign,tagBound]
              unfold_leaf_helpers
              simp [notPast,present,tagBound,notForeign,exactRel,skipped,effective,Id.run,bind,pure]
              try unfold_leaf_helpers
              try simp [exactRel,skipped,effective]
              all_goals try rw [exactRel]
              all_goals try unfold_leaf_helpers
              all_goals simp_all [onlyForeign,skipped,effective,Id.run,bind,pure]
              all_goals try unfold_leaf_helpers
              all_goals try simp_all [skipped,effective,Id.run,bind,pure]
            · exact pop weights data location witness baseStack index steps valid (by simp [cost];omega) zero
            · rw [potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              omega
          | Recurse =>
            dsimp only [effective] at skipped
            have pushing := children_loop node.children (baseStack.push (index,true))
            simp only [forIn'_eq_forIn,pure] at pushing
            refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
            · simp only [scan,notForeign,tagBound]
              unfold_leaf_helpers
              simp [notPast,present,tagBound,notForeign,exactRel,skipped,effective,Id.run,bind,pure]
              try unfold_leaf_helpers
              simp [exactRel,skipped,effective,pushing,expanded]
              all_goals try rw [exactRel]
              all_goals try unfold_leaf_helpers
              all_goals simp_all [onlyForeign,skipped,effective,pushing,expanded,Id.run,bind,pure]
              all_goals try unfold_leaf_helpers
              all_goals try simp_all [skipped,effective,pushing,expanded,Id.run,bind,pure]
            · exact expand weights data location witness baseStack index node steps valid present (fun _ => skipped)
            · rw [expanded_potential,potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              have bounded := weights.children index node present
              omega
      | true =>
        cases relation : GeneralBorrowExposedKnownRootWriteState.related initial root index with
        | EitherAccess =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write false false = some .EitherAccess := by simpa only [relation] using classified
          have isForeign : foreign initial index node none = false := by
            have nz : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write ≠ 0 := by
              intro zero
              have impossible := relation
              simp [GeneralBorrowExposedKnownRootWriteState.related,zero,Nat.ne_of_gt rootPositive] at impossible
            simp [foreign,onlyForeign,nz]
          unfold onlyForeign at exactRel
          refine .inr ⟨(materialized location index node,seen location index node none protections witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
          · simp only [scan,notForeign,tagBound]
            unfold_leaf_helpers
            simp [notPast,present,tagBound,notForeign,exactRel,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp [exactRel,materialized,seen,effective]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals simp_all [onlyForeign,materialized,seen,effective,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [materialized,seen,effective,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective,Nat.not_le_of_gt]
          · apply post weights data location _ witness _ baseStack index steps valid
            · intro query;rfl
            · exact materialized_profile tree location index node protections present valid.base.profile
            · intro query different
              unfold materialized Miri.TreeBorrows.UniValMap.orInsert
              split
              · rfl
              · exact GeneralBorrowFreshLocation.get_other _ index query node.defaultLocationState different
            · exact fun done => by simp [seen,done]
            · intro same
              have foundAt : tree.nodes.get data.witness = some node := by simpa only [same] using present
              have sameNode : node = data.node := Option.some.inj (foundAt.symm.trans data.present)
              have allows := GeneralBorrowExposedKnownRootWritePrimaryWitness.witness_allows data location valid.base.frame valid.base.profile index node present same
              have permits : ((effective location index data.node).permission.strongestAllowedLocalAccess (protections.contains data.node.tag)).allows .Write = true := by simpa only [sameNode] using allows
              simp [seen,sameNode,data.exposed,permits]
            · exact GeneralBorrowExposedNonleafCoherence.materialized_coherent tree location index node protections present valid.base.coherent
          · rw [potential_push]
            simp [cost]
        | LocalAccess =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write false false = some .LocalAccess := by simpa only [relation] using classified
          unfold onlyForeign at exactRel
          have recurse : (effective location index node).skipIfKnownNoop .Write .LocalAccess = .Recurse := rfl
          have nonzeroInitial := local_nonzero initial root index rootPositive relation
          have compatible := local_compatible tree initial location protections valid.base.frame valid.base.profile index node present (data.base.included index supported) nonzeroInitial
          obtain ⟨recorded,next,delta,record,access,good,localSupport,noSupport⟩ := GeneralBorrowExposedConditionalWritePermissions.visit
            (effective location index node) .LocalAccess (protections.contains node.tag)
            compatible (GeneralBorrowEvents.recurse_scheduled _ _ _ recurse)
          have currentZero : zero location index = false := by rw [zero_frame initial location valid.base.frame index];simp [zero,nonzeroInitial]
          have nextGood : GeneralBorrowExposedConditionalWritePermissions.Condition (zero location index) next (protections.contains node.tag) := by
            simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,currentZero,Bool.false_eq_true,ite_false] using good
          have support : node.isExposed = true → GeneralBorrowExposedConditionalWritePermissions.support next (protections.contains node.tag) =
              GeneralBorrowExposedConditionalWritePermissions.support (effective location index node) (protections.contains node.tag) := fun _ => localSupport rfl
          have cacheOK : ∀ oldLevel newLevel, (location.exposedCache.updateExposure tree.nodes index oldLevel newLevel).outcome = .ok () :=
            fun oldLevel newLevel => GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes data.base.depth index node present oldLevel newLevel
          refine .inr ⟨(updated tree location index node protections recorded next delta,
            seen location index node none protections witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
          · simp only [scan,notForeign,tagBound]
            unfold_leaf_helpers
            simp [notPast,present,tagBound,notForeign,exactRel,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp only [exactRel,or_insert_snd,record,access,LocationState.AccessResult.resultingState]
            simp [updated,write,materialized,seen,effective,cacheOK]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals simp_all [onlyForeign,record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective,Nat.not_le_of_gt]
            all_goals try split <;> simp_all [Bool.and_eq_false_iff]
          · apply post weights data location _ witness _ baseStack index steps valid
            · exact updated_frame tree location index node protections recorded next delta data.base.depth present support
            · exact updated_profile tree location index node protections recorded next delta present valid.base.profile (updated_frame tree location index node protections recorded next delta data.base.depth present support) nextGood
            · exact fun query different => updated_other tree location index query node protections recorded next delta different
            · exact fun done => by simp [seen,done]
            · intro same
              have foundAt : tree.nodes.get data.witness = some node := by simpa only [same] using present
              have sameNode : node = data.node := Option.some.inj (foundAt.symm.trans data.present)
              have allows := GeneralBorrowExposedKnownRootWritePrimaryWitness.witness_allows data location valid.base.frame valid.base.profile index node present same
              have permits : ((effective location index data.node).permission.strongestAllowedLocalAccess (protections.contains data.node.tag)).allows .Write = true := by simpa only [sameNode] using allows
              simp [seen,sameNode,data.exposed,permits]
            · exact GeneralBorrowExposedConditionalWriteCoherence.updated_coherent tree location index node protections recorded next delta .LocalAccess data.base.depth present valid.base.coherent record access
          · rw [potential_push]
            simp [cost]
        | ForeignAccess =>
          have exactRel : location.exposedCache.accessRelatedness root index .Write false false = some .ForeignAccess := by simpa only [relation] using classified
          have zero := GeneralBorrowExposedKnownRootWriteState.foreign_zero initial root index relation
          have isForeign : foreign initial index node none = true := by simp [foreign,onlyForeign,zero]
          unfold onlyForeign at exactRel
          have recurse := valid.base.pending index node (by simp) present isForeign
          have compatible := foreign_compatible tree initial location protections valid.base.frame valid.base.profile index node present (data.base.included index supported) zero
          obtain ⟨recorded,next,delta,record,access,good,localSupport,noSupport⟩ := GeneralBorrowExposedConditionalWritePermissions.visit
            (effective location index node) .ForeignAccess (protections.contains node.tag)
            compatible (GeneralBorrowEvents.recurse_scheduled _ _ _ recurse)
          have currentZero : GeneralBorrowExposedKnownRootWriteState.zero location index = true := by rw [zero_frame initial location valid.base.frame index];simp [GeneralBorrowExposedKnownRootWriteState.zero,zero]
          have nextGood : GeneralBorrowExposedConditionalWritePermissions.Condition (GeneralBorrowExposedKnownRootWriteState.zero location index) next (protections.contains node.tag) := by
            simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,currentZero,ite_true] using good
          have support : node.isExposed = true → GeneralBorrowExposedConditionalWritePermissions.support next (protections.contains node.tag) =
              GeneralBorrowExposedConditionalWritePermissions.support (effective location index node) (protections.contains node.tag) := by
            intro exposed
            have zeroCurrent : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write = 0 := by
              have eq : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write = GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write := congrArg UInt16.toNat (valid.base.frame index)
              rw [eq,zero]
            have oldZero := GeneralBorrowExposedConditionalAccessSupport.exposed_zero tree location protections valid.base.coherent data.base.short index node present exposed .Write zeroCurrent
            exact (noSupport oldZero).trans oldZero.symm
          have cacheOK : ∀ oldLevel newLevel, (location.exposedCache.updateExposure tree.nodes index oldLevel newLevel).outcome = .ok () :=
            fun oldLevel newLevel => GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes data.base.depth index node present oldLevel newLevel
          refine .inr ⟨(updated tree location index node protections recorded next delta,
            seen location index node none protections witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
          · simp only [scan,notForeign,tagBound]
            unfold_leaf_helpers
            simp [notPast,present,tagBound,notForeign,exactRel,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp only [exactRel,or_insert_snd,record,access,LocationState.AccessResult.resultingState]
            simp [updated,write,materialized,seen,effective,cacheOK]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals simp_all [onlyForeign,record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective,Nat.not_le_of_gt]
            all_goals try split <;> simp_all [Bool.and_eq_false_iff]
          · apply post weights data location _ witness _ baseStack index steps valid
            · exact updated_frame tree location index node protections recorded next delta data.base.depth present support
            · exact updated_profile tree location index node protections recorded next delta present valid.base.profile (updated_frame tree location index node protections recorded next delta data.base.depth present support) nextGood
            · exact fun query different => updated_other tree location index query node protections recorded next delta different
            · exact fun done => by simp [seen,done]
            · intro same
              have foundAt : tree.nodes.get data.witness = some node := by simpa only [same] using present
              have sameNode : node = data.node := Option.some.inj (foundAt.symm.trans data.present)
              have allows := GeneralBorrowExposedKnownRootWritePrimaryWitness.witness_allows data location valid.base.frame valid.base.profile index node present same
              have permits : ((effective location index data.node).permission.strongestAllowedLocalAccess (protections.contains data.node.tag)).allows .Write = true := by simpa only [sameNode] using allows
              simp [seen,sameNode,data.exposed,permits]
            · exact GeneralBorrowExposedConditionalWriteCoherence.updated_coherent tree location index node protections recorded next delta .ForeignAccess data.base.depth present valid.base.coherent record access
          · rw [potential_push]
            simp [cost]
  have run : ∀ bound (state : LoopState), potential weights.weight state.2.2.2.1 = bound → Invariant weights data state →
      Invariant weights data (Lean.Loop.forIn (m := Id) {} state scan) ∧ (Lean.Loop.forIn (m := Id) {} state scan : Id LoopState).2.1 = true := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro state measured valid
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rcases step state valid with done | more
      · obtain ⟨final,actual,preserved,seen⟩ := done
        simpa only [actual,bind,pure] using And.intro preserved seen
      · obtain ⟨next,actual,preserved,smaller⟩ := more
        simp only [actual,bind]
        exact ih _ (by omega) next rfl preserved
  have retained := run _ (initial,false,.Completed,#[(root,false)],0) rfl
    (GeneralBorrowExposedScopedWriteFramePrimaryInvariant.initial weights data)
  simp only [retained.1.base.status,retained.2,Bool.not_true,Bool.not_false,Bool.and_false,Bool.false_and,Bool.true_and,Bool.false_eq_true,beq_self_eq_true,↓reduceIte]
  exact ⟨True.intro,retained.1.base.frame,retained.1.base.profile,retained.1.base.coherent,retained.1.base.outside⟩

end DuplicatePrefix.GeneralBorrowExposedScopedWriteFramePrimaryLoop
