import duplicate_prefix.GeneralBorrowSparseLeafPhysicalScalar
import duplicate_prefix.GeneralBorrowWildcardSubtreeState
namespace DuplicatePrefix.GeneralBorrowSparseLeafPhysical
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf GeneralBorrowWildcardSubtreeState GeneralBorrowSparseExposedLeafState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] UniValMap.insert UniValMap.orInsert
noncomputable section

/-- A physical supporting leaf executes real local materialization/record and
Read/Write, including lazy reservation activation. It preserves the complete
cache because both local permission strengths remain Write. Only its own
permission row can change; no successful leaf callback is an input. -/
theorem access (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodeAt root=some node) (leaf : node.children=#[]) (exposed : node.isExposed=true)
    (bound : ∀tag,maximum=some tag→node.tag.value≤tag.value)
    (positive : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind≠0)
    (good : GeneralBorrowExposedConditionalWritePermissions.Compatible (effective location root node) .LocalAccess (protections.contains node.tag)) :
    ∃after,tree.performWildcardAccessAt location root maximum kind protections false=⟨after,.Completed⟩ ∧
      after.exposedCache=location.exposedCache ∧
      GeneralBorrowExposedConditionalWritePermissions.Compatible (effective after root node) .LocalAccess (protections.contains node.tag) ∧
      (∀query,query≠root→after.perms.get query=location.perms.get query) := by
  have lookup : tree.nodes.get root=some node:=present
  let state:=effective location root node
  let recorded : LocationState:={state with idempotentForeignAccess:=.None}
  have recordedGood : GeneralBorrowExposedConditionalWritePermissions.Compatible recorded .LocalAccess (protections.contains node.tag):=good
  obtain ⟨next,delta,actual,nextGood⟩:=local_transition recorded (protections.contains node.tag) recordedGood kind
  have record : state.recordNewAccess kind .LocalAccess=.Recorded recorded := by
    cases kind <;> rfl
  have oldLevel:=level_write state _ good
  have newLevel:=level_write next _ nextGood
  have updateSame : ∀cache : ExposedCache,cache.updateExposure tree.nodes root
      (state.permission.strongestAllowedLocalAccess (protections.contains node.tag))
      (next.permission.strongestAllowedLocalAccess (protections.contains node.tag))=⟨cache,.ok ()⟩ := by
    intro cache
    rw [oldLevel,newLevel]
    rfl
  have permits : (state.permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind=true := by rw [oldLevel];cases kind <;>rfl
  have cutoff : onlyForeign node maximum=false := by
    cases maximum with
    | none=>rfl
    | some tag=>simp only [onlyForeign];exact decide_eq_false (UInt64.not_lt.mpr (bound tag rfl))
  have guard : (maximum.isNone || maximum.any (fun tag=>tag.value≥node.tag.value))=true := by
    cases maximum with
    | none=>rfl
    | some tag=>simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bound tag rfl
  have related : location.exposedCache.accessRelatedness root root kind false (onlyForeign node maximum)=some .LocalAccess := by
    rw [cutoff]
    cases kind <;> simp_all [ExposedCache.accessRelatedness,GeneralBorrowWildcardRelatednessBounds.count,Id.run,pure]
  unfold onlyForeign at related
  have nonempty : 0<tree.nodes.size := by have bounded:=GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node present;change root.toNat<tree.nodes.size at bounded;omega
  have notPast : ¬2>tree.nodes.size*2+1:=by omega
  have notPast1 : ¬1>tree.nodes.size*2+1:=by omega
  let after:=write location root node recorded next
  have rootStored : after.perms.get root=some next:=write_same location root node recorded next
  refine ⟨after,?_,?_,?_,?_⟩
  · unfold BorrowTree.performWildcardAccessAt
    simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step1 : scan () (location,false,.Completed,#[(root,false)],0)=.yield (location,false,.Completed,#[(root,true)],1) := by
      simp only [scan]
      unfold_leaf_helpers
      cases maximum <;>
        simp_all [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,leaf,Id.run,bind,pure]
      all_goals unfold_leaf_helpers
      all_goals simp [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,leaf]
    have step2 : scan () (location,false,.Completed,#[(root,true)],1)=.yield (after,true,.Completed,#[],2) := by
      simp only [scan]
      unfold_leaf_helpers
      have orState:=or_insert_snd location root node
      have recordedActual : (location.perms.orInsert root node.defaultLocationState).2.recordNewAccess kind .LocalAccess=.Recorded recorded:=by rw [orState];exact record
      cases maximum <;> cases stored : location.perms.get root <;>
        simp_all [effective,UniValMap.orInsert,after,write,recorded,state,LocationState.AccessResult.resultingState,updateSame,bind,pure]
      all_goals intro impossible;omega
    have step3 : scan () (after,true,.Completed,#[],2)=.done (after,true,.Completed,#[],2) := by simp [scan,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step1,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step2,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step3,bind,pure]
    rfl
  · rfl
  · simpa only [effective,rootStored,Option.getD_some] using nextGood
  · intro query different
    exact write_other location root query node recorded next different
end
end DuplicatePrefix.GeneralBorrowSparseLeafPhysical
