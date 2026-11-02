import duplicate_prefix.GeneralBorrowEffectfulRetagReadyFormation
import duplicate_prefix.GeneralBorrowEffectfulRetagReady
import duplicate_prefix.GeneralBorrowConcreteChildCausalOrder
import duplicate_prefix.GeneralBorrowEffectfulTreeUpdateFrame
namespace DuplicatePrefix.GeneralBorrowEffectfulRetagCausalOrder
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.TreeBorrows.RetagPipeline
open GeneralBorrowWildcardParentTagOrder GeneralBorrowEffectfulTreeUpdateFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable section
open Lean Elab Term in
elab "causal_access_tree" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".accessTreeForReborrow" && name.toString.contains "RetagPipelineEffectful" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected exact actual effectful reborrow access core"

theorem access_frame (tree : BorrowTree) (provenance : ProvenanceExtra) (offset len : Size)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) :
    (tree.performBorrowAccessRange provenance offset len kind protections mode).tree.nodes = tree.nodes ∧
    (tree.performBorrowAccessRange provenance offset len kind protections mode).tree.tagMapping = tree.tagMapping := by
  cases provenance <;> unfold BorrowTree.performBorrowAccessRange
  all_goals simp only [Id.run,bind,pure]
  all_goals split <;> try simp only [Id.run,bind,pure]
  all_goals repeat' split
  all_goals simp_all

open Lean Elab Term in
elab "causal_run_reborrow" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".runReborrow" && name.toString.contains "RetagPipelineEffectful" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected exact actual effectful reborrow core"

/-- Actual effectful parent-access loop followed by the actual child constructor.
The data-race leaf is arbitrary: its type changes only External state. -/
theorem access_preserves {K E H : Type} [DecidableEq K]
    (result : Effectful.Result K E H) (request : Request) (policy : RetagPolicy.NewPermission)
    (tag parentTag : BorTag) (id : AllocId) (offset : Size) (inside : DedupRangeMap LocationState)
    (mutable : Mutability) (effects : Effectful.Hooks K E H)
    (prepared : AllTrees (Ready tag parentTag id) result.state.memory) :
    AllTrees (fun _ tree => ParentTagOrder tree)
      (causal_access_tree result request policy tag ⟨id,offset,.concrete parentTag⟩ inside mutable effects).state.memory := by
  unfold_entry_helper ".accessTreeForReborrow"
  unfold_entry_helper ".addEvent"
  unfold_entry_helper ".fail"
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_fresh_modify_scan
  let P := Ready tag parentTag id
  let property := fun state : Option (Effectful.Result K E H) × Effectful.Result K E H =>
    AllTrees P state.2.state.memory ∧ ∀ returned,state.1=some returned→AllTrees P returned.state.memory
  have step : ∀segment∈inside.iterAll.toList,∀state,property state→property (scan segment state).value := by
    intro segment member state good
    rcases state with ⟨returned,current⟩
    dsimp only [property] at good ⊢
    cases associated : segment.data.permission.associatedAccess with
    | none => simpa only [scan,associated,ForInStep.value] using (show property (none,current) from ⟨good.1,by simp⟩)
    | some kind =>
      cases readonly : (kind == .Write && mutable == .Not) with
      | true => simp only [scan,associated,readonly,↓reduceIte,ForInStep.value];exact ⟨good.1,fun result equal => by cases equal;exact good.1⟩
      | false =>
        cases added : offset.add (Size.ofBytes segment.range.start) with
        | error error => simp only [scan,associated,readonly,Bool.false_eq_true,↓reduceIte,added,ForInStep.value];exact ⟨good.1,fun result equal => by cases equal;exact good.1⟩
        | ok absolute =>
          cases ended : absolute.add (Size.ofBytes (segment.range.stop-segment.range.start)) with
          | error error => simp only [scan,associated,readonly,Bool.false_eq_true,↓reduceIte,added,ended,ForInStep.value];exact ⟨good.1,fun result equal => by cases equal;exact good.1⟩
          | ok stop =>
            cases found : current.state.memory.live.find? (fun row => row.1 == id) with
            | none => simp only [scan,associated,readonly,Bool.false_eq_true,↓reduceIte,added,ended,found,ForInStep.value];exact ⟨good.1,fun result equal => by cases equal;exact good.1⟩
            | some row =>
              have key : row.1 = id := by simpa only [beq_iff_eq] using Array.find?_some found
              have before := good.1 row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
              let accessed := row.2.allocation.extra.performBorrowAccessRange (.concrete parentTag) absolute
                (Size.ofBytes (segment.range.stop-segment.range.start)) kind current.state.global.protectedTags .VisitChildrenOfAccessed
              have frame := access_frame row.2.allocation.extra (.concrete parentTag) absolute
                (Size.ofBytes (segment.range.stop-segment.range.start)) kind current.state.global.protectedTags .VisitChildrenOfAccessed
              have replacement : P id accessed.tree := by
                rw [key] at before
                exact before.frame frame.1 frame.2
              cases stored : entry_tree_update current.state.memory id accessed.tree with
              | error error => simp only [scan,associated,readonly,Bool.false_eq_true,↓reduceIte,added,ended,found,accessed,stored,ForInStep.value];exact ⟨good.1,fun result equal => by cases equal;exact good.1⟩
              | ok memory =>
                have nextGood := update_success P current.state.memory id accessed.tree good.1 replacement memory stored
                simp only [scan,associated,readonly,Bool.false_eq_true,↓reduceIte,added,ended,found]
                dsimp only [accessed] at stored
                simp only [stored]
                repeat' first
                  | split
                  | exact ⟨nextGood,fun result equal => by cases equal;exact nextGood⟩
                  | exact ⟨nextGood,by simp⟩
  have initial : property (none,result) := ⟨prepared,by simp⟩
  have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,result) initial
  generalize folded : forIn inside.iterAll.toList (none,result) scan = final at maintained ⊢
  rcases final with ⟨returned,current⟩
  cases returned with
  | some out =>
    intro row member
    exact (maintained.2 out rfl row member).order
  | none =>
    have currentReady : AllTrees P current.state.memory := maintained.1
    have currentOrder : AllTrees (fun _ tree => ParentTagOrder tree) current.state.memory := by
      intro row member
      exact (currentReady row member).order
    cases found : current.state.memory.live.find? (fun row => row.1 == id) with
    | none => simpa only [found] using currentOrder
    | some row =>
      have key : row.1 = id := by simpa only [beq_iff_eq] using Array.find?_some found
      have ready := currentReady row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
      rw [key] at ready
      obtain ⟨parent,node,tagged,present⟩ := ready.parent rfl
      obtain ⟨mapping,index,inserted,vacant⟩ := ready.slot
      obtain ⟨depth⟩ := ready.depth
      let child := row.2.allocation.extra.newChild offset (.concrete parentTag) tag inside policy.outsidePermission policy.protector.isSome
      have childOrder : ParentTagOrder child.tree :=
        GeneralBorrowConcreteChildCausalOrder.inserted_order row.2.allocation.extra depth ready.order parentTag tag
          parent node mapping index inserted vacant tagged present (ready.below parent node present)
          offset inside policy.outsidePermission policy.protector.isSome
      cases stored : entry_tree_update current.state.memory id child.tree with
      | error error =>
        dsimp only [child] at stored
        simpa only [found,stored] using currentOrder
      | ok memory =>
        have nextOrder := update_success (fun _ tree => ParentTagOrder tree) current.state.memory id child.tree currentOrder childOrder memory stored
        simp only [found]
        dsimp only [child] at stored
        simp only [stored]
        split <;> exact nextOrder
/-- Lift the actual allocation-local reborrow dispatch; all early-error paths
retain the original causal graph property. The parent binding is initial data. -/
theorem run_preserves {K E H : Type} [DecidableEq K]
    (state : MachineState K) (request : Request) (policy : RetagPolicy.NewPermission)
    (size : Size) (tag parentTag : BorTag) (id : AllocId) (offset : Size)
    (events : Array Event) (external : E) (effects : Effectful.Hooks K E H)
    (resolved : request.hooks.allocationResolution = some ⟨id,offset,.concrete parentTag⟩)
    (prepared : AllTrees (Ready tag parentTag id) state.memory) :
    AllTrees (fun _ tree => ParentTagOrder tree)
      (causal_run_reborrow state request policy size tag events external effects).state.memory := by
  have direct : AllTrees (fun _ tree => ParentTagOrder tree) state.memory := by
    intro row member
    exact (prepared row member).order
  unfold_entry_helper ".runReborrow"
  unfold_entry_helper ".finish"
  unfold_entry_helper ".addEvent"
  unfold_entry_helper ".fail"
  simp only [resolved,Id.run,bind,pure]
  repeat' first
    | exact direct
    | exact access_preserves _ _ _ _ _ _ _ _ _ _ prepared
    | split

/-- Actual public EFFECTFUL retag dispatch preserves causal parent-tag order
for a concrete source bound to an original live parent. This is a graph
invariant on every outcome, not a successful-retag or NoUB assertion. Every
internal packet is formed from original runtime/allocator/source data. -/
theorem preserves {K E H : Type} [DecidableEq K]
    (state : MachineState K) (request : Request) (external : E) (effects : Effectful.Hooks K E H)
    (unique : (state.memory.live.toList.map Prod.fst).Nodup)
    (runtime : ∀ row ∈ state.memory.live.toList, DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra state.global)
    (orders : AllTrees (fun _ tree => ParentTagOrder tree) state.memory)
    (room : ∀ row ∈ state.memory.live.toList, row.2.allocation.extra.nodes.size+1 ≤ 4294967295)
    (id : AllocId) (offset : Size) (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag = some parent)
    (nodePresent : entry.allocation.extra.nodeAt parent = some node)
    (resolved : request.hooks.allocationResolution = some ⟨id,offset,.concrete parentTag⟩) :
    AllTrees (fun _ tree => ParentTagOrder tree)
      (Effectful.retagPointerValue state request external effects).state.memory := by
  have prepared := GeneralBorrowEffectfulRetagReadyFormation.forms state.memory state.global unique runtime orders room
    id entry present parentTag parent node tagged nodePresent
  have next (global : GlobalState) (tag : BorTag) (allocated : state.global.newPointerTag = .ok (global,tag))
      (policy : RetagPolicy.NewPermission) (size : Size) (events : Array Event) :
      AllTrees (fun _ tree => ParentTagOrder tree)
        (causal_run_reborrow {state with global:=global} request policy size tag events external effects).state.memory := by
    have tagEq : tag = state.global.nextPointerTag := by
      unfold GlobalState.newPointerTag at allocated
      split at allocated
      · cases allocated
      · have pairs := Except.ok.inj allocated
        exact (congrArg Prod.snd pairs).symm
    subst tag
    exact run_preserves {state with global:=global} request policy size state.global.nextPointerTag parentTag id offset events external effects resolved prepared
  unfold Effectful.retagPointerValue
  unfold_entry_helper ".finishWithoutRetag"
  unfold_entry_helper ".addEvent"
  unfold_entry_helper ".fail"
  simp only [Id.run,bind,pure]
  repeat' first
    | exact orders
    | (apply next <;> assumption)
    | split

end
end DuplicatePrefix.GeneralBorrowEffectfulRetagCausalOrder
