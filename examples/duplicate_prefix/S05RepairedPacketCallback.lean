import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorizationRepaired
import duplicate_prefix.S05ZeroCellActualCallRepaired
import duplicate_prefix.GeneralBorrowWildcardSubtreeStack

/-! The repaired A callback at the actual closed-copy boundary: source Read
has happened; destination Write normal access and the preceding root0 callback
are computed before the A callback on byte [1,2). All generated
FnEntry/shared/helper nodes and real protectors are retained. This is one
component of the real copy, not whole-call Return or all-input coverage. -/
namespace DuplicatePrefix.S05RepairedPacketCallback
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix
open DuplicatePrefixCallbackVisitAuthorizationRepaired
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

noncomputable section
abbrev tree := S05ZeroCellActualCallRepaired.PureTree.read.tree
abbrev held := S05ZeroCellActualCallRepaired.PureTree.held
def readLocation : LocationTree := (tree.locations.entries[1]'(by cbv)).data
def source : UniIndex := (tree.indexOfTag S05ZeroCellActualCallRepaired.PureTree.tag).getD (ix 0)
def normal := tree.performNormalAccessAt readLocation source .Write held .VisitChildrenOfAccessed
def accessedRoot : Option UniIndex := UniIndex.ofNat? normal.access.root
def maximum : Option BorTag := accessedRoot.bind (fun i => (tree.nodes.get i).map TreeNode.tag)
def firstRoot : UniIndex := (tree.roots[0]?).getD (ix 0)
def prior := tree.performWildcardAccessAt normal.location firstRoot maximum .Write held false
def initial : LocationTree := prior.location
def node (i : Nat) : TreeNode :=
  (tree.nodeAt (ix i)).getD ⟨tag 1,none,#[],.Disabled,.None,false,none⟩
/-- The child result is computed by the real visitor, not chosen as a literal. -/
def child := tree.performWildcardAccessAt initial (ix 4) maximum .Write held true
def afterD := GeneralBorrowWildcardVirtualLeaf.materialized child.location (ix 2) (node 2)
def afterA := GeneralBorrowWildcardVirtualLeaf.materialized afterD (ix 1) (node 1)

theorem boundary : (tree.locations.entries[1]'(by cbv)).range = ⟨1,2⟩ := by cbv

/-- Actual concrete source, normal root, tag cutoff and root iteration order.
All are computed from the released generated tree; no replacement forest is used. -/
theorem preceding_path :
    tree.indexOfTag S05ZeroCellActualCallRepaired.PureTree.tag = some source ∧
    normal.outcome = .ok () ∧ normal.access.status = .Completed ∧
    accessedRoot = some (ix 3) ∧ maximum = some (tag 4) ∧
    tree.roots[0]? = some firstRoot ∧ firstRoot = ix 0 ∧
    tree.roots[1]? = some (ix 1) ∧ prior.status = .Completed := by cbv; simp

theorem child_completed : child.status = .Completed := by cbv

theorem guards :
    PostchildrenNoop ((child.location.perms.get (ix 2)).getD (node 2).defaultLocationState)
      .Write (held.contains (node 2).tag) (some .ForeignAccess) ∧
    PostchildrenNoop ((afterD.perms.get (ix 1)).getD (node 1).defaultLocationState)
      .Write (held.contains (node 1).tag) (some .ForeignAccess) := by
  constructor <;> cbv <;> simp

/-- Both new branches are admissible even though entry-time classification
was Either. Postchildren classification uses the computed child cache. -/
theorem classification :
    initial.exposedCache.accessRelatedness (ix 1) (ix 2) .Write true false = some .EitherAccess ∧
    child.location.exposedCache.accessRelatedness (ix 1) (ix 2) .Write true false = some .ForeignAccess ∧
    initial.exposedCache.accessRelatedness (ix 1) (ix 1) .Write true false = some .EitherAccess ∧
    afterD.exposedCache.accessRelatedness (ix 1) (ix 1) .Write true false = some .ForeignAccess := by cbv

theorem admitted :
    Authorized ((child.location.perms.get (ix 2)).getD (node 2).defaultLocationState)
      .Write (held.contains (node 2).tag) (some .EitherAccess) (some .ForeignAccess) ∧
    Authorized ((afterD.perms.get (ix 1)).getD (node 1).defaultLocationState)
      .Write (held.contains (node 1).tag) (some .EitherAccess) (some .ForeignAccess) := by
  exact ⟨.inr ⟨by cbv,guards.1⟩,.inr ⟨by cbv,guards.2⟩⟩

/-- Direct application of the reusable source theorem at these actual
child-derived poststates. This is separate from the concrete entry path below;
no choice of existential loop bodies is identified by assumption. -/
theorem source_postvisits :
    ∃ scan : Unit → (LocationTree × Bool × BorrowTree.WildcardAccessStatus ×
        Array (UniIndex × Bool) × Nat) → Id (ForInStep (LocationTree × Bool ×
        BorrowTree.WildcardAccessStatus × Array (UniIndex × Bool) × Nat)),
      (tree.performWildcardAccessAt initial (ix 1) maximum .Write held true =
        let final := Lean.Loop.forIn {} (initial,false,.Completed,#[(ix 1,false)],0) scan
        ⟨final.1, if final.2.2.1 == .Completed && !final.2.1 && !true then
          .NoValidExposedReferences (ix 1) none else final.2.2.1⟩) ∧
      scan () (child.location,false,.Completed,#[(ix 1,true),(ix 2,true)],4) =
        .yield (afterD,false,.Completed,#[(ix 1,true)],5) ∧
      scan () (afterD,false,.Completed,#[(ix 1,true)],5) =
        .yield (afterA,false,.Completed,#[],6) := by
  obtain ⟨scan,identity,post⟩ := actual_postchildren tree initial (ix 1)
    maximum .Write held true
  refine ⟨scan,identity,?_,?_⟩
  · have step := post child.location (ix 2) (node 2) #[(ix 1,true)] 4 false
      (by cbv) (by cbv) (by cbv) guards.1
    simpa only [afterD,show (node 2).isExposed = false by cbv,
      Bool.false_and,Bool.false_or,Array.push,List.concat,Nat.reduceAdd] using step
  · have step := post afterD (ix 1) (node 1) #[] 5 false
      (by cbv) (by cbv) (by cbv) guards.2
    simpa only [afterA,show (node 1).isExposed = false by cbv,
      Bool.false_and,Bool.false_or,Array.push,List.concat,Nat.reduceAdd] using step

private theorem pre_nodes :
    tree.nodes.get (ix 1) = some (node 1) ∧ tree.nodes.get (ix 2) = some (node 2) ∧
    tree.nodes.get (ix 4) = some (node 4) ∧
    (node 1).children = #[ix 2] ∧ (node 2).children = #[ix 4] ∧ (node 4).children = #[] ∧
    (node 1).tag = tag 2 ∧ (node 2).tag = tag 3 ∧ (node 4).tag = tag 5 ∧
    tree.nodes.size = 11 := by cbv; simp

private theorem pre_v :
    initial.exposedCache.accessRelatedness (ix 1) (ix 4) .Write true true = some .ForeignAccess ∧
    ((initial.perms.get (ix 4)).getD (node 4).defaultLocationState).skipIfKnownNoop
      .Write .ForeignAccess = .Recurse := by cbv

/-- A continuous finite path in the ACTUAL callback loop. The pending D/A
postvisits are reached only after V's real transition/cache update. -/
theorem component_path :
    tree.performWildcardAccessAt initial (ix 1) maximum .Write held true =
      ⟨afterA,.Completed⟩ := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step0 : scan () (initial,false,.Completed,#[(ix 1,false)],0) =
      .yield (initial,false,.Completed,#[(ix 1,true),(ix 2,false)],1) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [pre_nodes,pre_nodes.1,pre_nodes.2.1,pre_nodes.2.2.1,
      pre_nodes.2.2.2.1,pre_nodes.2.2.2.2.1,pre_nodes.2.2.2.2.2.1,
      pre_nodes.2.2.2.2.2.2.1,pre_nodes.2.2.2.2.2.2.2.1,
      pre_nodes.2.2.2.2.2.2.2.2.1,pre_nodes.2.2.2.2.2.2.2.2.2,
      preceding_path.2.2.2.2.1,classification.1,classification.2.2.1,
      pre_v.1,pre_v.2,tag,Id.run,bind,pure,
      GeneralBorrowWildcardSubtreeStack.children_loop]
    all_goals unfold_leaf_helpers
    all_goals simp [pre_v.2,Id.run,bind,pure]
  have step1 : scan () (initial,false,.Completed,#[(ix 1,true),(ix 2,false)],1) =
      .yield (initial,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,false)],2) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [pre_nodes,pre_nodes.1,pre_nodes.2.1,pre_nodes.2.2.1,
      pre_nodes.2.2.2.1,pre_nodes.2.2.2.2.1,pre_nodes.2.2.2.2.2.1,
      pre_nodes.2.2.2.2.2.2.1,pre_nodes.2.2.2.2.2.2.2.1,
      pre_nodes.2.2.2.2.2.2.2.2.1,pre_nodes.2.2.2.2.2.2.2.2.2,
      preceding_path.2.2.2.2.1,classification.1,classification.2.2.1,
      pre_v.1,pre_v.2,tag,Id.run,bind,pure,
      GeneralBorrowWildcardSubtreeStack.children_loop]
    all_goals unfold_leaf_helpers
    all_goals simp [pre_v.2,Id.run,bind,pure]
  have step2 : scan () (initial,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,false)],2) =
      .yield (initial,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,true)],3) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [pre_nodes,pre_nodes.1,pre_nodes.2.1,pre_nodes.2.2.1,
      pre_nodes.2.2.2.1,pre_nodes.2.2.2.2.1,pre_nodes.2.2.2.2.2.1,
      pre_nodes.2.2.2.2.2.2.1,pre_nodes.2.2.2.2.2.2.2.1,
      pre_nodes.2.2.2.2.2.2.2.2.1,pre_nodes.2.2.2.2.2.2.2.2.2,
      preceding_path.2.2.2.2.1,classification.1,classification.2.2.1,
      pre_v.1,pre_v.2,tag,Id.run,bind,pure,
      GeneralBorrowWildcardSubtreeStack.children_loop]
    all_goals unfold_leaf_helpers
    all_goals simp [pre_v.2,Id.run,bind,pure]
  have step3 : scan () (initial,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,true)],3) =
      .yield (child.location,false,.Completed,#[(ix 1,true),(ix 2,true)],4) := by
    simp only [scan]
    unfold_leaf_helpers
    cbv
  have step4 : scan () (child.location,false,.Completed,#[(ix 1,true),(ix 2,true)],4) =
      .yield (afterD,false,.Completed,#[(ix 1,true)],5) := by
    simp only [scan]
    unfold_leaf_helpers
    cbv
  have step5 : scan () (afterD,false,.Completed,#[(ix 1,true)],5) =
      .yield (afterA,false,.Completed,#[],6) := by
    simp only [scan]
    unfold_leaf_helpers
    cbv
  have stop : scan () (afterA,false,.Completed,#[],6) =
      .done (afterA,false,.Completed,#[],6) := by simp [scan,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step0,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step3,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step4,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step5,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [stop,bind,pure]

/-- The newly admitted parent visits retain the child's exact current cache. -/
theorem child_effects_retained : afterA.exposedCache = child.location.exposedCache ∧
    afterA.perms.get (ix 4) = child.location.perms.get (ix 4) := by
  constructor
  · rfl
  · cbv

end
end DuplicatePrefix.S05RepairedPacketCallback
