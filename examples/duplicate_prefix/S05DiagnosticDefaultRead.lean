import duplicate_prefix.S05DiagnosticLenRelease
import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowFreshResult
import duplicate_prefix.GeneralBorrowHomogeneousFullModify
namespace DuplicatePrefix.S05DiagnosticDefaultRead
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState GeneralBorrowNodeUpdate RangeMapNonempty
open S05DiagnosticFnEntryRead (ix tag original a d b v)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def tree := S05DiagnosticLenRelease.released
def location := S05DiagnosticLenRelease.afterNormal
def protections := S05DiagnosticSharedRead.protections
def afterNormal : LocationTree := location
def afterRead : BorrowTree := {tree with locations := homogeneous 2 afterNormal}
/-- Frozen descendants are skipped by the actual foreign Read visitor. -/
theorem normal :
    (tree.performNormalAccessAt location (ix 6) .Read protections .VisitChildrenOfAccessed).location = afterNormal ∧
    (tree.performNormalAccessAt location (ix 6) .Read protections .VisitChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location (ix 6) .Read protections .VisitChildrenOfAccessed).outcome = .ok () := by
  with_unfolding_all decide +kernel
theorem primary : tree.performWildcardAccessAt afterNormal (ix 0) (some (tag 4)) .Read protections false =
    ⟨afterNormal,.Completed⟩ := by
  exact GeneralBorrowWildcardLeaf.access tree afterNormal (ix 0) original (tag 4) .Read protections
    ⟨rfl,rfl,rfl,by decide +kernel,rfl,by decide +kernel⟩
theorem other : tree.performWildcardAccessAt afterNormal (ix 1) (some (tag 4)) .Read protections true =
    ⟨afterNormal,.Completed⟩ := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have s1 : scan () (afterNormal,false,.Completed,#[(ix 1,false)],0) =
      .yield (afterNormal,false,.Completed,#[(ix 1,true),(ix 2,false)],1) := by rfl
  have s2 : scan () (afterNormal,false,.Completed,#[(ix 1,true),(ix 2,false)],1) =
      .yield (afterNormal,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,false)],2) := by rfl
  have s3 : scan () (afterNormal,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,false)],2) =
      .yield (afterNormal,false,.Completed,#[(ix 1,true),(ix 2,true)],3) := by rfl
  have s4 : scan () (afterNormal,false,.Completed,#[(ix 1,true),(ix 2,true)],3) =
      .yield (afterNormal,false,.Completed,#[(ix 1,true)],4) := by rfl
  have s5 : scan () (afterNormal,false,.Completed,#[(ix 1,true)],4) =
      .yield (afterNormal,false,.Completed,#[],5) := by rfl
  have stop : scan () (afterNormal,false,.Completed,#[],5) =
      .done (afterNormal,false,.Completed,#[],5) := by rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s3,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s4,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s5,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [stop,bind,pure]
  rfl
theorem callback :
    source_access_status (source_tree_access_at tree location (some (ix 6)) .Read protections .VisitChildrenOfAccessed ⟨0,2⟩) = none ∧
    source_access_location (source_tree_access_at tree location (some (ix 6)) .Read protections .VisitChildrenOfAccessed ⟨0,2⟩) = afterNormal := by
  simp_tree_helpers
  simp only [show (ChildrenVisitMode.VisitChildrenOfAccessed == ChildrenVisitMode.SkipChildrenOfAccessed) = false from rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [normal.1,normal.2.1,normal.2.2,beq_self_eq_true,Bool.false_eq_true,↓reduceIte]
  have root : (tree.performNormalAccessAt location (ix 6) .Read protections .VisitChildrenOfAccessed).access.root = 3 := by decide +kernel
  simp only [root]
  change _
  simp only [UniIndex.ofNat?,show (3:Nat) ≤ 4294967295 from by decide,↓reduceIte]
  change _
  simp only [show tree.roots = #[ix 0,ix 1,ix 3] from rfl,
    show ((some (⟨UInt32.ofNat 3⟩ : UniIndex)).bind fun root => (tree.nodes.get root).map TreeNode.tag) = some (tag 4) from rfl,
    Array.size_push,Array.size_empty,Array.getElem?_eq_getElem,
    Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, show #[ix 0,ix 1,ix 3].size = 3 from rfl]
  simp only [show List.range' 0 3 = [0,1,2] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [Option.isNone_none, Bool.not_false, Bool.true_and, ↓reduceIte,
    show (some (⟨UInt32.ofNat 3⟩ : UniIndex) != some (ix 0)) = true from rfl,
    show (some (⟨UInt32.ofNat 3⟩ : UniIndex) != some (ix 1)) = true from rfl,
    show (some (⟨UInt32.ofNat 3⟩ : UniIndex) != some (ix 3)) = false from rfl,
    show ((0:Nat) != 0) = false from rfl, show ((1:Nat) != 0) = true from rfl,
    show #[ix 0,ix 1,ix 3][0]? = some (ix 0) from rfl,
    show #[ix 0,ix 1,ix 3][1]? = some (ix 1) from rfl,
    show #[ix 0,ix 1,ix 3][2]? = some (ix 3) from rfl,
    primary,other, bne_self_eq_false, Bool.false_eq_true]
  exact ⟨trivial,trivial⟩

/-- Actual whole-range Read on the exact source allocation returned by len. -/
theorem read :
    let result := tree.performBorrowAccessRange (.concrete (tag 8)) Size.ZERO (Size.ofBytes 2)
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = afterRead := by
  have result := GeneralBorrowHomogeneousSourceAccess.full tree location 2 (by decide) rfl
    (.concrete (tag 8)) (some (ix 6)) .Read protections .VisitChildrenOfAccessed
    ⟨by decide +kernel,by decide⟩ callback.1
  simpa only [callback.2,afterRead] using result

def parent : TreeNode := {S05DiagnosticLenRead.parent with children := #[ix 7,ix 9]}
def child : TreeNode := GeneralBorrowFreshDefaultChild.child (tag 12) (ix 6)
def nextLocation : LocationTree := {afterNormal with perms := afterNormal.perms.insert (ix 9) GeneralBorrowFreshDefaultChild.inside}
def nextTree : BorrowTree := {
  tagMapping := ⟨S05DiagnosticLenRelease.tree.tagMapping.mapping.push (tag 12,ix 9),#[]⟩
  nodes := ⟨#[some original,some a,some d,some b,some v,some S05DiagnosticSharedRead.parent,
    some parent,some S05DiagnosticLenRelease.parent,some S05DiagnosticLenRelease.child,some child]⟩
  locations := homogeneous 2 nextLocation
  roots := #[ix 0,ix 1,ix 3] }
private theorem node_cases (index : UniIndex) (node : TreeNode)
    (present : afterRead.nodes.get index = some node) :
    (index = ix 0 ∧ node = original) ∨ (index = ix 1 ∧ node = a) ∨
    (index = ix 2 ∧ node = d) ∨ (index = ix 3 ∧ node = b) ∨
    (index = ix 4 ∧ node = v) ∨ (index = ix 5 ∧ node = S05DiagnosticSharedRead.parent) ∨ (index = ix 6 ∧ node = S05DiagnosticLenRead.parent) ∨ (index = ix 7 ∧ node = S05DiagnosticLenRelease.parent) ∨ (index = ix 8 ∧ node = S05DiagnosticLenRelease.child) := by
  have bound : index.toNat < 9 := by
    by_cases h : index.toNat < 9
    · exact h
    have absent : afterRead.nodes.get index = none := by
      simp only [UniValMap.get,afterRead,tree,S05DiagnosticLenRelease.released,S05DiagnosticLenRelease.tree]
      rw [show #[some original,some a,some d,some b,some v,some S05DiagnosticSharedRead.parent,some S05DiagnosticLenRead.parent,some S05DiagnosticLenRelease.parent,some S05DiagnosticLenRelease.child][index.toNat]? = none from
        Array.getElem?_eq_none (by simpa using h)]
    rw [absent] at present
    contradiction
  have choices : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨
      index.toNat = 3 ∨ index.toNat = 4 ∨ index.toNat = 5 ∨ index.toNat = 6 ∨ index.toNat = 7 ∨ index.toNat = 8 := by omega
  rcases choices with h | h | h | h | h | h | h | h | h
  all_goals
    have indexEq : index = ix index.toNat := by
      cases index
      simp [ix,UniIndex.toNat]
    rw [h] at indexEq
    subst index
    change some _ = some node at present
    injection present with present
    subst node
    simp

private def depth : GeneralBorrowExposure.ParentDepth afterRead.nodes where
  depth := fun index => index.toNat
  bounded := by
    intro index node present
    rcases node_cases index node present with h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩; decide
  parent := by
    intro index node present before parentEq
    rcases node_cases index node present with h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals first | contradiction | skip
    all_goals
      simp only [d,v,S05DiagnosticSharedRead.parent,S05DiagnosticFnEntryRead.w,S05DiagnosticLenRead.parent,S05DiagnosticSharedRead.child,S05DiagnosticLenRelease.parent,S05DiagnosticLenRead.child,S05DiagnosticLenRelease.child,GeneralBorrowFreshChild.child,GeneralBorrowFreshAnchor.sharedNode,Option.some.injEq] at parentEq
      subst before
      exact ⟨_,rfl,by decide⟩


private theorem next_sifa : (sourceUpdateSifa nextTree (ix 6) .Read).1 = nextTree := by
  unfold_source_sifa
  simp only [show (IdempotentForeignAccess.Read == .Write) = false from rfl, Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have s1 : scan () (none,nextTree,some (ix 6),0,true) = .yield (none,nextTree,some (ix 6),0,false) := by
    simp [scan,nextTree,homogeneous,DedupRangeMap.iterAll,←Array.forIn'_toList,
      UniValMap.get,UniValMap.size,UniIndex.toNat,ix,parent,S05DiagnosticLenRead.parent,S05DiagnosticSharedRead.child,GeneralBorrowFreshChild.child,
      nextLocation,afterNormal,location,S05DiagnosticLenRelease.afterNormal,S05DiagnosticLenRelease.location,
      S05DiagnosticLenRead.afterNormal,S05DiagnosticLenRead.location,S05DiagnosticSharedRead.location,
      S05DiagnosticFnEntryRead.afterNormal,S05DiagnosticFnEntryRead.location,UniValMap.insert,UniValMap.extendTo]
    simp [GeneralBorrowFreshChild.inside,IdempotentForeignAccess.ensureNoStrongerThan,
      IdempotentForeignAccess.rank,DedupRangeMap.modifyAll,Id.run,bind,pure]
  have stop : scan () (none,nextTree,some (ix 6),0,false) = .done (none,nextTree,some (ix 6),0,false) := by rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [stop,bind,pure]

private theorem fresh : GeneralBorrowTagMap.Fresh afterRead.tagMapping (tag 12) := by
  intro entry member
  simp [afterRead,tree,S05DiagnosticLenRelease.released,S05DiagnosticLenRelease.tree] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide
/-- Real unprotected mutable TwoPhase constructor after the exact Read. -/
theorem constructor :
    (afterRead.newChild Size.ZERO (.concrete (tag 8)) (tag 12)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).outcome = .ok () := by
  apply GeneralBorrowFreshDefaultChild.append_success afterRead depth (tag 8) (tag 12) (ix 6) S05DiagnosticLenRead.parent
  · decide +kernel
  · rfl
  · exact fresh
  · rfl
  · rfl
  · decide
  · decide
  · exact DedupRangeMap.new_wellFormed (Size.ofBytes 2) _
  · decide
/-- The exact ten-node result installed by the mutable Ref at MIR (6,7). -/
theorem constructor_tree :
    (afterRead.newChild Size.ZERO (.concrete (tag 8)) (tag 12)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree = nextTree := by
  change (afterRead.newChild (Size.ofBytes 0) (.concrete (tag 8)) (tag 12)
    (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree = nextTree
  rw [GeneralBorrowFreshDefaultChild.append_tree afterRead (tag 8) (tag 12) (ix 6)
    S05DiagnosticLenRead.parent (by decide +kernel) rfl fresh rfl rfl (by decide) 0 2 (by decide)
    (DedupRangeMap.new_wellFormed (Size.ofBytes 2) _) (by decide)]
  have modify := GeneralBorrowHomogeneousFullModify.state 2 (by decide) afterNormal
    (fun old => GeneralBorrowFreshMaterialization.materialized old (ix 9) GeneralBorrowFreshDefaultChild.inside)
  change (sourceUpdateSifa {nextTree with locations :=
    ((homogeneous 2 afterNormal).modifyRange Size.ZERO (Size.ofBytes 2)
      (fun _ old => GeneralBorrowFreshMaterialization.materialized old (ix 9) GeneralBorrowFreshDefaultChild.inside)).state} (ix 6) .Read).1 = nextTree
  rw [modify]
  exact next_sifa
end DuplicatePrefix.S05DiagnosticDefaultRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticDefaultRead." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic default read dependency {dependency}"
