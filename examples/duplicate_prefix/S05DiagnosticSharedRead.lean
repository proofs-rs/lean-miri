import duplicate_prefix.S05DiagnosticFnEntryArgument
import duplicate_prefix.GeneralBorrowFreshSharedChild
import duplicate_prefix.GeneralBorrowFreshResult
import duplicate_prefix.GeneralBorrowHomogeneousFullModify
namespace DuplicatePrefix.S05DiagnosticSharedRead
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState GeneralBorrowNodeUpdate RangeMapNonempty
open S05DiagnosticFnEntryRead (ix tag original a d b v)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def parent : TreeNode := {S05DiagnosticFnEntryRead.w with children := #[ix 6],defaultInitialSifa := .None}
def child : TreeNode := GeneralBorrowFreshChild.child (tag 8) (ix 5)
def location : LocationTree := {S05DiagnosticFnEntryRead.afterNormal with
  perms := S05DiagnosticFnEntryRead.afterNormal.perms.insert (ix 6) GeneralBorrowFreshChild.inside}
def tree : BorrowTree := {
  tagMapping := ⟨#[(tag 1,ix 0),(tag 2,ix 1),(tag 3,ix 2),(tag 4,ix 3),(tag 5,ix 4),(tag 6,ix 5),(tag 8,ix 6)],#[]⟩
  nodes := ⟨#[some original,some a,some d,some b,some v,some parent,some child]⟩
  locations := homogeneous 2 location
  roots := #[ix 0,ix 1,ix 3] }

private def stage : BorrowTree := {tree with nodes := ⟨#[some original,some a,some d,some b,some v,
  some {S05DiagnosticFnEntryRead.w with children := #[ix 6]},some child]⟩}

private theorem sifa : (sourceUpdateSifa stage (ix 5) .None).1 = tree := by
  unfold_source_sifa
  simp only [show (IdempotentForeignAccess.None == .Write) = false from rfl, Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have s1 : scan () (none,stage,some (ix 5),0,true) = .yield (none,tree,some (ix 3),1,true) := by
    simp [scan,stage,tree,homogeneous,DedupRangeMap.iterAll,←Array.forIn'_toList,
      UniValMap.get,UniValMap.size,UniIndex.toNat,ix,parent,S05DiagnosticFnEntryRead.w,
      location,S05DiagnosticFnEntryRead.afterNormal,S05DiagnosticFnEntryRead.location,UniValMap.insert,UniValMap.extendTo]
    simp [IdempotentForeignAccess.ensureNoStrongerThan,IdempotentForeignAccess.rank,DedupRangeMap.modifyAll,Id.run,bind,pure]
  have s2 : scan () (none,tree,some (ix 3),1,true) = .yield (none,tree,some (ix 3),1,false) := by
    simp [scan,tree,homogeneous,DedupRangeMap.iterAll,←Array.forIn'_toList,
      UniValMap.get,UniValMap.size,UniIndex.toNat,ix,b,
      location,S05DiagnosticFnEntryRead.afterNormal,S05DiagnosticFnEntryRead.location,UniValMap.insert,UniValMap.extendTo]
    simp [IdempotentForeignAccess.ensureNoStrongerThan,IdempotentForeignAccess.rank,DedupRangeMap.modifyAll,Id.run,bind,pure]
  have stop : scan () (none,tree,some (ix 3),1,false) = .done (none,tree,some (ix 3),1,false) := by rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [stop,bind,pure]

theorem entry_tree :
    (S05DiagnosticFnEntryRead.afterRead.newChild Size.ZERO (.concrete (tag 6)) (tag 8)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree = tree := by
  have fresh : GeneralBorrowTagMap.Fresh S05DiagnosticFnEntryRead.afterRead.tagMapping (tag 8) := by
    intro entry member
    simp [S05DiagnosticFnEntryRead.afterRead,S05DiagnosticFnEntryRead.tree] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have well : S05DiagnosticFnEntryRead.afterRead.locations.WellFormed := by
    exact DedupRangeMap.new_wellFormed (Size.ofBytes 2) _
  change (S05DiagnosticFnEntryRead.afterRead.newChild (Size.ofBytes 0) (.concrete (tag 6)) (tag 8)
    (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree = tree
  rw [GeneralBorrowFreshResult.mutable_tree S05DiagnosticFnEntryRead.afterRead (tag 6) (tag 8) (ix 5)
    S05DiagnosticFnEntryRead.w (by decide +kernel) rfl fresh rfl rfl (by decide) 0 2 (by decide) well (by decide)]
  have modify := GeneralBorrowHomogeneousFullModify.state 2 (by decide) S05DiagnosticFnEntryRead.afterNormal
    (fun old => GeneralBorrowFreshMaterialization.materialized old (ix 6) GeneralBorrowFreshChild.inside)
  change (sourceUpdateSifa { stage with locations :=
    ((homogeneous 2 S05DiagnosticFnEntryRead.afterNormal).modifyRange Size.ZERO (Size.ofBytes 2)
      (fun _ old => GeneralBorrowFreshMaterialization.materialized old (ix 6) GeneralBorrowFreshChild.inside)).state } (ix 5) .None).1 = tree
  rw [modify]
  exact sifa

/-- The normalized source tree is the exact selected argument adapter result. -/
theorem finalTree_eq (tracker : MachineHooks.BorrowState)
    (nextEq : tracker.global.nextPointerTag = tag 8)
    (protectedEq : tracker.global.protectedTags = ({} : ProtectedTags)) :
    S05DiagnosticFnEntryArgument.finalTree S05DiagnosticFnEntryRead.tree tracker (tag 6) 0 2 = tree := by
  unfold S05DiagnosticFnEntryArgument.finalTree
  simp only [TypedBorrowSteps.registeredGlobal,nextEq,protectedEq]
  change ((S05DiagnosticFnEntryRead.tree.performBorrowAccessRange (.concrete (tag 6)) Size.ZERO
    (Size.ofBytes 2) .Read S05DiagnosticFnEntryRead.protections .VisitChildrenOfAccessed).tree.newChild
      Size.ZERO (.concrete (tag 6)) (tag 8) (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside)
      (.ReservedFrz false) true).tree = tree
  rw [S05DiagnosticFnEntryRead.read.2]
  exact entry_tree

def protections : ProtectedTags := (S05DiagnosticFnEntryRead.protections).insert (tag 9) .StrongProtector

theorem normal :
    (tree.performNormalAccessAt location (ix 6) .Read protections .VisitChildrenOfAccessed).location = location ∧
    (tree.performNormalAccessAt location (ix 6) .Read protections .VisitChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location (ix 6) .Read protections .VisitChildrenOfAccessed).outcome = .ok () := by
  decide +kernel
theorem primary : tree.performWildcardAccessAt location (ix 0) (some (tag 4)) .Read protections false =
    ⟨location,.Completed⟩ := by
  exact GeneralBorrowWildcardLeaf.access tree location (ix 0) original (tag 4) .Read protections
    ⟨rfl,rfl,rfl,by decide +kernel,rfl,by decide +kernel⟩

/-- The A/D/V visitor is finite and uses only its actual Read callbacks. -/
theorem other : tree.performWildcardAccessAt location (ix 1) (some (tag 4)) .Read protections true =
    ⟨location,.Completed⟩ := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have s1 : scan () (location,false,.Completed,#[(ix 1,false)],0) =
      .yield (location,false,.Completed,#[(ix 1,true),(ix 2,false)],1) := by rfl
  have s2 : scan () (location,false,.Completed,#[(ix 1,true),(ix 2,false)],1) =
      .yield (location,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,false)],2) := by rfl
  have s3 : scan () (location,false,.Completed,#[(ix 1,true),(ix 2,true),(ix 4,false)],2) =
      .yield (location,false,.Completed,#[(ix 1,true),(ix 2,true)],3) := by rfl
  have s4 : scan () (location,false,.Completed,#[(ix 1,true),(ix 2,true)],3) =
      .yield (location,false,.Completed,#[(ix 1,true)],4) := by rfl
  have s5 : scan () (location,false,.Completed,#[(ix 1,true)],4) =
      .yield (location,false,.Completed,#[],5) := by rfl
  have stop : scan () (location,false,.Completed,#[],5) =
      .done (location,false,.Completed,#[],5) := by rfl
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
    source_access_location (source_tree_access_at tree location (some (ix 6)) .Read protections .VisitChildrenOfAccessed ⟨0,2⟩) = location := by
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


theorem read :
    let result := tree.performBorrowAccessRange (.concrete (tag 8)) Size.ZERO (Size.ofBytes 2)
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = tree := by
  have result := GeneralBorrowHomogeneousSourceAccess.full tree location 2 (by decide) rfl
    (.concrete (tag 8)) (some (ix 6)) .Read protections .VisitChildrenOfAccessed
    ⟨by decide +kernel,by decide⟩ callback.1
  simpa only [callback.2,show ({tree with locations := homogeneous 2 location} : BorrowTree) = tree from rfl] using result

private theorem node_cases (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (index = ix 0 ∧ node = original) ∨ (index = ix 1 ∧ node = a) ∨
    (index = ix 2 ∧ node = d) ∨ (index = ix 3 ∧ node = b) ∨
    (index = ix 4 ∧ node = v) ∨ (index = ix 5 ∧ node = parent) ∨ (index = ix 6 ∧ node = child) := by
  have bound : index.toNat < 7 := by
    by_cases h : index.toNat < 7
    · exact h
    have absent : tree.nodes.get index = none := by
      simp only [UniValMap.get,tree]
      rw [show #[some original,some a,some d,some b,some v,some parent,some child][index.toNat]? = none from
        Array.getElem?_eq_none (by simpa using h)]
    rw [absent] at present
    contradiction
  have choices : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨
      index.toNat = 3 ∨ index.toNat = 4 ∨ index.toNat = 5 ∨ index.toNat = 6 := by omega
  rcases choices with h | h | h | h | h | h | h
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

private def depth : GeneralBorrowExposure.ParentDepth tree.nodes where
  depth := fun index => index.toNat
  bounded := by
    intro index node present
    rcases node_cases index node present with h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩; decide
  parent := by
    intro index node present before parentEq
    rcases node_cases index node present with h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals first | contradiction | skip
    all_goals
      simp only [d,v,parent,S05DiagnosticFnEntryRead.w,child,GeneralBorrowFreshChild.child,Option.some.injEq] at parentEq
      subst before
      exact ⟨_,rfl,by decide⟩

theorem constructor :
    (tree.newChild Size.ZERO (.concrete (tag 8)) (tag 10)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState)
      .Frozen false).outcome = .ok () := by
  apply GeneralBorrowFreshSharedChild.append_success tree depth (tag 8) (tag 10) (ix 6) child
  · decide +kernel
  · rfl
  · intro entry member
    simp [tree] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · rfl
  · rfl
  · decide
  · decide
  · change (DedupRangeMap.new (Size.ofBytes 2) location).WellFormed
    exact DedupRangeMap.new_wellFormed _ _
  · decide

end DuplicatePrefix.S05DiagnosticSharedRead

#print axioms DuplicatePrefix.S05DiagnosticSharedRead.entry_tree
#print axioms DuplicatePrefix.S05DiagnosticSharedRead.finalTree_eq
#print axioms DuplicatePrefix.S05DiagnosticSharedRead.read
#print axioms DuplicatePrefix.S05DiagnosticSharedRead.constructor
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticSharedRead." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic shared Read dependency {dependency}"
