import duplicate_prefix.S05DiagnosticSharedRead
import duplicate_prefix.GeneralBorrowFreshSharedChild
import duplicate_prefix.GeneralBorrowFreshResult
import duplicate_prefix.GeneralBorrowHomogeneousFullModify
namespace DuplicatePrefix.S05DiagnosticLenRead
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState GeneralBorrowNodeUpdate RangeMapNonempty
open S05DiagnosticFnEntryRead (ix tag original a d b v)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def parent : TreeNode := {S05DiagnosticSharedRead.child with children := #[ix 7]}
def child : TreeNode := GeneralBorrowFreshAnchor.sharedNode (tag 10) (ix 6)
def location : LocationTree := {S05DiagnosticSharedRead.location with
  perms := S05DiagnosticSharedRead.location.perms.insert (ix 7) GeneralBorrowFreshAnchor.sharedState}
def tree : BorrowTree := {
  tagMapping := ⟨#[(tag 1,ix 0),(tag 2,ix 1),(tag 3,ix 2),(tag 4,ix 3),(tag 5,ix 4),(tag 6,ix 5),(tag 8,ix 6),(tag 10,ix 7)],#[]⟩
  nodes := ⟨#[some original,some a,some d,some b,some v,some S05DiagnosticSharedRead.parent,some parent,some child]⟩
  locations := homogeneous 2 location
  roots := #[ix 0,ix 1,ix 3] }

private theorem sifa : (sourceUpdateSifa tree (ix 6) .Read).1 = tree := by
  unfold_source_sifa
  simp only [show (IdempotentForeignAccess.Read == .Write) = false from rfl, Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have s1 : scan () (none,tree,some (ix 6),0,true) = .yield (none,tree,some (ix 6),0,false) := by
    simp [scan,tree,homogeneous,DedupRangeMap.iterAll,←Array.forIn'_toList,
      UniValMap.get,UniValMap.size,UniIndex.toNat,ix,parent,S05DiagnosticSharedRead.child,GeneralBorrowFreshChild.child,
      location,S05DiagnosticSharedRead.location,S05DiagnosticFnEntryRead.afterNormal,S05DiagnosticFnEntryRead.location,UniValMap.insert,UniValMap.extendTo]
    simp [GeneralBorrowFreshChild.inside,IdempotentForeignAccess.ensureNoStrongerThan,IdempotentForeignAccess.rank,DedupRangeMap.modifyAll,Id.run,bind,pure]
  have stop : scan () (none,tree,some (ix 6),0,false) = .done (none,tree,some (ix 6),0,false) := by rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [stop,bind,pure]

theorem shared_tree :
    (S05DiagnosticSharedRead.tree.newChild Size.ZERO (.concrete (tag 8)) (tag 10)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen false).tree = tree := by
  have fresh : GeneralBorrowTagMap.Fresh S05DiagnosticSharedRead.tree.tagMapping (tag 10) := by
    intro entry member
    simp [S05DiagnosticSharedRead.tree] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have well : S05DiagnosticSharedRead.tree.locations.WellFormed := by
    exact DedupRangeMap.new_wellFormed (Size.ofBytes 2) _
  change (S05DiagnosticSharedRead.tree.newChild (Size.ofBytes 0) (.concrete (tag 8)) (tag 10)
    (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen false).tree = tree
  rw [GeneralBorrowFreshSharedChild.append_tree S05DiagnosticSharedRead.tree (tag 8) (tag 10) (ix 6)
    S05DiagnosticSharedRead.child (by decide +kernel) rfl fresh rfl rfl (by decide) false 0 2 (by decide) well (by decide)]
  have modify := GeneralBorrowHomogeneousFullModify.state 2 (by decide) S05DiagnosticSharedRead.location
    (fun old => GeneralBorrowFreshMaterialization.materialized old (ix 7) GeneralBorrowFreshAnchor.sharedState)
  change (sourceUpdateSifa { tree with locations :=
    ((homogeneous 2 S05DiagnosticSharedRead.location).modifyRange Size.ZERO (Size.ofBytes 2)
      (fun _ old => GeneralBorrowFreshMaterialization.materialized old (ix 7) GeneralBorrowFreshAnchor.sharedState)).state } (ix 6) .Read).1 = tree
  rw [modify]
  exact sifa

def protections : ProtectedTags := S05DiagnosticSharedRead.protections.insert (tag 11) .StrongProtector

/-- The actual shared FnEntry policy materializes Frozen/accessed/Read bytes. -/
theorem initial : RetagPolicy.initialLocationState (NestedConstruction.sharedPolicy true) true =
    .ok GeneralBorrowFreshAnchor.sharedState := NestedConstruction.shared_initial true

def afterNormal : LocationTree := {location with perms := location.perms.insert (ix 7) ⟨.Frozen,true,.None⟩}
def afterRead : BorrowTree := {tree with locations := homogeneous 2 afterNormal}

theorem normal :
    (tree.performNormalAccessAt location (ix 7) .Read protections .VisitChildrenOfAccessed).location = afterNormal ∧
    (tree.performNormalAccessAt location (ix 7) .Read protections .VisitChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location (ix 7) .Read protections .VisitChildrenOfAccessed).outcome = .ok () := by
  decide +kernel
theorem primary : tree.performWildcardAccessAt afterNormal (ix 0) (some (tag 4)) .Read protections false =
    ⟨afterNormal,.Completed⟩ := by
  exact GeneralBorrowWildcardLeaf.access tree afterNormal (ix 0) original (tag 4) .Read protections
    ⟨rfl,rfl,rfl,by decide +kernel,rfl,by decide +kernel⟩

/-- The A/D/V visitor is finite and uses only its actual Read callbacks. -/
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
    source_access_status (source_tree_access_at tree location (some (ix 7)) .Read protections .VisitChildrenOfAccessed ⟨0,2⟩) = none ∧
    source_access_location (source_tree_access_at tree location (some (ix 7)) .Read protections .VisitChildrenOfAccessed ⟨0,2⟩) = afterNormal := by
  simp_tree_helpers
  simp only [show (ChildrenVisitMode.VisitChildrenOfAccessed == ChildrenVisitMode.SkipChildrenOfAccessed) = false from rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [normal.1,normal.2.1,normal.2.2,beq_self_eq_true,Bool.false_eq_true,↓reduceIte]
  have root : (tree.performNormalAccessAt location (ix 7) .Read protections .VisitChildrenOfAccessed).access.root = 3 := by decide +kernel
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
    let result := tree.performBorrowAccessRange (.concrete (tag 10)) Size.ZERO (Size.ofBytes 2)
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = afterRead := by
  have result := GeneralBorrowHomogeneousSourceAccess.full tree location 2 (by decide) rfl
    (.concrete (tag 10)) (some (ix 7)) .Read protections .VisitChildrenOfAccessed
    ⟨by decide +kernel,by decide⟩ callback.1
  simpa only [callback.2,afterRead] using result

private theorem node_cases (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (index = ix 0 ∧ node = original) ∨ (index = ix 1 ∧ node = a) ∨
    (index = ix 2 ∧ node = d) ∨ (index = ix 3 ∧ node = b) ∨
    (index = ix 4 ∧ node = v) ∨ (index = ix 5 ∧ node = S05DiagnosticSharedRead.parent) ∨ (index = ix 6 ∧ node = parent) ∨ (index = ix 7 ∧ node = child) := by
  have bound : index.toNat < 8 := by
    by_cases h : index.toNat < 8
    · exact h
    have absent : tree.nodes.get index = none := by
      simp only [UniValMap.get,tree]
      rw [show #[some original,some a,some d,some b,some v,some S05DiagnosticSharedRead.parent,some parent,some child][index.toNat]? = none from
        Array.getElem?_eq_none (by simpa using h)]
    rw [absent] at present
    contradiction
  have choices : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨
      index.toNat = 3 ∨ index.toNat = 4 ∨ index.toNat = 5 ∨ index.toNat = 6 ∨ index.toNat = 7 := by omega
  rcases choices with h | h | h | h | h | h | h | h
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
    rcases node_cases index node present with h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩; decide
  parent := by
    intro index node present before parentEq
    rcases node_cases index node present with h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals first | contradiction | skip
    all_goals
      simp only [d,v,S05DiagnosticSharedRead.parent,S05DiagnosticFnEntryRead.w,parent,S05DiagnosticSharedRead.child,child,GeneralBorrowFreshChild.child,GeneralBorrowFreshAnchor.sharedNode,Option.some.injEq] at parentEq
      subst before
      exact ⟨_,rfl,by decide⟩

theorem constructor :
    (afterRead.newChild Size.ZERO (.concrete (tag 10)) (tag 11)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState)
      .Frozen true).outcome = .ok () := by
  apply GeneralBorrowFreshSharedChild.append_success afterRead depth (tag 10) (tag 11) (ix 7) child
  · decide +kernel
  · rfl
  · intro entry member
    simp [afterRead,tree] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · rfl
  · rfl
  · decide
  · decide
  · change (DedupRangeMap.new (Size.ofBytes 2) afterNormal).WellFormed
    exact DedupRangeMap.new_wellFormed _ _
  · decide

def nextParent : TreeNode := {child with children := #[ix 8]}
def nextChild : TreeNode := GeneralBorrowFreshAnchor.sharedNode (tag 11) (ix 7)
def nextLocation : LocationTree := {afterNormal with
  perms := afterNormal.perms.insert (ix 8) GeneralBorrowFreshAnchor.sharedState}
def nextTree : BorrowTree := {
  tagMapping := ⟨tree.tagMapping.mapping.push (tag 11,ix 8),#[]⟩
  nodes := ⟨#[some original,some a,some d,some b,some v,some S05DiagnosticSharedRead.parent,some parent,some nextParent,some nextChild]⟩
  locations := homogeneous 2 nextLocation
  roots := #[ix 0,ix 1,ix 3] }

private theorem next_sifa : (sourceUpdateSifa nextTree (ix 7) .Read).1 = nextTree := by
  unfold_source_sifa
  simp only [show (IdempotentForeignAccess.Read == .Write) = false from rfl, Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have s1 : scan () (none,nextTree,some (ix 7),0,true) = .yield (none,nextTree,some (ix 7),0,false) := by
    simp [scan,nextTree,homogeneous,DedupRangeMap.iterAll,←Array.forIn'_toList,
      UniValMap.get,UniValMap.size,UniIndex.toNat,ix,nextParent,child,GeneralBorrowFreshAnchor.sharedNode,
      nextLocation,afterNormal,location,S05DiagnosticSharedRead.location,S05DiagnosticFnEntryRead.afterNormal,
      S05DiagnosticFnEntryRead.location,UniValMap.insert,UniValMap.extendTo]
    simp [GeneralBorrowFreshAnchor.sharedState,IdempotentForeignAccess.ensureNoStrongerThan,
      IdempotentForeignAccess.rank,DedupRangeMap.modifyAll,Id.run,bind,pure]
  have stop : scan () (none,nextTree,some (ix 7),0,false) = .done (none,nextTree,some (ix 7),0,false) := by rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [stop,bind,pure]

/-- Exact nine-node state returned by the real protected helper-entry constructor. -/
theorem constructor_tree :
    (afterRead.newChild Size.ZERO (.concrete (tag 10)) (tag 11)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree = nextTree := by
  have fresh : GeneralBorrowTagMap.Fresh afterRead.tagMapping (tag 11) := by
    intro entry member
    simp [afterRead,tree] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have well : afterRead.locations.WellFormed := by
    exact DedupRangeMap.new_wellFormed (Size.ofBytes 2) _
  change (afterRead.newChild (Size.ofBytes 0) (.concrete (tag 10)) (tag 11)
    (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree = nextTree
  rw [GeneralBorrowFreshSharedChild.append_tree afterRead (tag 10) (tag 11) (ix 7)
    child (by decide +kernel) rfl fresh rfl rfl (by decide) true 0 2 (by decide) well (by decide)]
  have modify := GeneralBorrowHomogeneousFullModify.state 2 (by decide) afterNormal
    (fun old => GeneralBorrowFreshMaterialization.materialized old (ix 8) GeneralBorrowFreshAnchor.sharedState)
  change (sourceUpdateSifa { nextTree with locations :=
    ((homogeneous 2 afterNormal).modifyRange Size.ZERO (Size.ofBytes 2)
      (fun _ old => GeneralBorrowFreshMaterialization.materialized old (ix 8) GeneralBorrowFreshAnchor.sharedState)).state } (ix 7) .Read).1 = nextTree
  rw [modify]
  exact next_sifa

end DuplicatePrefix.S05DiagnosticLenRead

#print axioms DuplicatePrefix.S05DiagnosticLenRead.shared_tree
#print axioms DuplicatePrefix.S05DiagnosticLenRead.read
#print axioms DuplicatePrefix.S05DiagnosticLenRead.constructor
#print axioms DuplicatePrefix.S05DiagnosticLenRead.constructor_tree
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticLenRead." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic len Read dependency {dependency}"
