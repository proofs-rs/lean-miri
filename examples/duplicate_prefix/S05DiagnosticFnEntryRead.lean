import duplicate_prefix.GeneralBorrowHomogeneousSourceAccess
import duplicate_prefix.GeneralBorrowFreshChild
import duplicate_prefix.GeneralBorrowWildcardSubtreeStack

namespace DuplicatePrefix.S05DiagnosticFnEntryRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState GeneralBorrowNodeUpdate RangeMapNonempty
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def tag (n : UInt64) (h : n ≠ 0 := by decide) : BorTag := ⟨n,h⟩
def original : TreeNode := ⟨tag 1,none,#[],.Disabled,.None,true,none⟩
def a : TreeNode := ⟨tag 2,none,#[ix 2],.Cell,.Write,false,none⟩
def d : TreeNode := ⟨tag 3,some (ix 1),#[ix 4],.ReservedFrz false,.Read,false,none⟩
def b : TreeNode := ⟨tag 4,none,#[ix 5],.Cell,.None,false,none⟩
def v : TreeNode := ⟨tag 5,some (ix 2),#[],.ReservedFrz false,.Read,true,none⟩
def w : TreeNode := ⟨tag 6,some (ix 3),#[],.ReservedFrz false,.Read,false,none⟩
def cache : ExposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩,some ⟨0,0⟩,some ⟨1,1⟩,some ⟨0,0⟩]⟩⟩
def location : LocationTree := {
  perms := ⟨#[some ⟨.Unique,true,.None⟩,some ⟨.Cell,false,.Write⟩,
    some ⟨.Disabled,true,.Read⟩,some ⟨.Cell,true,.None⟩,none,some ⟨.ReservedFrz false,true,.Read⟩]⟩
  exposedCache := cache }
def tree : BorrowTree := {
  tagMapping := ⟨#[(tag 1,ix 0),(tag 2,ix 1),(tag 3,ix 2),(tag 4,ix 3),(tag 5,ix 4),(tag 6,ix 5)],#[]⟩
  nodes := ⟨#[some original,some a,some d,some b,some v,some w]⟩
  locations := homogeneous 2 location
  roots := #[ix 0,ix 1,ix 3] }
def protections : ProtectedTags := ({} : ProtectedTags).insert (tag 8) .StrongProtector
def afterNormal : LocationTree := {location with perms := location.perms.insert (ix 5) ⟨.ReservedFrz false,true,.None⟩}

/-- Exact lower normal Read, without a counterfactual Write authorization. -/
theorem normal :
    (tree.performNormalAccessAt location (ix 5) .Read protections .VisitChildrenOfAccessed).location = afterNormal ∧
    (tree.performNormalAccessAt location (ix 5) .Read protections .VisitChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location (ix 5) .Read protections .VisitChildrenOfAccessed).outcome = .ok () := by
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
    source_access_status (source_tree_access_at tree location (some (ix 5)) .Read protections .VisitChildrenOfAccessed ⟨0,2⟩) = none ∧
    source_access_location (source_tree_access_at tree location (some (ix 5)) .Read protections .VisitChildrenOfAccessed ⟨0,2⟩) = afterNormal := by
  simp_tree_helpers
  simp only [show (ChildrenVisitMode.VisitChildrenOfAccessed == ChildrenVisitMode.SkipChildrenOfAccessed) = false from rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [normal.1,normal.2.1,normal.2.2,beq_self_eq_true,Bool.false_eq_true,↓reduceIte]
  have root : (tree.performNormalAccessAt location (ix 5) .Read protections .VisitChildrenOfAccessed).access.root = 3 := by decide +kernel
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

def afterRead : BorrowTree := {tree with locations := homogeneous 2 afterNormal}

theorem read :
    let result := tree.performBorrowAccessRange (.concrete (tag 6)) Size.ZERO (Size.ofBytes 2)
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = afterRead := by
  have result := GeneralBorrowHomogeneousSourceAccess.full tree location 2 (by decide) rfl
    (.concrete (tag 6)) (some (ix 5)) .Read protections .VisitChildrenOfAccessed
    ⟨by decide +kernel,by decide⟩ callback.1
  simpa only [callback.2,afterRead] using result

private theorem node_cases (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (index = ix 0 ∧ node = original) ∨ (index = ix 1 ∧ node = a) ∨
    (index = ix 2 ∧ node = d) ∨ (index = ix 3 ∧ node = b) ∨
    (index = ix 4 ∧ node = v) ∨ (index = ix 5 ∧ node = w) := by
  have bound : index.toNat < 6 := by
    by_cases h : index.toNat < 6
    · exact h
    have absent : tree.nodes.get index = none := by
      simp only [UniValMap.get,tree]
      rw [show #[some original,some a,some d,some b,some v,some w][index.toNat]? = none from
        Array.getElem?_eq_none (by simpa using h)]
    rw [absent] at present
    contradiction
  have choices : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨
      index.toNat = 3 ∨ index.toNat = 4 ∨ index.toNat = 5 := by omega
  rcases choices with h | h | h | h | h | h
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
    rcases node_cases index node present with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩; decide
  parent := by
    intro index node present before parent
    rcases node_cases index node present with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals first | contradiction | skip
    all_goals
      simp only [d,v,w,Option.some.injEq] at parent
      subst before
      exact ⟨_,rfl,by decide⟩

theorem constructor :
    (afterRead.newChild Size.ZERO (.concrete (tag 6)) (tag 8)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside)
      (.ReservedFrz false) true).outcome = .ok () := by
  apply GeneralBorrowFreshChild.mutable_success afterRead depth (tag 6) (tag 8) (ix 5) w
  · decide +kernel
  · rfl
  · intro entry member
    simp [afterRead,tree] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · rfl
  · rfl
  · decide
  · decide
  · change (DedupRangeMap.new (Size.ofBytes 2) afterNormal).WellFormed
    exact DedupRangeMap.new_wellFormed _ _
  · decide

end DuplicatePrefix.S05DiagnosticFnEntryRead


#print axioms DuplicatePrefix.S05DiagnosticFnEntryRead.read
#print axioms DuplicatePrefix.S05DiagnosticFnEntryRead.constructor
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticFnEntryRead." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic FnEntry Read dependency {dependency}"
