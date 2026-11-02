import duplicate_prefix.S05DiagnosticAsMutRead
import duplicate_prefix.GeneralBorrowHomogeneousHiddenUniqueRelease
namespace DuplicatePrefix.S05DiagnosticAsMutRelease
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState GeneralBorrowNodeUpdate RangeMapNonempty
open S05DiagnosticFnEntryRead (ix tag original a d b v)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def tree := S05DiagnosticAsMutRead.nextTree
def location := S05DiagnosticAsMutRead.nextLocation
def protections := S05DiagnosticAsMutRead.protections
def afterNormal : LocationTree := location
def released : BorrowTree := {tree with locations := homogeneous 2 afterNormal}

/-- ReservedFrz(false)'s actual protector-end associated access is Read. -/
theorem associated : Permission.associatedAccess (.ReservedFrz false) = some .Read := rfl
/-- The current local SIFA is already None; the exact protected Read completes. -/
theorem normal :
    (tree.performNormalAccessAt location (ix 10) .Read protections .SkipChildrenOfAccessed).location = afterNormal ∧
    (tree.performNormalAccessAt location (ix 10) .Read protections .SkipChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location (ix 10) .Read protections .SkipChildrenOfAccessed).outcome = .ok () := by
  decide +kernel
theorem min : source_min_exposed tree (ix 10) = none := by
  unfold_min_exposed
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step : scan () (none,#[ix 10],0,none) = .yield (none,#[],1,none) := by rfl
  have stop : scan () (none,#[],1,none) = .done (none,#[],1,none) := by rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [stop,bind,pure]
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
    source_access_status (source_tree_access_at tree location (some (ix 10)) .Read protections .SkipChildrenOfAccessed ⟨0,2⟩) = none ∧
    source_access_location (source_tree_access_at tree location (some (ix 10)) .Read protections .SkipChildrenOfAccessed ⟨0,2⟩) = afterNormal := by
  simp_tree_helpers
  simp only [beq_self_eq_true,min,Option.bind_some,Option.bind_none, Bool.false_eq_true, ↓reduceIte]
  simp only [normal.1,normal.2.1,normal.2.2,beq_self_eq_true,Bool.false_eq_true,↓reduceIte]
  have root : (tree.performNormalAccessAt location (ix 10) .Read protections .SkipChildrenOfAccessed).access.root = 3 := by decide +kernel
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
  simp only [show (tree.nodes.get (⟨UInt32.ofNat 3⟩ : UniIndex)).map TreeNode.tag = some (tag 4) from rfl,
    show (tree.nodes.get (ix 0)).map TreeNode.tag = some (tag 1) from rfl,
    show (tree.nodes.get (ix 1)).map TreeNode.tag = some (tag 2) from rfl,
    show (tree.nodes.get (ix 3)).map TreeNode.tag = some (tag 4) from rfl,
    primary,other,bne_self_eq_false,Option.isNone_none,Bool.not_false,Bool.true_and,Bool.false_eq_true,↓reduceIte]
  exact ⟨trivial,trivial⟩

/-- The normalized release input is the actual mutable FnEntry constructor output. -/
theorem constructor_tree :
    (S05DiagnosticAsMutRead.afterRead.newChild Size.ZERO (.concrete (tag 12)) (tag 13)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree = tree :=
  S05DiagnosticAsMutRead.constructor_tree

/-- The actual mutable helper protector release performs its associated Read. -/
theorem release : tree.releaseProtector (tag 13) protections = ⟨released,.Released⟩ := by
  unfold BorrowTree.releaseProtector
  simp only [show tree.indexOfTag (tag 13) = some (ix 10) from by decide +kernel,Id.run,bind,pure,
    show tree.locations = homogeneous 2 location from rfl,show (homogeneous 2 location).entries.size=1 from rfl]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    show List.range' 0 1=[0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [show tree.locations = homogeneous 2 location from rfl]
  rw [index_exact (homogeneous 2 location) 0 (by change 0<1;decide)]
  simp only [show (homogeneous 2 location).entries[0]'(by change 0<1;decide) = ⟨⟨0,2⟩,location⟩ from rfl,
    show location.perms.get (ix 10) = some GeneralBorrowFreshChild.inside from by decide +kernel,
    GeneralBorrowFreshChild.inside,Permission.associatedAccess,↓reduceIte,bind,pure]
  simp only [setAtPos_success (homogeneous 2 location) 0 (by change 0<1;decide),callback.1,bind,pure]
  rw [setAtPos_exact (homogeneous 2 location) 0 (by change 0<1;decide)]
  rw [callback.2]
  unfold BorrowTree.updateExposureForProtectorRelease
  rfl
/-- Exact release equality in the constructor expression consumed by physical Return. -/
theorem actual_release :
    ((S05DiagnosticAsMutRead.afterRead.newChild Size.ZERO (.concrete (tag 12)) (tag 13)
      (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree).releaseProtector
        (tag 13) protections = ⟨released,.Released⟩ := by
  rw [constructor_tree]
  exact release
end DuplicatePrefix.S05DiagnosticAsMutRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticAsMutRelease." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic as_mut_ptr release dependency {dependency}"
