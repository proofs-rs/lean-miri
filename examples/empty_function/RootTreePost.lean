import empty_function.RootTagPost
namespace EmptyFunction.RootTreePost
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem singleton_get {Value : Type} (value : Value) (index : UniIndex) :
    (⟨#[some value]⟩ : UniValMap Value).get index = if index.toNat = 0 then some value else none := by
  by_cases zero : index.toNat = 0
  · simp [UniValMap.get,zero]
  · have outside : ¬ index.toNat < 1 := by omega
    simp [UniValMap.get,zero]

private theorem index_zero (index : UniIndex) (zero : index.toNat = 0) : index = ⟨0⟩ := by
  cases index with
  | mk value =>
    change value.toNat = 0 at zero
    have equal : value = 0 := UInt32.toNat_inj.mp zero
    subst value
    rfl

/-- The actual constructor creates a formed singleton tree below the current
global tag counter. No ordering against a separately reserved child tag is
required or asserted. -/
def fresh (root next : BorTag) (size : Size)
    (below : root.value.toNat < next.value.toNat) :
    TreeRuntimeInput.TreeFormed (BorrowTree.new root size) next := by
  let node : TreeNode := {
    tag := root
    parent := none
    defaultInitialPermission := Permission.newDisabled
    defaultInitialSifa := .None }
  have nodes : (BorrowTree.new root size).nodes = (⟨#[some node]⟩ : UniValMap TreeNode) := by rfl
  have mapping : (BorrowTree.new root size).tagMapping = (⟨#[(root,⟨0⟩)],#[]⟩ : UniKeyMap BorTag) := by rfl
  have locations : (BorrowTree.new root size).locations = DedupRangeMap.new size
      ({perms := ⟨#[some ⟨Permission.newUnique,true,.None⟩]⟩,exposedCache := {}} : LocationTree) := by rfl
  constructor
  · refine ⟨fun _ => 0,?_⟩
    intro index found present parent parentEq
    rw [nodes,singleton_get] at present
    split at present
    · cases present
      cases parentEq
    · cases present
  · intro index member
    simp only [mapping,Array.not_mem_empty] at member
  · simp [mapping]
  · simp [mapping,nodes,UniValMap.size]
  · intro index vacant position valid
    rw [nodes,singleton_get] at vacant
    have nonzero : index.toNat ≠ 0 := by
      intro zero
      simp only [zero,ite_true] at vacant
      cases vacant
    cases empty : size.bytes == 0
    · have atZero : position = 0 := by
        simp only [locations,DedupRangeMap.new,empty,Bool.false_eq_true,↓reduceIte,Array.size_singleton] at valid
        omega
      subst position
      simp only [locations,DedupRangeMap.new,empty,Bool.false_eq_true,↓reduceIte]
      change (⟨#[some ⟨Permission.newUnique,true,.None⟩]⟩ : UniValMap LocationState).get index = none
      simp only [singleton_get,nonzero,↓reduceIte]
    · simp only [locations,DedupRangeMap.new,empty,↓reduceIte,Array.size_empty] at valid
      omega
  · intro row member
    have equal : row = (root,⟨0⟩) := by simpa only [mapping,Array.mem_singleton] using member
    subst row
    refine ⟨node,?_,rfl⟩
    rw [nodes,singleton_get]
    rfl
  · intro index found present
    rw [nodes,singleton_get] at present
    split at present
    · rename_i zero
      cases present
      have equal := index_zero index zero
      subst index
      simp [mapping,UniKeyMap.get,node]
    · cases present
  · simp [mapping]
  · intro row member
    have equal : row = (root,⟨0⟩) := by simpa only [mapping,Array.mem_singleton] using member
    subst row
    exact below

/-- A root cached in a formed global registry is below its actual current
counter, including the root newly installed by initExtra. -/
def cached (global : GlobalState) (formed : TreeRuntimeInput.GlobalFormed global)
    (id : AllocId) (root : BorTag) (size : Size) (present : global.rootTag? id = some root) :
    TreeRuntimeInput.TreeFormed (BorrowTree.new root size) global.nextPointerTag := by
  apply fresh root global.nextPointerTag size
  unfold GlobalState.rootTag? at present
  cases found : global.rootPointerTags.find? (fun row => row.1 == id) with
  | none => simp only [found,Option.map_none] at present; cases present
  | some row =>
    have same : row.2 = root := by simpa only [found,Option.map_some,Option.some.injEq] using present
    rw [←same]
    exact formed.rootsBelow row (Array.mem_of_find?_eq_some found)

/-- The actual root operation supplies both the singleton constructor shape
and the counter bound needed when the owned allocation becomes live. -/
def root_operation (before after : GlobalState) (id : AllocId) (root : BorTag) (size : Size)
    (formed : TreeRuntimeInput.GlobalFormed before)
    (actual : before.rootPointerTag id = .ok (after,root)) :
    TreeRuntimeInput.TreeFormed (BorrowTree.new root size) after.nextPointerTag :=
  cached after (RootTagPost.formed before id after root formed actual) id root size
    (RootTagPost.root before id after root actual).1

end EmptyFunction.RootTreePost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RootTreePost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent new tree axiom {dependency} in {name}"
