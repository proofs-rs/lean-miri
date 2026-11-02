import Miri.TreeBorrows.TreeState
import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.GeneralBorrowNodeUpdate
import Init.Internal.Order.While
import Lean

/-! One finite, actual core trace with byte-dependent wildcard origins. Each
operation consumes the preceding result. This is no ordinary-input or Rust
reachability claim, and says nothing about whole-function failure. -/
namespace DuplicatePrefix.CurrentCallSplitOriginTrace
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def tag (n : UInt64) (nonzero : n ≠ 0 := by decide) : BorTag := ⟨n,nonzero⟩
def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def mutable : LocationState := ⟨.ReservedFrz false,true,.Read⟩
def seed : BorrowTree := BorrowTree.new (tag 1) (Size.ofBytes 2)
def readA := seed.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 1) .Read {} .VisitChildrenOfAccessed
def a := readA.tree.newChild Size.ZERO (.concrete (tag 1)) (tag 2)
  (DedupRangeMap.new (Size.ofBytes 1) mutable) (.ReservedFrz false) false
def readB := a.tree.performBorrowAccessRange (.concrete (tag 1)) (Size.ofBytes 1) (Size.ofBytes 1) .Read {} .VisitChildrenOfAccessed
def b := readB.tree.newChild (Size.ofBytes 1) (.concrete (tag 1)) (tag 3)
  (DedupRangeMap.new (Size.ofBytes 1) mutable) (.ReservedFrz false) false
def writeA := b.tree.performBorrowAccessRange (.concrete (tag 2)) Size.ZERO (Size.ofBytes 1) .Write {} .VisitChildrenOfAccessed
def writeB := writeA.tree.performBorrowAccessRange (.concrete (tag 3)) (Size.ofBytes 1) (Size.ofBytes 1) .Write {} .VisitChildrenOfAccessed
def exposeA := writeB.tree.exposeTag {} (tag 2)
def exposeB := exposeA.tree.exposeTag {} (tag 3)
def wildcardRead := exposeB.tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes 2) .Read {} .VisitChildrenOfAccessed
def v := wildcardRead.tree.newChild Size.ZERO .wildcard (tag 4)
  (DedupRangeMap.new (Size.ofBytes 2) mutable) (.ReservedFrz false) false
def finalWrite := v.tree.performBorrowAccessRange (.concrete (tag 4)) Size.ZERO (Size.ofBytes 2) .Write {} .VisitChildrenOfAccessed

/-- Every success is computed from the actual chained core operations. -/
theorem operations_complete :
    readA.status=.Completed ∧ a.outcome=.ok () ∧ readB.status=.Completed ∧ b.outcome=.ok () ∧
    writeA.status=.Completed ∧ writeB.status=.Completed ∧ exposeA.outcome=.ok () ∧ exposeB.outcome=.ok () ∧
    wildcardRead.status=.Completed ∧ v.outcome=.ok () ∧ finalWrite.status=.Completed := by
  cbv <;> decide +kernel

def rowAt (tree : BorrowTree) (byte : UInt64) : Option LocationTree :=
  (tree.locations.entries.find? (fun segment=>segment.range.start ≤ byte && byte < segment.range.stop)).map (·.data)
def permissionAt (tree : BorrowTree) (byte : UInt64) (index : UniIndex) : Option Permission :=
  (rowAt tree byte).bind fun location=>(tree.nodes.get index).map fun node=>
    ((location.perms.get index).getD node.defaultLocationState).permission

theorem cross_disabled_before_wildcard :
    permissionAt exposeB.tree 0 (ix 1)=some .Unique ∧ permissionAt exposeB.tree 1 (ix 1)=some .Disabled ∧
    permissionAt exposeB.tree 0 (ix 2)=some .Disabled ∧ permissionAt exposeB.tree 1 (ix 2)=some .Unique := by
  cbv <;> decide +kernel

theorem final_metadata :
    finalWrite.tree.nodes.data.size=4 ∧
    finalWrite.tree.roots=#[ix 0,ix 3] ∧
    finalWrite.tree.nodes.data.map (Option.map TreeNode.parent)=#[some none,some (some (ix 0)),some (some (ix 0)),some none] ∧
    finalWrite.tree.nodes.data.map (Option.map TreeNode.tag)=#[some (tag 1),some (tag 2),some (tag 3),some (tag 4)] ∧
    finalWrite.tree.nodes.data.map (Option.map TreeNode.isExposed)=#[some false,some true,some true,some false] := by
  cbv <;> decide +kernel

theorem final_cross_disabled :
    permissionAt finalWrite.tree 0 (ix 1)=some .Unique ∧ permissionAt finalWrite.tree 1 (ix 1)=some .Disabled ∧
    permissionAt finalWrite.tree 0 (ix 2)=some .Disabled ∧ permissionAt finalWrite.tree 1 (ix 2)=some .Unique := by
  cbv <;> decide +kernel

/-- Accessors below read the actual final nodes. The fallback is itself the
actual original root; every exported node lookup is proved present. -/
def rootNode : TreeNode := (seed.nodes.get (ix 0)).get (by cbv <;> decide +kernel)
def finalNode (index : Nat) : TreeNode := (finalWrite.tree.nodes.get (ix index)).getD rootNode

theorem node_endpoints :
    finalWrite.tree.nodes.get (ix 1)=some (finalNode 1) ∧
    finalWrite.tree.nodes.get (ix 2)=some (finalNode 2) ∧
    finalWrite.tree.nodes.get (ix 3)=some (finalNode 3) ∧
    (finalNode 1).isExposed=true ∧ (finalNode 2).isExposed=true ∧
    (finalNode 3).parent=none ∧ ix 3≠ix 0 := by
  cbv <;> decide +kernel

theorem exposed_only_a_or_b (index : UniIndex) (node : TreeNode)
    (present : finalWrite.tree.nodes.get index=some node) (exposed : node.isExposed=true) :
    index=ix 1 ∨ index=ix 2 := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid finalWrite.tree.nodes index node present
  rw [final_metadata.1] at bound
  have alternatives : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 ∨ index.toNat=3 := by omega
  rcases alternatives with atZero | atOne | atTwo | atThree
  · have same : index=ix 0 := GeneralBorrowNodeUpdate.index_injective _ _ (atZero.trans (show (ix 0).toNat=0 by decide).symm)
    subst index
    have shape : (finalWrite.tree.nodes.get (ix 0)).map TreeNode.isExposed=some false := by cbv <;> decide +kernel
    rw [present] at shape
    simp only [Option.map_some,Option.some.injEq] at shape
    rw [shape] at exposed
    cases exposed
  · exact Or.inl (GeneralBorrowNodeUpdate.index_injective _ _ (atOne.trans (show (ix 1).toNat=1 by decide).symm))
  · exact Or.inr (GeneralBorrowNodeUpdate.index_injective _ _ (atTwo.trans (show (ix 2).toNat=2 by decide).symm))
  · have same : index=ix 3 := GeneralBorrowNodeUpdate.index_injective _ _ (atThree.trans (show (ix 3).toNat=3 by decide).symm)
    subst index
    have shape : (finalWrite.tree.nodes.get (ix 3)).map TreeNode.isExposed=some false := by cbv <;> decide +kernel
    rw [present] at shape
    simp only [Option.map_some,Option.some.injEq] at shape
    rw [shape] at exposed
    cases exposed

theorem final_segment_count : finalWrite.tree.locations.entries.size=2 := by cbv <;> decide +kernel

def leftSegment : RangeMapSegment LocationTree := finalWrite.tree.locations.entries[0]'(by rw [final_segment_count];decide)
def rightSegment : RangeMapSegment LocationTree := finalWrite.tree.locations.entries[1]'(by rw [final_segment_count];decide)

theorem segment_endpoints :
    leftSegment∈finalWrite.tree.locations.entries.toList ∧ rightSegment∈finalWrite.tree.locations.entries.toList ∧
    leftSegment.range.start=0 ∧ leftSegment.range.stop=1 ∧ rightSegment.range.start=1 ∧ rightSegment.range.stop=2 ∧
    (RawState rightSegment.data (ix 1) (finalNode 1)).permission=.Disabled ∧
    (RawState leftSegment.data (ix 2) (finalNode 2)).permission=.Disabled := by
  refine ⟨Array.mem_toList_iff.mpr (Array.getElem_mem _),Array.mem_toList_iff.mpr (Array.getElem_mem _),?_⟩
  cbv <;> decide +kernel

end DuplicatePrefix.CurrentCallSplitOriginTrace
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallSplitOriginTrace" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved split-origin trace dependency {dependency}"
