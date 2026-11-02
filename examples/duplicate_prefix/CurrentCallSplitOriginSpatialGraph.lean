import duplicate_prefix.CurrentCallSpatialRows
import duplicate_prefix.CurrentCallSplitOriginTypedInput

namespace DuplicatePrefix.CurrentCallSplitOriginSpatialGraph
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover
open CurrentCallSplitOriginTrace
open BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
noncomputable section

theorem lookup_cases (index : UniIndex) (node : TreeNode)
    (present : finalWrite.tree.nodes.get index = some node) :
    (index=ix 0 ∧ node=finalNode 0) ∨ (index=ix 1 ∧ node=finalNode 1) ∨
    (index=ix 2 ∧ node=finalNode 2) ∨ (index=ix 3 ∧ node=finalNode 3) := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid finalWrite.tree.nodes index node present
  rw [final_metadata.1] at bound
  have cases : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 ∨ index.toNat=3 := by omega
  have same (n : Nat) (small : n < 4) (position : index.toNat=n) : index=ix n ∧ node=finalNode n := by
    have eq : index=ix n := GeneralBorrowNodeUpdate.index_injective _ _ (by
      simpa only [ix,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : n<4294967296)] using position)
    subst index
    have found : finalWrite.tree.nodes.get (ix n)=some (finalNode n) := by
      have alternatives : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
      rcases alternatives with rfl | rfl | rfl | rfl <;> cbv
    exact ⟨rfl,Option.some.inj (present.symm.trans found)⟩
  rcases cases with h | h | h | h
  · exact .inl (same 0 (by decide) h)
  · exact .inr (.inl (same 1 (by decide) h))
  · exact .inr (.inr (.inl (same 2 (by decide) h)))
  · exact .inr (.inr (.inr (same 3 (by decide) h)))

def topology : TraversalTree := ⟨#[⟨none,[1,2]⟩,⟨some 0,[]⟩,⟨some 0,[]⟩,⟨none,[]⟩]⟩

theorem topology_eq (location : LocationTree) (held : ProtectedTags) :
    (source_normal_projection finalWrite.tree location held).topology = topology := by
  cbv

theorem topology_forest : Nonempty (GeneralBorrowForest.Forest topology) := by
  refine ⟨⟨id,?_,?_,?_,?_⟩⟩
  · intro index valid parent edge
    have alt : index=0 ∨ index=1 ∨ index=2 ∨ index=3 := by change index<4 at valid; omega
    rcases alt with rfl | rfl | rfl | rfl <;> simp [topology] at edge <;> subst parent <;> decide
  · intro index valid
    have alt : index=0 ∨ index=1 ∨ index=2 ∨ index=3 := by change index<4 at valid; omega
    rcases alt with rfl | rfl | rfl | rfl <;> simp [topology]
  · intro parent valid child member
    have alt : parent=0 ∨ parent=1 ∨ parent=2 ∨ parent=3 := by change parent<4 at valid; omega
    rcases alt with rfl | rfl | rfl | rfl <;> simp [topology] at member
    rcases member with rfl | rfl <;> exact ⟨by decide,rfl⟩
  · intro child valid parent edge
    have alt : child=0 ∨ child=1 ∨ child=2 ∨ child=3 := by change child<4 at valid; omega
    rcases alt with rfl | rfl | rfl | rfl <;> simp [topology] at edge <;> subst parent <;> exact ⟨by decide,by decide⟩

theorem final_graph : GeneralBorrowStructuralHistoryState.GraphState finalWrite.tree := by
  have p1 : (finalNode 1).parent=some (ix 0) := by cbv
  have p2 : (finalNode 2).parent=some (ix 0) := by cbv
  have emptyChildren : (finalNode 1).children=#[] ∧ (finalNode 2).children=#[] ∧ (finalNode 3).children=#[] := by cbv
  refine ⟨?_,?_,?_,?_,?_,?_,by rw [show finalWrite.tree.nodes.size=4 by exact final_metadata.1]; decide⟩
  · intro location held
    rw [topology_eq]
    exact topology_forest
  · refine ⟨⟨UniIndex.toNat,?_,?_⟩⟩
    · intro index node present
      have bound := GeneralBorrowNodeUpdate.lookup_valid finalWrite.tree.nodes index node present
      exact Nat.le_of_lt bound
    · intro index node present parent edge
      rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have impossible : (finalNode 0).parent=none := by cbv
        rw [impossible] at edge; cases edge
      · have same : parent=ix 0 := by rw [p1] at edge; exact (Option.some.inj edge).symm
        subst parent
        exact ⟨finalNode 0,by cbv,by decide⟩
      · have same : parent=ix 0 := by rw [p2] at edge; exact (Option.some.inj edge).symm
        subst parent
        exact ⟨finalNode 0,by cbv,by decide⟩
      · rw [node_endpoints.2.2.2.2.2.1] at edge; cases edge
  · intro index node present child member
    rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have children : (finalNode 0).children=#[ix 1,ix 2] := by cbv
      rw [children] at member
      simp at member
      rcases member with rfl | rfl
      · exact ⟨finalNode 1,node_endpoints.1⟩
      · exact ⟨finalNode 2,node_endpoints.2.1⟩
    all_goals simp only [emptyChildren.1,emptyChildren.2.1,emptyChildren.2.2] at member
    all_goals simp at member
  · intro index node present parentless
    rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [final_metadata.2.1]; simp
    · rw [p1] at parentless; cases parentless
    · rw [p2] at parentless; cases parentless
    · rw [final_metadata.2.1]; simp
  · intro root member
    rw [final_metadata.2.1] at member
    simp at member
    rcases member with rfl | rfl
    · exact ⟨finalNode 0,by cbv,by cbv⟩
    · exact ⟨finalNode 3,node_endpoints.2.2.1,node_endpoints.2.2.2.2.2.1⟩
  · have free : finalWrite.tree.tagMapping.deassigned=#[] := by cbv
    refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
    · intro index member; simp only [free,Array.mem_empty_iff] at member
    · intro index member; simp only [free,Array.mem_empty_iff] at member
    · rw [free]; simp
    · cbv
    · cbv; decide
    · intro index node present
      rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cbv

end
end DuplicatePrefix.CurrentCallSplitOriginSpatialGraph
