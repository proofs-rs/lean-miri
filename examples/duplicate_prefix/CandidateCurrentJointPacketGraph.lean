import duplicate_prefix.CandidateCurrentJointCall
import duplicate_prefix.S05ZeroCellJointCertificate

/-! Graph certificate for the ACTUAL generated six-node call-time packet.
Only current graph data and fixed A/B origin1 bindings are used. -/
namespace DuplicatePrefix.CandidateCurrentJointPacketGraph
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open S05ZeroCellTypedGeneratedPrefix (ix tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

 def original : TreeNode := ⟨tag 1,none,#[],.Disabled,.None,true,none⟩
def a : TreeNode := ⟨tag 2,none,#[ix 2],.Cell,.Read,false,none⟩
def d : TreeNode := ⟨tag 3,some (ix 1),#[ix 4],.ReservedFrz false,.Read,false,none⟩
def b : TreeNode := ⟨tag 4,none,#[ix 5],.Cell,.Read,false,none⟩
def v : TreeNode := ⟨tag 5,some (ix 2),#[],.ReservedFrz false,.Read,true,none⟩
def w : TreeNode := ⟨tag 6,some (ix 3),#[],.ReservedFrz false,.Read,false,none⟩
def tree : BorrowTree := {
  tagMapping := ⟨#[(tag 1,ix 0),(tag 2,ix 1),(tag 3,ix 2),(tag 4,ix 3),(tag 5,ix 4),(tag 6,ix 5)],#[]⟩
  nodes := ⟨#[some original,some a,some d,some b,some v,some w]⟩
  locations := S05ZeroCellJointCertificate.raw.locations
  roots := #[ix 0,ix 1,ix 3] }

theorem actual_graph : S05ZeroCellJointCertificate.raw = tree := by cbv
private theorem small (index : UniIndex) (bound : index.toNat < 6) :
    index=ix 0 ∨ index=ix 1 ∨ index=ix 2 ∨ index=ix 3 ∨ index=ix 4 ∨ index=ix 5 := by
  have choices : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 ∨
      index.toNat=3 ∨ index.toNat=4 ∨ index.toNat=5 := by omega
  have indexEq : index = ix index.toNat := by cases index; simp [ix,UniIndex.toNat]
  rcases choices with h | h | h | h | h | h
  all_goals rw [h] at indexEq
  all_goals simp [indexEq]

theorem nodes (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (index=ix 0 ∧ node=original) ∨ (index=ix 1 ∧ node=a) ∨
    (index=ix 2 ∧ node=d) ∨ (index=ix 3 ∧ node=b) ∨
    (index=ix 4 ∧ node=v) ∨ (index=ix 5 ∧ node=w) := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  change index.toNat < 6 at bound
  rcases small index bound with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals change some _ = some node at present
  all_goals injection present with same
  all_goals subst node
  all_goals simp

/-- Each wildcard root chooses older exposed original tag1, once across bytes. -/
def completion : Completion :=
  ⟨#[none,some (ix 0),some (ix 1),some (ix 0),some (ix 2),some (ix 3)],#[0,1,2,1,3,2]⟩
def row : Array LocationState :=
  #[⟨.Unique,true,.None⟩,⟨.Cell,true,.Write⟩,⟨.Disabled,true,.Read⟩,
    ⟨.Cell,true,.None⟩,⟨.ReservedFrz false,false,.Read⟩,⟨.ReservedFrz false,true,.Read⟩]

theorem actual_precise_row : row = Array.ofFn S05ZeroCellJointCertificate.state := by cbv
def precise : PreciseAllocation := ⟨completion,#[row,row]⟩
def held : ProtectedTags := {}
def pointer (id : AllocId) (address : UInt64) : PointerInstance :=
  ⟨id,⟨Size.ofBytes address,.concrete id (tag 6)⟩,ix 5⟩

private theorem parent_children (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (child : UniIndex) :
    child ∈ node.children.toList ↔
      ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index := by
  constructor
  · intro member
    rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [original,a,d,b,v,w] at member
    all_goals first | contradiction | (subst child; exact ⟨_,rfl,rfl⟩)
  · rintro ⟨childNode,found,edge⟩
    rcases nodes child childNode found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals first | contradiction | skip
    all_goals simp only [d,v,w,Option.some.injEq] at edge
    all_goals subst index
    all_goals have same := Option.some.inj present.symm
    all_goals subst node
    all_goals simp [a,d,b]

theorem completes : Completes tree completion := by
  refine ⟨rfl,rfl,by decide,?_,?_,?_,?_⟩
  · intro position root listed
    have bound := (Array.getElem?_eq_some_iff.mp listed).1
    change position < 3 at bound
    have choices : position=0 ∨ position=1 ∨ position=2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals have same : root = _ := Option.some.inj listed.symm
    all_goals subst root
    all_goals exact ⟨_,rfl,rfl⟩
  · intro index node present
    refine ⟨?_,parent_children index node present,?_,?_⟩
    · rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
    · intro parent edge
      rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals first | contradiction | (simp only [d,v,w,Option.some.injEq] at edge; subst parent; rfl)
    · rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · intro position root listed
    have bound := (Array.getElem?_eq_some_iff.mp listed).1
    change position < 3 at bound
    have choices : position=0 ∨ position=1 ∨ position=2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals have same : root = _ := Option.some.inj listed.symm
    all_goals subst root
    · rfl
    all_goals refine ⟨0,ix 0,ix 0,_,original,by decide,rfl,rfl,rfl,rfl,by decide,Path.refl _ _ rfl,rfl⟩
  · intro child parent edge
    have bound := (Array.getElem?_eq_some_iff.mp edge).1
    change child.toNat < 6 at bound
    rcases small child bound with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [completion,ix,UniIndex.toNat] at edge
    all_goals subst parent
    all_goals exact ⟨⟨_,rfl⟩,⟨_,rfl⟩,by decide⟩


private def branch (index : UniIndex) : Nat := if index=ix 1 ∨ index=ix 2 ∨ index=ix 4 then 1 else 0
private theorem edge_branch (child parent : UniIndex)
    (edge : completion.parents[child.toNat]? = some (some parent)) : branch parent ≤ branch child := by
  have bound := (Array.getElem?_eq_some_iff.mp edge).1
  change child.toNat < 6 at bound
  rcases small child bound with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [completion,ix,UniIndex.toNat] at edge
  all_goals subst parent
  all_goals decide
private theorem below_branch {ancestor child : UniIndex} (path : Below completion ancestor child) :
    branch ancestor ≤ branch child := by
  induction path with
  | refl => exact Nat.le_refl _
  | step edge _ earlier => exact Nat.le_trans earlier (edge_branch _ _ edge)

theorem source_rights (allocation : Allocation Provenance BorrowTree)
    (extra : allocation.extra = tree) (id : AllocId) (address : UInt64)
    (byte : Nat) (inside : byte < 2) : LoanRights allocation held precise (pointer id address) byte .mut := by
  intro index node present
  rw [extra] at present
  rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals constructor
  all_goals first
    | (intro path; have impossible := below_branch path; change 1 ≤ 0 at impossible; omega)
    | (intro _; change Allows _ false .Write _; unfold Allows GeneralBorrowExposedConditionalWritePermissions.Compatible; rcases (show byte=0 ∨ byte=1 by omega) with rfl | rfl <;> cbv <;> try simp)


end DuplicatePrefix.CandidateCurrentJointPacketGraph
