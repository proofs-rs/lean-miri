import duplicate_prefix.CandidateCallBindings
import duplicate_prefix.S05DiagnosticFnEntryRead
import duplicate_prefix.S05LiveSubtreeCacheSoundness
import duplicate_prefix.GeneralBorrowStructuralHistoryState

/-! Static certificate for the existing six-node raw tree and one completed
origin choice. No execution, history, ordinary-input or final-safety claim. -/
namespace DuplicatePrefix.CandidateSixNodeCertificate
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership S05DiagnosticFnEntryRead GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
set_option autoImplicit false

private theorem small (index : UniIndex) (bound : index.toNat < 6) :
    index=ix 0 ∨ index=ix 1 ∨ index=ix 2 ∨ index=ix 3 ∨ index=ix 4 ∨ index=ix 5 := by
  have choices : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 ∨
      index.toNat=3 ∨ index.toNat=4 ∨ index.toNat=5 := by omega
  have indexEq : index = ix index.toNat := by cases index; simp [ix,UniIndex.toNat]
  rcases choices with h | h | h | h | h | h
  all_goals rw [h] at indexEq
  all_goals simp [indexEq]

private theorem nodes (index : UniIndex) (node : TreeNode)
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
  #[⟨.Unique,true,.None⟩,⟨.Cell,false,.Write⟩,⟨.Disabled,true,.Read⟩,
    ⟨.Cell,true,.None⟩,⟨.ReservedFrz false,false,.Read⟩,⟨.ReservedFrz false,true,.Read⟩]
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

theorem profile : GeneralBorrowLocationSifaConsistency.Profile tree location held := by
  constructor
  · intro index node present
    rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals first | exact ⟨.None,rfl,by decide⟩ | exact ⟨.Write,rfl,by decide⟩ | exact ⟨.Read,rfl,by decide⟩
  · intro index absent
    have outside : 6 ≤ index.toNat := by
      by_cases bound : index.toNat < 6
      · rcases small index bound with rfl | rfl | rfl | rfl | rfl | rfl <;> cases absent
      · omega
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by change 6 ≤ index.toNat; exact outside)]

theorem coherent : LocationCoherent tree location held := by
  intro query kind
  by_cases bound : query.toNat < 6
  · rcases small query bound with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases kind <;> with_unfolding_all decide
  · have neq (n : Nat) (small : n < 6) : query ≠ ix n := by
      intro same; subst query
      have converted : (ix n).toNat = n := by simp [ix,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : n < 2^32)]
      rw [converted] at bound; omega
    have absent : location.exposedCache.nodes.get query = none := by
      unfold UniValMap.get
      rw [Array.getElem?_eq_none (by change 6 ≤ query.toNat;omega)]
    have entries : tree.nodes.entries.toList = [(ix 0,original),(ix 1,a),(ix 2,d),(ix 3,b),(ix 4,v),(ix 5,w)] := by with_unfolding_all rfl
    have walk0 : walk tree.nodes (tree.nodes.size+1) (ix 0) = [ix 0] := by with_unfolding_all rfl
    have walk4 : walk tree.nodes (tree.nodes.size+1) (ix 4) = [ix 4,ix 2,ix 1] := by with_unfolding_all rfl
    have counts : cardinality tree.nodes (effective location held) query kind = 0 := by
      unfold cardinality
      rw [entries]
      simp [contributes,original,a,d,b,v,w,walk0,walk4,
        neq 0 (by decide),neq 1 (by decide),neq 2 (by decide),neq 4 (by decide)]
    simp only [counter,absent,Option.getD_none,counts]
    cases kind <;> rfl

/-- The existing numeric cache condition holds even though blanket Write-live fails. -/
theorem sound (support : UniIndex → Prop) :
    S05LiveSubtreeCacheSoundness.Soundness tree location held support := by
  intro query node inside present witness witnessNode found walked live
  rcases nodes query node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rcases nodes witness witnessNode found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals first
    | exact ⟨.None,rfl,by decide⟩
    | exact ⟨.Write,rfl,by decide⟩
    | exact ⟨.Read,rfl,by decide⟩
    | (have blocked := live (ix 2) d rfl (by decide +kernel) (by decide +kernel)
       exact False.elim (blocked.1 rfl))
    | (exfalso; revert walked; decide +kernel)

theorem scalar_identity (byte : Nat) (inside : byte < 2) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    PreciseState precise byte index = RawState location index node := by
  have bytes : byte=0 ∨ byte=1 := by omega
  rcases bytes with rfl | rfl
  all_goals rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rfl

/-- Full candidate Refines, not just pointwise scalar inclusion. -/
theorem refines (allocation : Allocation Provenance BorrowTree)
    (extra : allocation.extra = tree) (length : allocation.len = 2) : Refines allocation held precise := by
  rw [Refines,extra,length]
  refine ⟨completes,rfl,?_,?_,?_⟩
  · intro entry member
    simp [precise] at member
    rcases member with rfl | rfl <;> rfl
  · intro byte inside
    exact ⟨⟨⟨0,2⟩,location⟩,by simp [tree,RangeMapNonempty.homogeneous],by change 0 ≤ byte; omega,inside⟩
  · intro segment stored
    have same : segment = ⟨⟨0,2⟩,location⟩ := by simpa [tree,RangeMapNonempty.homogeneous,DedupRangeMap.new] using stored
    subst segment
    refine ⟨by decide,by decide,coherent,profile,?_⟩
    intro byte lower upper index node present
    have possible : (RawState location index node).possible = true := by
      rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
    rw [scalar_identity byte upper index node present]
    exact ⟨possible,possible,fun _ _ rights => rights⟩

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
  rw [scalar_identity byte inside index node present]
  rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals constructor
  all_goals first
    | (intro path; have impossible := below_branch path; change 1 ≤ 0 at impossible; omega)
    | (intro _; change Allows _ false .Write _; unfold Allows GeneralBorrowExposedConditionalWritePermissions.Compatible; decide +kernel)

theorem not_write_live :
    ¬ (∀ query node, tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → supports (effective location held witness witnessNode) .Write = true →
      (RawState location query node).permission ≠ .Disabled ∧ (RawState location query node).permission ≠ .Frozen) := by
  intro live
  have bad := live (ix 2) d rfl (ix 4) v rfl rfl (by decide +kernel) (by decide +kernel)
  exact bad.1 rfl

/-- Every genuine support area for A contains D by child closure. -/
theorem no_area_write_live (area : GeneralBorrowWildcardControlStack.Support tree (ix 1)) :
    ¬ (∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → supports (effective location held witness witnessNode) .Write = true →
      (RawState location query node).permission ≠ .Disabled ∧ (RawState location query node).permission ≠ .Frozen) := by
  intro live
  have inside : area.contains (ix 2) := area.children (ix 1) a area.rooted rfl (ix 2) (by decide)
  have bad := live (ix 2) d inside rfl (ix 4) v rfl rfl (by decide +kernel) (by decide +kernel)
  exact bad.1 rfl

private def topology : TraversalTree :=
  ⟨#[⟨none,[]⟩,⟨none,[2]⟩,⟨some 1,[4]⟩,⟨none,[5]⟩,⟨some 2,[]⟩,⟨some 3,[]⟩]⟩
private theorem nat_cases (n : Nat) (bound : n < 6) :
    n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
private def forest : GeneralBorrowForest.Forest topology where
  rank := id
  parents := by
    intro index valid parent edge
    rcases nat_cases index valid with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [topology] at edge
    all_goals subst parent
    all_goals exact ⟨by decide,by decide⟩
  childrenDistinct := by
    intro index valid
    rcases nat_cases index valid with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [topology]
  childParent := by
    intro index valid child member
    rcases nat_cases index valid with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [topology] at member
    all_goals subst child
    all_goals exact ⟨by decide,rfl⟩
  parentChild := by
    intro index valid parent edge
    rcases nat_cases index valid with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [topology] at edge
    all_goals subst parent
    all_goals exact ⟨by decide,by decide⟩
private def depth : GeneralBorrowExposure.ParentDepth tree.nodes where
  depth index := index.toNat
  bounded := by
    intro index node present
    rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  parent := by
    intro index node present parent edge
    rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals first | contradiction | skip
    all_goals simp only [d,v,w,Option.some.injEq] at edge
    all_goals subst parent
    all_goals exact ⟨_,rfl,by decide⟩

theorem graph : GeneralBorrowStructuralHistoryState.GraphState tree where
  forest := by
    intro location protections
    have same : (source_normal_projection tree location protections).topology = topology := by with_unfolding_all rfl
    rw [same]
    exact ⟨forest⟩
  depth := ⟨depth⟩
  children := by
    intro index node present child member
    exact ((parent_children index node present child).mp member).imp (fun node h => h.1)
  covered := by
    intro index node present parentless
    exact (completes.2.2.2.2.1 index node present).2.2.2.mp parentless
  rootNodes := by
    intro root member
    have choices : root=ix 0 ∨ root=ix 1 ∨ root=ix 3 := by simpa [tree] using member
    rcases choices with rfl | rfl | rfl <;> exact ⟨_,rfl,rfl⟩
  allocator := {
    pool := {
      bounded := by intro index member; simp [tree] at member
      vacant := by intro index member; simp [tree] at member
      nodup := by decide }
    accounting := rfl
    unique := by unfold GeneralBorrowGcAllocator.KeyUnique; decide
    nodeTags := by intro index node present; exact (completes.2.2.2.2.1 index node present).1 }
  fits := by decide

theorem order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree := by
  intro index node present parent parentNode edge parentPresent
  rcases nodes index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals first | contradiction | skip
  all_goals simp only [d,v,w,Option.some.injEq] at edge
  all_goals subst parent
  all_goals have same := Option.some.inj parentPresent.symm
  all_goals subst parentNode
  all_goals decide

/-- This is a static failure of the retained-contributor condition, not execution. -/
theorem no_area_skip_stable (area : GeneralBorrowWildcardControlStack.Support tree (ix 1)) :
    ¬ S05WriteCacheContributorOwnership.SkipStable tree location held (some (tag 4)) area.contains := by
  intro stable
  have bad := stable (ix 1) a area.rooted rfl (by decide +kernel) (ix 4) v rfl rfl (by decide +kernel) (by decide +kernel)
  change true = false at bad
  cases bad

end DuplicatePrefix.CandidateSixNodeCertificate
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateSixNodeCertificate." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved six-node certificate dependency {dependency}"
