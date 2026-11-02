import duplicate_prefix.GeneralBorrowRangePreserves
/-! A checked counterexample to the sufficiency of graph coverage and anchor
ownership alone for multiple-root access. This constructed state is not claimed
to arise from a valid Rust caller history. A valid-history generalization needs
additional exposed-reference/cache invariants, proved from that history. -/
namespace DuplicatePrefix.GeneralBorrowMultiRootGap
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def first : UniIndex := ⟨0⟩
def second : UniIndex := ⟨1⟩
def oldNode : TreeNode := ⟨⟨1,by decide⟩,none,#[],.Disabled,.None,false,none⟩
def anchorNode : TreeNode := ⟨⟨2,by decide⟩,none,#[],.Disabled,.None,false,none⟩
def location : LocationTree := ⟨⟨#[some ⟨.Disabled,false,.None⟩,some ⟨.Unique,true,.None⟩]⟩,{}⟩
def tree : BorrowTree := ⟨⟨#[(oldNode.tag,first),(anchorNode.tag,second)],#[]⟩,
  ⟨#[some oldNode,some anchorNode]⟩,RangeMapNonempty.homogeneous 1 location,#[first,second]⟩

private theorem index_eq (left right : UniIndex) (same : left.toNat = right.toNat) : left = right := by
  cases left with | mk left =>
    cases right with | mk right =>
      congr 1
      exact UInt32.toNat_inj.mp same

private theorem lookup_cases (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    (index = first ∧ node = oldNode) ∨ (index = second ∧ node = anchorNode) := by
  have valid : index.toNat < 2 := by
    by_cases bound : index.toNat < 2
    · exact bound
    · have absent : tree.nodeAt index = none := by
        unfold BorrowTree.nodeAt UniValMap.get
        rw [Array.getElem?_eq_none (xs := tree.nodes.data) (i := index.toNat) (by simpa [tree] using bound)]
      rw [absent] at present
      cases present
  have two : index.toNat = 0 ∨ index.toNat = 1 := by omega
  rcases two with zero | one
  · have same : index = first := index_eq index first zero
    subst index
    exact .inl ⟨rfl,Option.some.inj present.symm⟩
  · have same : index = second := index_eq index second one
    subst index
    exact .inr ⟨rfl,Option.some.inj present.symm⟩

theorem roots_cover : GeneralBorrowGraph.RootsCover tree := by
  intro index node present parentless
  rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

theorem children : GeneralBorrowGraph.ChildNodes tree := by
  intro index node present child member
  rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [oldNode,anchorNode] at member

def depth : ParentDepth tree.nodes where
  depth := fun _ => 0
  bounded := by intro index node present;decide
  parent := by
    intro index node present before parent
    rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [oldNode,anchorNode] at parent

def normal : NormalTreeState := {
  topology := ⟨#[⟨none,[]⟩,⟨none,[]⟩]⟩
  defaultStates := #[⟨.Disabled,false,.None⟩,⟨.Disabled,false,.None⟩]
  protectedNodes := []
  locationStates := #[some ⟨.Disabled,false,.None⟩,some ⟨.Unique,true,.None⟩]
}
private theorem projection_exact : source_normal_projection tree location {} = normal := by
  unfold_general_projection
  unfold_general_topology
  with_unfolding_all rfl

def forest : GeneralBorrowForest.Forest (source_normal_projection tree location {}).topology := by
  rw [projection_exact]
  refine ⟨fun _ => 0,?_,?_,?_,?_⟩
  · intro index valid parent edge
    have cases : index = 0 ∨ index = 1 := by change index < 2 at valid;omega
    rcases cases with rfl | rfl <;> contradiction
  · intro index valid
    have cases : index = 0 ∨ index = 1 := by change index < 2 at valid;omega
    rcases cases with rfl | rfl <;> exact List.nodup_nil
  · intro parent valid child member
    have cases : parent = 0 ∨ parent = 1 := by change parent < 2 at valid;omega
    rcases cases with rfl | rfl <;> contradiction
  · intro child valid parent edge
    have cases : child = 0 ∨ child = 1 := by change child < 2 at valid;omega
    rcases cases with rfl | rfl <;> contradiction

theorem owned : GeneralBorrowRange.LocationOwned tree {} second .Read location := by
  refine ⟨⟨forest⟩,?_⟩
  rw [projection_exact]
  refine ⟨by decide,rfl,rfl,?_⟩
  intro index valid
  have cases : index = 0 ∨ index = 1 := by change index < 2 at valid;omega
  rcases cases with rfl | rfl
  · refine ⟨⟨.Disabled,false,.None⟩,rfl,?_⟩
    change true = true ∧ (false = false ∨ _)
    exact ⟨rfl,Or.inl rfl⟩
  · refine ⟨⟨.Unique,true,.None⟩,rfl,?_⟩
    change true = true ∧ Permission.Unique ≠ .Disabled
    exact ⟨rfl,by decide⟩
private theorem normal_location :
    (tree.performNormalAccessAt location second .Read {} .VisitChildrenOfAccessed).location = location := by
  unfold BorrowTree.performNormalAccessAt
  rw [projection_exact]
  with_unfolding_all rfl

private theorem normal_status :
    (tree.performNormalAccessAt location second .Read {} .VisitChildrenOfAccessed).access.status = .Completed := by
  unfold BorrowTree.performNormalAccessAt
  rw [projection_exact]
  with_unfolding_all rfl

private theorem normal_outcome :
    (tree.performNormalAccessAt location second .Read {} .VisitChildrenOfAccessed).outcome = .ok () := by
  unfold BorrowTree.performNormalAccessAt
  rw [projection_exact]
  with_unfolding_all rfl

private theorem normal_root :
    (tree.performNormalAccessAt location second .Read {} .VisitChildrenOfAccessed).access.root = second.toNat := by
  unfold BorrowTree.performNormalAccessAt
  rw [projection_exact]
  with_unfolding_all rfl

private theorem wildcard_failure : tree.performWildcardAccessAt location first (some anchorNode.tag) .Read {} false =
    ⟨location,.NoValidExposedReferences first (some first)⟩ := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step1 : scan () (location,false,.Completed,#[(first,false)],0) =
      .yield (location,false,.Completed,#[(first,true)],1) := by
    with_unfolding_all rfl
  have step2 : scan () (location,false,.Completed,#[(first,true)],1) =
      .yield (location,false,.NoValidExposedReferences first (some first),#[],2) := by
    with_unfolding_all rfl
  have step3 : scan () (location,false,.NoValidExposedReferences first (some first),#[],2) =
      .done (location,false,.NoValidExposedReferences first (some first),#[],2) := by
    with_unfolding_all rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step3,bind,pure]
  rfl

/-- The real whole location wrapper propagates the first root's wildcard
failure, despite ordinary graph coverage and anchor permission ownership. -/
theorem actual_failure :
    source_access_status (source_tree_access_at tree location (some second) .Read {} .VisitChildrenOfAccessed ⟨0,1⟩) =
      some (.WildcardFailure ⟨0,1⟩ (.NoValidExposedReferences first (some first))) := by
  simp_tree_helpers
  simp only [normal_outcome,normal_status,normal_root,normal_location,index_self]
  simp only [show tree.roots = #[first,second] from rfl,
    Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    List.range'_succ,List.range'_zero,bind,pure]
  simp only [show #[first,second].size = 2 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 2 = [0,1] from rfl]
  simp [List.forIn_cons,List.forIn_nil,wildcard_failure,bind,pure,
    show tree.nodes.get second = some anchorNode from rfl,show second ≠ first from by decide]
end DuplicatePrefix.GeneralBorrowMultiRootGap
