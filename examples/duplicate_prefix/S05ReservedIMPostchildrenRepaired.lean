import duplicate_prefix.DuplicatePrefixResidualWriteRepaired

/-! The SAME source-generated operations as the C diagnostic, now under the
complete held-sensitive no-op guard.
This renamed completion theorem does not reinterpret that C failure. The
component's child effects, cache and consistency are retained. This is not
ordinary admission, a whole Call/Result or a UB-freedom theorem. -/
namespace DuplicatePrefix.S05ReservedIMPostchildrenRepaired
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposureCardinality
open GeneralBorrowExposureAncestorFold
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 1000000
set_option linter.unusedSimpArgs false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def tag (n : UInt64) (h : n ≠ 0 := by decide) : BorTag := ⟨n,h⟩
def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def seed := BorrowTree.new (tag 1) (Size.ofBytes 1)
def original := seed.exposeTag {} (tag 1)
def a := original.tree.newChild Size.ZERO .wildcard (tag 2)
  (DedupRangeMap.new Size.ZERO ⟨.ReservedIM,false,.Write⟩) .ReservedIM false
def readA := a.tree.performBorrowAccessRange (.concrete (tag 2)) Size.ZERO (Size.ofBytes 1)
  .Read {} .VisitChildrenOfAccessed
def d := readA.tree.newChild Size.ZERO (.concrete (tag 2)) (tag 3)
  (DedupRangeMap.new (Size.ofBytes 1) ⟨.ReservedFrz false,true,.Read⟩) (.ReservedFrz false) false
def firstWrite := d.tree.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 1)
  .Write {} .VisitChildrenOfAccessed
def b := firstWrite.tree.newChild Size.ZERO .wildcard (tag 4)
  (DedupRangeMap.new Size.ZERO ⟨.Cell,false,.Write⟩) .Cell false
def v := b.tree.newChild Size.ZERO (.concrete (tag 3)) (tag 5)
  (DedupRangeMap.new Size.ZERO ⟨.ReservedFrz false,false,.Read⟩) (.ReservedFrz false) false
def exposed := v.tree.exposeTag {} (tag 5)
def secondWrite := exposed.tree.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 1)
  .Write {} .VisitChildrenOfAccessed
def tree := secondWrite.tree
def initial : LocationTree := (tree.locations.entries[0]'(by cbv)).data
def node (n : Nat) : TreeNode := (tree.nodes.get (ix n)).getD ⟨tag 1,none,#[],.Disabled,.None,false,none⟩
def child := tree.performWildcardAccessAt initial (ix 4) (some (tag 4)) .Write {} true
def result := tree.performWildcardAccessAt initial (ix 1) (some (tag 4)) .Write {} true

theorem operations_complete : original.outcome = .ok () ∧ a.outcome = .ok () ∧
    readA.status = .Completed ∧ d.outcome = .ok () ∧ firstWrite.status = .Completed ∧
    b.outcome = .ok () ∧ v.outcome = .ok () ∧ exposed.outcome = .ok () ∧
    secondWrite.status = .Completed := by cbv

/-- Creating V weakens the stored ancestor SIFAs. The subsequent real origin
Write prunes disabled D at entry, retains V and re-records A's Write SIFA. -/
theorem sifa_route :
    ((v.tree.locations.entries[0]'(by cbv)).data.perms.get (ix 1)).map LocationState.idempotentForeignAccess = some .Read ∧
    initial.perms.get (ix 1) = some ⟨.ReservedIM,true,.Write⟩ ∧
    initial.perms.get (ix 2) = some ⟨.Disabled,true,.Read⟩ ∧
    (node 1).isExposed = false ∧ (node 4).isExposed = true ∧
    tree.roots = #[ix 0,ix 1,ix 3] ∧ (node 3).tag = tag 4 := by cbv; simp

theorem actual_child_effect : child.status = .Completed ∧
    child.location.perms.get (ix 4) = some ⟨.Disabled,false,.Write⟩ ∧
    initial.exposedCache.accessRelatedness (ix 1) (ix 1) .Write true false = some .EitherAccess ∧
    child.location.exposedCache.accessRelatedness (ix 1) (ix 1) .Write true false = some .ForeignAccess ∧
    initial.exposedCache.nodes.get (ix 1) = some ⟨1,1⟩ ∧
    child.location.exposedCache.nodes.get (ix 1) = some ⟨0,0⟩ := by cbv

/-- The same real child-first execution now completes, retaining the
completed child's permission and cache updates. -/
theorem actual_completed : result.status = .Completed ∧
    result.location.perms.get (ix 4) = some ⟨.Disabled,false,.Write⟩ ∧
    result.location.exposedCache = child.location.exposedCache := by cbv


/- Computed projections of THIS generated five-node result. The kernel
identities below are proof normalization only, never substituted operations. -/
private def n0 : TreeNode := ⟨tag 1,none,#[],.Disabled,.None,true,none⟩
private def n1 : TreeNode := ⟨tag 2,none,#[ix 2],.ReservedIM,.Read,false,none⟩
private def n2 : TreeNode := ⟨tag 3,some (ix 1),#[ix 4],.ReservedFrz false,.Read,false,none⟩
private def n3 : TreeNode := ⟨tag 4,none,#[],.Cell,.Write,false,none⟩
private def n4 : TreeNode := ⟨tag 5,some (ix 2),#[],.ReservedFrz false,.Read,true,none⟩
private def nodeTable : Array (Option TreeNode) := #[some n0,some n1,some n2,some n3,some n4]
private def beforeTable : LocationTree := {
  perms := ⟨#[some ⟨.Unique,true,.None⟩,some ⟨.ReservedIM,true,.Write⟩,some ⟨.Disabled,true,.Read⟩]⟩
  exposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩,none,some ⟨1,1⟩]⟩⟩ }
private def afterTable : LocationTree := {
  perms := ⟨#[some ⟨.Unique,true,.None⟩,some ⟨.ReservedIM,true,.Write⟩,some ⟨.Disabled,true,.Read⟩,none,some ⟨.Disabled,false,.Write⟩]⟩
  exposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨0,0⟩,some ⟨0,0⟩,none,some ⟨0,0⟩]⟩⟩ }
private theorem nodes_data : tree.nodes.data = nodeTable := by cbv
private theorem initial_eq : initial = beforeTable := by cbv
private theorem child_eq : child.location = afterTable := by cbv
private theorem result_eq : result.location = afterTable := by cbv
private def topology := (source_normal_projection tree initial {}).topology
private def topologyTable : Array TraversalNode := #[⟨none,[]⟩,⟨none,[2]⟩,⟨some 1,[4]⟩,⟨none,[]⟩,⟨some 2,[]⟩]
private theorem topology_data : topology.nodes = topologyTable := by cbv
private theorem entries : tree.nodes.entries.toList = [(ix 0,n0),(ix 1,n1),(ix 2,n2),(ix 3,n3),(ix 4,n4)] := by cbv
private theorem walk0 : walk tree.nodes (tree.nodes.size+1) (ix 0) = [ix 0] := by cbv
private theorem walk4 : walk tree.nodes (tree.nodes.size+1) (ix 4) = [ix 4,ix 2,ix 1] := by cbv
attribute [local irreducible] tree initial child result

private theorem small (index : UniIndex) (bound : index.toNat < 5) :
    index=ix 0 ∨ index=ix 1 ∨ index=ix 2 ∨ index=ix 3 ∨ index=ix 4 := by
  have choices : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 ∨ index.toNat=3 ∨ index.toNat=4 := by omega
  have indexEq : index = ix index.toNat := by cases index; simp [ix,UniIndex.toNat]
  rcases choices with h | h | h | h | h
  all_goals rw [h] at indexEq
  all_goals simp [indexEq]

private theorem nodes (index : UniIndex) (entry : TreeNode) (present : tree.nodes.get index = some entry) :
    (index=ix 0 ∧ entry=n0) ∨ (index=ix 1 ∧ entry=n1) ∨ (index=ix 2 ∧ entry=n2) ∨
    (index=ix 3 ∧ entry=n3) ∨ (index=ix 4 ∧ entry=n4) := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index entry present
  rw [nodes_data] at bound
  change index.toNat < 5 at bound
  rcases small index bound with rfl | rfl | rfl | rfl | rfl
  all_goals simp [UniValMap.get,nodes_data,nodeTable,ix,UniIndex.toNat] at present
  all_goals subst entry
  all_goals simp

/-- Exact raw parent-tag ordering, with no history premise. -/
theorem parent_tag_order : ∀ child childNode, tree.nodes.get child = some childNode →
    ∀ parent parentNode, childNode.parent = some parent → tree.nodes.get parent = some parentNode →
      parentNode.tag.value ≤ childNode.tag.value := by
  intro child childNode present parent parentNode edge parentPresent
  rcases nodes child childNode present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals simp only [n0,n1,n2,n3,n4,Option.some.injEq,reduceCtorEq] at edge
  all_goals subst parent
  all_goals simp [UniValMap.get,nodes_data,nodeTable,ix,UniIndex.toNat] at parentPresent
  all_goals subst parentNode
  all_goals decide +kernel

def forest : GeneralBorrowForest.Forest topology := by
  have same : topology = ⟨topologyTable⟩ := congrArg TraversalTree.mk topology_data
  rw [same]
  refine { rank := id, parents := ?_, childrenDistinct := ?_, childParent := ?_, parentChild := ?_ }
  · intro i valid parent edge
    change i < 5 at valid
    have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl
    all_goals cbv at edge
    all_goals simp only [Option.some.injEq,reduceCtorEq] at edge
    all_goals subst parent
    all_goals simp [topologyTable]
  · intro i valid
    change i < 5 at valid
    have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl
    all_goals simp [topologyTable]
  · intro i valid child member
    change i < 5 at valid
    have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl
    all_goals simp [topologyTable] at member
    all_goals subst child
    all_goals simp [topologyTable]
  · intro i valid parent edge
    change i < 5 at valid
    have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl
    all_goals cbv at edge
    all_goals simp only [Option.some.injEq,reduceCtorEq] at edge
    all_goals subst parent
    all_goals simp [topologyTable]

private theorem get_none {α : Type} (map : UniValMap α) (index : UniIndex)
    (outside : map.data.size ≤ index.toNat) : map.get index = none := by
  unfold UniValMap.get
  rw [Array.getElem?_eq_none outside]

private theorem profile (location : LocationTree) (chosen : location = beforeTable ∨ location = afterTable) :
    GeneralBorrowLocationSifaConsistency.Profile tree location {} := by
  constructor
  · intro index entry present
    rcases nodes index entry present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals rcases chosen with rfl | rfl
    all_goals first
      | exact ⟨.None,by decide +kernel,by decide +kernel⟩
      | exact ⟨.Write,by decide +kernel,by decide +kernel⟩
      | exact ⟨.Read,by decide +kernel,by decide +kernel⟩
  · intro index absent
    have outside : 5 ≤ index.toNat := by
      by_cases bound : index.toNat < 5
      · rcases small index bound with rfl | rfl | rfl | rfl | rfl
        all_goals simp [UniValMap.get,nodes_data,nodeTable,ix,UniIndex.toNat] at absent
      · omega
    rcases chosen with rfl | rfl
    all_goals apply get_none
    all_goals apply Nat.le_trans (m := 5)
    all_goals first | decide +kernel | exact outside

private theorem possible (location : LocationTree) (chosen : location = beforeTable ∨ location = afterTable) :
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location := by
  intro index entry present
  rcases nodes index entry present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rcases chosen with rfl | rfl
  all_goals decide +kernel

theorem runtime_consistency :
    (GeneralBorrowLocationSifaConsistency.Profile tree initial {} ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) ∧
    (GeneralBorrowLocationSifaConsistency.Profile tree result.location {} ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location) := by
  rw [initial_eq,result_eq]
  exact ⟨⟨profile _ (.inl rfl),possible _ (.inl rfl)⟩,⟨profile _ (.inr rfl),possible _ (.inr rfl)⟩⟩

private theorem coherent (location : LocationTree) (chosen : location = beforeTable ∨ location = afterTable) :
    LocationCoherent tree location {} := by
  intro query kind
  by_cases bound : query.toNat < 5
  · rcases small query bound with rfl | rfl | rfl | rfl | rfl
    all_goals rcases chosen with rfl | rfl
    all_goals cases kind
    all_goals simp only [LocationCoherent,Coherent,counter,cardinality]
    all_goals rw [entries]
    all_goals simp only [contributes,n0,n1,n2,n3,n4,walk0,walk4,List.filter_cons,List.filter_nil]
    all_goals decide +kernel
  · have neq (n : Nat) (small : n < 5) : query ≠ ix n := by
      intro same;subst query
      have converted : (ix n).toNat = n := by simp [ix,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : n < 2^32)]
      rw [converted] at bound;omega
    have counts : cardinality tree.nodes (GeneralBorrowExposureCardinality.effective location {}) query kind = 0 := by
      unfold cardinality
      rw [entries]
      simp [contributes,n0,n1,n2,n3,n4,walk0,walk4,
        neq 0 (by decide),neq 1 (by decide),neq 2 (by decide),neq 4 (by decide)]
    have absent : location.exposedCache.nodes.get query = none := by
      rcases chosen with rfl | rfl
      all_goals apply get_none
      all_goals change 5 ≤ query.toNat
      all_goals omega
    cases kind <;> simp only [counter,absent,Option.getD_none,counts] <;> rfl

theorem cache_cardinality : LocationCoherent tree initial {} ∧ LocationCoherent tree child.location {} ∧
    LocationCoherent tree result.location {} := by
  rw [initial_eq,child_eq,result_eq]
  exact ⟨coherent _ (.inl rfl),coherent _ (.inr rfl),coherent _ (.inr rfl)⟩

end DuplicatePrefix.S05ReservedIMPostchildrenRepaired
