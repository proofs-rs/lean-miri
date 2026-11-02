import duplicate_prefix.S05NoCutoffOwnershipBridge
import duplicate_prefix.GeneralBorrowSifaPermissionConsistency

namespace DuplicatePrefix.S05CutoffOwnershipCacheGap
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def cutoff : BorTag := ⟨10,by decide⟩
def oldTag : BorTag := ⟨1,by decide⟩
def youngTag : BorTag := ⟨11,by decide⟩
def selectedNode : TreeNode := ⟨cutoff,none,#[],.Disabled,.None,false,none⟩
def rootNode : TreeNode := ⟨oldTag,none,#[ix 2],.Cell,.Write,false,none⟩
def childNode : TreeNode := ⟨youngTag,some (ix 1),#[],.Unique,.None,true,none⟩
def location : LocationTree := {
  perms := ⟨#[none,none,some ⟨.Unique,true,.None⟩]⟩
  exposedCache := ⟨⟨#[none,some ⟨1,1⟩,some ⟨1,1⟩]⟩⟩ }
def tree : BorrowTree :=
  ⟨⟨#[(cutoff,ix 0),(oldTag,ix 1),(youngTag,ix 2)],#[]⟩,
    ⟨#[some selectedNode,some rootNode,some childNode]⟩,
    RangeMapNonempty.homogeneous 1 location,#[ix 0,ix 1]⟩
def area (query : UniIndex) : Prop := query = ix 1 ∨ query = ix 2

private theorem support_node (query : UniIndex) (node : TreeNode)
    (inside : area query) (present : tree.nodes.get query = some node) :
    (query = ix 1 ∧ node = rootNode) ∨ (query = ix 2 ∧ node = childNode) := by
  rcases inside with same | same
  · subst query
    have equal : node = rootNode := Option.some.inj present.symm
    exact Or.inl ⟨rfl,equal⟩
  · subst query
    have equal : node = childNode := Option.some.inj present.symm
    exact Or.inr ⟨rfl,equal⟩

/-- The independent no-cutoff graph/permission/activity ownership packet is
satisfied. This finite snapshot is not asserted reachable from valid Rust. -/
theorem ownership : Nonempty (S05NoCutoffOwnershipBridge.Ownership tree location {} (ix 1) 1) := by
  refine ⟨⟨⟨area,Or.inl rfl,?_,?_⟩,?_,?_,?_,?_⟩⟩
  · intro query inside
    rcases inside with rfl | rfl <;> exact ⟨_,rfl⟩
  · intro query node inside present child member
    rcases support_node query node inside present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have same : child = ix 2 := by simpa [rootNode] using member
      exact Or.inr same
    · simp only [childNode,Array.toList_empty,List.not_mem_nil] at member
  · intro query inside
    rcases inside with rfl | rfl
    all_goals
      intro row member walked
      have entries : tree.nodes.entries.toList = [(ix 0,selectedNode),(ix 1,rootNode),(ix 2,childNode)] := by with_unfolding_all rfl
      rw [entries] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals first | contradiction | exact (by decide) | exact False.elim (by have impossible : ¬_ := by decide;exact impossible walked)
  · intro query node inside present kind
    rcases support_node query node inside present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · change DuplicatePrefixScalarAuthorization.Compatible ⟨.Cell,false,.Write⟩ kind .ForeignAccess false
      cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]
    · change DuplicatePrefixScalarAuthorization.Compatible ⟨.Unique,true,.None⟩ kind .ForeignAccess false
      cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]
  · intro query node inside present witness witnessNode found exposed walked kind supports
    rcases support_node query node inside present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · change DuplicatePrefixScalarAuthorization.Compatible ⟨.Cell,false,.Write⟩ kind .LocalAccess false
      cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]
    · change DuplicatePrefixScalarAuthorization.Compatible ⟨.Unique,true,.None⟩ kind .LocalAccess false
      cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

  · intro impossible;cases impossible

/-- Removing the exposed Unique child is a legal conservative Write mask. -/
theorem legal_child : Removal tree location {} (some cutoff) .Write [ix 2] := by
  refine ⟨by decide,?_⟩
  intro query member
  have same : query = ix 2 := by simpa only [List.mem_singleton] using member
  subst query
  exact ⟨childNode,rfl,by decide +kernel⟩

/-- The same snapshot's cache permits Either on entry but produces a forbidden
new Foreign skip at exit. Thus the no-cutoff ownership packet alone cannot
justify concrete/some-cutoff residual-pair authorization. -/
theorem not_authorized : ¬ Authorization tree location {} (ix 1) 1 (some cutoff) .Write area := by
  intro authorized
  have pair := authorized.queries [] [ix 2] (empty_removal tree location {} (some cutoff) .Write)
    legal_child (by simp) (ix 1) rootNode (Or.inl rfl) rfl (by decide)
  have impossible : ¬ DuplicatePrefixCallbackVisitAuthorization.Authorized
      ((location.perms.get (ix 1)).getD rootNode.defaultLocationState) .Write false
      (residualRelation tree location {} (ix 1) (ix 1) rootNode (some cutoff) .Write 1 [])
      (residualRelation tree location {} (ix 1) (ix 1) rootNode (some cutoff) .Write 1 [ix 2]) := by
    have before : residualRelation tree location {} (ix 1) (ix 1) rootNode (some cutoff) .Write 1 [] = some .EitherAccess := by
      with_unfolding_all rfl
    have after : residualRelation tree location {} (ix 1) (ix 1) rootNode (some cutoff) .Write 1 [ix 2] = some .ForeignAccess := by
      with_unfolding_all rfl
    rw [before,after]
    change ¬ DuplicatePrefixCallbackVisitAuthorization.Authorized ⟨.Cell,false,.Write⟩ .Write false (some .EitherAccess) (some .ForeignAccess)
    simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,
      IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
      IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,AccessRelatedness.isForeign]
  exact impossible pair

/-- Every scalar cache individually respects its permission. The missing
condition concerns cache ordering between ancestors and descendants. -/
theorem scalar_consistency :
    GeneralBorrowSifaPermissionConsistency.Consistent rootNode.defaultLocationState false ∧
    GeneralBorrowSifaPermissionConsistency.Consistent ⟨.Unique,true,.None⟩ false := by
  exact ⟨⟨.Write,rfl,by decide⟩,⟨.None,rfl,by decide⟩⟩

end DuplicatePrefix.S05CutoffOwnershipCacheGap
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05CutoffOwnershipCacheGap.ownership,
      ``DuplicatePrefix.S05CutoffOwnershipCacheGap.legal_child,
      ``DuplicatePrefix.S05CutoffOwnershipCacheGap.not_authorized,
      ``DuplicatePrefix.S05CutoffOwnershipCacheGap.scalar_consistency] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
