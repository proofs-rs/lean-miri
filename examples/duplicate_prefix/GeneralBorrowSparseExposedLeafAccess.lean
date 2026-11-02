import duplicate_prefix.GeneralBorrowSparseExposedLeafState
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowSparseExposedLeafState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem write_profile {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree location protections) : GeneralBorrowExposedConditionalWriteState.Profile tree location protections := by
  intro index node present
  have count:=positive shape location protections raw index node present .Write
  have nonzero : GeneralBorrowExposedConditionalWriteState.zero location index=false := by
    simp [GeneralBorrowExposedConditionalWriteState.zero,Nat.ne_of_gt count]
  simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,nonzero,Bool.false_eq_true,ite_false] using raw.2 index node present

theorem read_profile {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree location protections) : GeneralBorrowExposedConditionalReadState.Readable tree location protections := by
  intro index node present
  have count:=positive shape location protections raw index node present .Read
  have nonzero : GeneralBorrowExposedConditionalReadState.zero location index=false := by
    simp [GeneralBorrowExposedConditionalReadState.zero,Nat.ne_of_gt count]
  have good:=raw.2 index node present
  change GeneralBorrowExposedConditionalReadPermissions.Condition _ _ _
  rw [GeneralBorrowExposedConditionalReadPermissions.Condition,nonzero]
  exact ⟨good.1,good.2.1⟩

def read_data {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree location protections) (root : UniIndex) (node : TreeNode) (present : tree.nodeAt root=some node) :
    GeneralBorrowExposedConditionalReadState.Data tree location root protections where
  support:=fun index=>index=root
  rooted:=rfl
  present:=by intro index same;subst index;exact ⟨node,present⟩
  children:=by intro index queried same found child member;subst index;have equal:=Option.some.inj (present.symm.trans found);subst queried;rw [(shape.nodes root node present).2.1] at member;cases member
  covers:=by intro index same;subst index;intro row member ancestor;exact ancestor
  coherent:=raw.1
  short:=shape.short
  depth:=shape.depth
  readable:=read_profile shape location protections raw

def write_data {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree location protections) (root : UniIndex) (node : TreeNode) (present : tree.nodeAt root=some node) :
    GeneralBorrowExposedConditionalWriteState.Data tree location root protections where
  support:=fun index=>index=root
  rooted:=rfl
  present:=by intro index same;subst index;exact ⟨node,present⟩
  children:=by intro index queried same found child member;subst index;have equal:=Option.some.inj (present.symm.trans found);subst queried;rw [(shape.nodes root node present).2.1] at member;cases member
  covers:=by intro index same;subst index;intro row member ancestor;exact ancestor
  coherent:=raw.1
  short:=shape.short
  depth:=shape.depth
  profile:=write_profile shape location protections raw

theorem ready {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree location protections) (kind : AccessKind) : GeneralBorrowExposedConditionalRangeData.Ready tree protections primary extras kind location := by
  have reciprocal : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree := by
    intro child node present parent edge
    rw [(shape.nodes child node present).1] at edge
    cases edge
  obtain ⟨node,present⟩:=shape.present primary (by simp)
  cases kind with
  | Read =>
    refine And.intro (shape.forest location protections) ?_
    refine And.intro ?_ ?_
    · exact ⟨{base:=read_data shape location protections raw primary node present
              graph:=reciprocal,witness:=primary,node:=node,present:=present
              exposed:=(shape.nodes primary node present).2.2
              support:=supports _ _ (raw.2 primary node present) .Read
              path:=.refl primary node present}⟩
    · intro root member
      obtain ⟨rootNode,rootPresent⟩:=shape.present root (by simp [member])
      exact ⟨read_data shape location protections raw root rootNode rootPresent⟩
  | Write =>
    refine And.intro (shape.forest location protections) ?_
    refine And.intro ?_ ?_
    · exact ⟨{base:=write_data shape location protections raw primary node present
              graph:=reciprocal,witness:=primary,node:=node,present:=present
              exposed:=(shape.nodes primary node present).2.2
              support:=supports _ _ (raw.2 primary node present) .Write
              path:=.refl primary node present}⟩
    · intro root member
      obtain ⟨rootNode,rootPresent⟩:=shape.present root (by simp [member])
      exact ⟨write_data shape location protections raw root rootNode rootPresent⟩

/-- Actual NONE Read/Write is closed on sparse exposed leaf forests. Both
explicit and vacant default permissions participate through the source's exact
effective-state rule. Read preserves the full cache; Write preserves its Write
counters. Finite cardinality and parentless source paths reconstruct reusable
scalar ownership, rather than assuming final profiles or access success. -/
theorem access {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree location protections) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange) :
    let actual:=source_tree_access_at tree location none kind protections mode range
    source_access_status actual=none ∧ Raw tree (source_access_location actual) protections := by
  have called:=GeneralBorrowExposedConditionalRangeData.location tree protections primary extras kind mode range location shape.roots (ready shape location protections raw kind)
  refine ⟨called.1,called.2.2.1,?_⟩
  intro index node present
  have initialPositive:=positive shape location protections raw index node present .Write
  have finalPositive : 0<GeneralBorrowWildcardRelatednessBounds.count
      (source_access_location (source_tree_access_at tree location none kind protections mode range)).exposedCache index .Write := by
    cases kind with
    | Read => rw [called.2.2.2.2 rfl];exact initialPositive
    | Write =>
      have same:=congrArg UInt16.toNat (called.2.2.2.1 index)
      rw [counter_count,counter_count] at same
      rw [same];exact initialPositive
  cases kind with
  | Write =>
    have good:=called.2.1 index node present
    have nonzero : GeneralBorrowExposedConditionalWriteState.zero
        (source_access_location (source_tree_access_at tree location none .Write protections mode range)) index=false := by
      simp [GeneralBorrowExposedConditionalWriteState.zero,Nat.ne_of_gt finalPositive]
    simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,nonzero,Bool.false_eq_true,ite_false] using good
  | Read =>
    have supported:=positive_support shape _ protections called.2.2.1 index node present .Write finalPositive
    have good:=called.2.1 index node present
    have possible : (GeneralBorrowWildcardVirtualLeaf.effective
        (source_access_location (source_tree_access_at tree location none .Read protections mode range)) index node).possible=true := by
      unfold GeneralBorrowExposedConditionalReadPermissions.Condition at good
      split at good <;> exact good.1
    exact local_of_support _ _ possible supported
end
end DuplicatePrefix.GeneralBorrowSparseExposedLeafAccess
