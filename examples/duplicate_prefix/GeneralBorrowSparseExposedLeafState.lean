import duplicate_prefix.GeneralBorrowExposedConditionalRangeData
import duplicate_prefix.GeneralBorrowStructuralHistoryState
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafState
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Static leaf-forest metadata, independent of byte partitions and permissions. -/
structure Geometry (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex) where
  roots : tree.roots=(primary::extras).toArray
  forest : ∀location protections,Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  short : tree.nodes.size<65536
  nodes : ∀index node,tree.nodeAt index=some node→node.parent=none ∧ node.children=#[] ∧ node.isExposed=true
  present : ∀root∈primary::extras,∃node,tree.nodeAt root=some node

/-- Effective scalar permissions may be explicitly stored or lazy defaults.
No stored-row, exact counter, visited outcome or callback profile is assumed. -/
def Raw (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧
  ∀index node,tree.nodeAt index=some node→GeneralBorrowExposedConditionalWritePermissions.Compatible
    (GeneralBorrowWildcardVirtualLeaf.effective location index node) .LocalAccess (protections.contains node.tag)

def Geometry.of_graph (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree) (roots : tree.roots=(primary::extras).toArray)
    (short : tree.nodes.size<65536)
    (nodes : ∀index node,tree.nodeAt index=some node→node.parent=none ∧ node.children=#[] ∧ node.isExposed=true) : Geometry tree primary extras :=
  ⟨roots,graph.forest,Classical.choice graph.depth,short,nodes,by
    intro root member
    obtain ⟨node,present,parent⟩:=graph.rootNodes root (by rw [roots];simpa using member)
    exact ⟨node,present⟩⟩

theorem supports (state : LocationState) (held : Bool)
    (good : GeneralBorrowExposedConditionalWritePermissions.Compatible state .LocalAccess held) (kind : AccessKind) :
    GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) kind=true := by
  have allows:=GeneralBorrowExposedConditionalWritePermissions.local_allows state held good
  cases kind <;> cases level : state.permission.strongestAllowedLocalAccess held <;>
    simp_all [GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead,
      GeneralBorrowExposureAncestorFold.supportsWrite,WildcardAccessLevel.allows]

theorem local_of_support (state : LocationState) (held : Bool) (possible : state.possible=true)
    (supported : GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Write=true) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible state .LocalAccess held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases held <;> simp_all [GeneralBorrowExposedConditionalWritePermissions.Compatible,
      GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsWrite,Permission.strongestAllowedLocalAccess]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> simp_all [GeneralBorrowExposedConditionalWritePermissions.Compatible,
      GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsWrite,Permission.strongestAllowedLocalAccess]

theorem counter_count (cache : ExposedCache) (index : UniIndex) (kind : AccessKind) :
    (GeneralBorrowExposureCardinality.counter cache index kind).toNat=GeneralBorrowWildcardRelatednessBounds.count cache index kind := by
  cases kind <;> rfl

theorem positive {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree location protections) (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index=some node) (kind : AccessKind) :
    0<GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index kind := by
  have actual:=GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes (GeneralBorrowExposureCardinality.effective location protections)
    raw.1 shape.short index node present (shape.nodes index node present).2.2 kind (supports _ _ (raw.2 index node present) kind)
  rw [counter_count] at actual
  exact actual

/-- A parentless forest's positive coherent counter must be supported by that
same physical node. Nat cardinalities are recovered before finite-width reasoning. -/
theorem positive_support {tree primary extras} (shape : Geometry tree primary extras) (location : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index=some node) (kind : AccessKind)
    (count : 0<GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index kind) :
    GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) kind=true := by
  have exactCount:=GeneralBorrowExposureCardinality.nat_exact location.exposedCache tree.nodes (GeneralBorrowExposureCardinality.effective location protections)
    coherent shape.short index kind
  rw [counter_count] at exactCount
  rw [exactCount] at count
  obtain ⟨row,member⟩:=List.exists_mem_of_length_pos count
  obtain ⟨entry,qualified⟩:=List.mem_filter.mp member
  have found : tree.nodeAt row.1=some row.2 := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp entry
  have get : tree.nodes.get row.1=some row.2:=found
  have parent:=(shape.nodes row.1 row.2 found).1
  simp only [GeneralBorrowExposureCardinality.contributes,Bool.and_eq_true] at qualified
  have walked : GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) row.1=[row.1] := by
    simp only [GeneralBorrowExposureAncestorFold.walk,get,parent]
  have equal : index=row.1 := by simpa only [walked,List.contains_cons,List.contains_nil,Bool.or_false,beq_iff_eq] using qualified.2
  subst index
  have same : row.2=node:=Option.some.inj (found.symm.trans present)
  subst node
  exact qualified.1.2

end
end DuplicatePrefix.GeneralBorrowSparseExposedLeafState
