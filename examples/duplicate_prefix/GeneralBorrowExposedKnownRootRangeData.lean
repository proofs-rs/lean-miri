import duplicate_prefix.GeneralBorrowExposedKnownRootAccess
import duplicate_prefix.GeneralBorrowExposedKnownRootWriteAccess
namespace DuplicatePrefix.GeneralBorrowExposedKnownRootRangeData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

set_option autoImplicit false in
structure Context (tree : BorrowTree) (anchor selected head : UniIndex) (tail : List UniIndex) where
  anchorNode : TreeNode
  selectedNode : TreeNode
  anchorPresent : tree.nodeAt anchor = some anchorNode
  selectedPresent : tree.nodes.get selected = some selectedNode
  roots : tree.roots = (head::tail).toArray
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  tags : ∀ index node,area.support index → tree.nodes.get index = some node → node.tag.value ≤ selectedNode.tag.value

def Profile (kind : AccessKind) (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  match kind with
  | .Read => GeneralBorrowExposedKnownRootState.Readable tree location protections
  | .Write => GeneralBorrowExposedKnownRootWriteState.Profile tree location protections

def Primary (kind : AccessKind) (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (protections : ProtectedTags) : Type :=
  match kind with
  | .Read => GeneralBorrowExposedKnownRootPrimaryWitness.Data tree location root protections
  | .Write => GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree location root protections

def Virtual (kind : AccessKind) (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (protections : ProtectedTags) : Type :=
  match kind with
  | .Read => GeneralBorrowExposedKnownRootState.Data tree location root protections
  | .Write => GeneralBorrowExposedKnownRootWriteState.Data tree location root protections

set_option autoImplicit false in
/-- Initial records for one location of either access kind. The owner
component is hidden; arbitrary exposed other components carry kind-specific
conditional raw profiles, without a callback or operation-success field. -/
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (kind : AccessKind) where
  forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology
  component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat
  owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component
  rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat
  hidden : ∀ index node,component.support index.toNat → tree.nodeAt index = some node → node.isExposed = false
  separate : ∀ index,area.support index → ¬component.support index.toNat
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections
  profile : Profile kind tree location protections
  primary : head ≠ selected → Primary kind tree location head protections
  virtual : ∀ root ∈ tail,root ≠ selected → Virtual kind tree location root protections

def Post (kind : AccessKind) (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧ Profile kind tree location protections

theorem initial {tree location protections anchor selected head tail kind}
    (data : Data tree location protections anchor selected head tail kind) : Post kind tree location protections :=
  ⟨data.coherent,data.profile⟩

/-- Dispatch both real concrete Read/Write location operations from initial
component records. The selected component may be in any root-array position. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor selected head tail)
    (data : Data tree location protections anchor selected head tail kind) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none ∧
      Post kind tree (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range)) protections := by
  cases kind with
  | Read =>
    obtain ⟨after,actual,status,frame,profile,coherent⟩ := GeneralBorrowExposedKnownRootAccess.access tree location protections
      anchor selected head context.anchorNode context.selectedNode tail mode range context.roots data.forest data.component data.owned context.depth context.children
      context.anchorPresent context.selectedPresent data.rootPath data.hidden data.separate data.coherent data.profile context.tags data.primary data.virtual
    refine ⟨status,?_⟩
    rw [actual]
    exact ⟨coherent,profile⟩
  | Write =>
    obtain ⟨after,actual,status,frame,profile,coherent⟩ := GeneralBorrowExposedKnownRootWriteAccess.access tree location protections
      anchor selected head context.anchorNode context.selectedNode tail mode range context.roots data.forest data.component data.owned context.depth context.children
      context.anchorPresent context.selectedPresent data.rootPath data.hidden data.separate data.coherent data.profile context.tags data.primary data.virtual
    refine ⟨status,?_⟩
    rw [actual]
    exact ⟨coherent,profile⟩
theorem post_map (kind : AccessKind) (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags) :
    Post kind {tree with locations := map} location protections = Post kind tree location protections := by
  cases kind <;> rfl

end DuplicatePrefix.GeneralBorrowExposedKnownRootRangeData
