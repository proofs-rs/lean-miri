import duplicate_prefix.GeneralBorrowGcDfsIncoming
import duplicate_prefix.GeneralBorrowCanonicalParentDepth

namespace DuplicatePrefix.GeneralBorrowGcDfsGraphRestoration
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Full reciprocal SOURCE graph data, including present parent endpoints,
actual child endpoints, unique outgoing edges, and strict parent ranks. -/
structure Graph (rank : UniIndex → Nat) (tree : BorrowTree) : Prop where
  parents : ∀ child node, tree.nodes.get child = some node → ∀ parent, node.parent = some parent →
    ∃ parentNode, tree.nodes.get parent = some parentNode ∧ child ∈ parentNode.children.toList ∧ rank parent < rank child
  children : ∀ parent node, tree.nodes.get parent = some node → ∀ child ∈ node.children.toList,
    ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some parent
  distinct : ∀ parent node, tree.nodes.get parent = some node → node.children.toList.Nodup

/-- Staged data restore full reciprocal graph data at every real postvisit
boundary. Completed parents use repaired incoming/outgoing edges. Pending
parents use untouched original metadata and genuine pending-child survival.
No requirement that all nodes are processed, or final Forest premise, is used. -/
theorem restore (rank : UniIndex → Nat) (original tree : BorrowTree) (processed : List UniIndex)
    (metadata : GeneralBorrowGcDfsReadyPlan.Metadata original) (backlinks : Backlinks original)
    (stage : Stage original processed tree) (ranked : Ranked rank tree)
    (pending : Pending original processed tree)
    (repaired : GeneralBorrowGcDfsReciprocalStage.Reciprocal processed tree)
    (incoming : Incoming original processed tree) : Graph rank tree := by
  constructor
  · intro child node present parent edge
    have parentData : ∃ parentNode, tree.nodes.get parent = some parentNode ∧ child ∈ parentNode.children.toList := by
      by_cases completed : parent ∈ processed
      · exact incoming.completed child node present parent edge completed
      · obtain ⟨originalNode,originalPresent,originalEdge⟩ := incoming.unprocessed child node present parent edge completed
        obtain ⟨parentNode,parentPresent,member⟩ := backlinks child originalNode originalPresent parent originalEdge
        exact ⟨parentNode,(stage.outside parent completed).trans parentPresent,member⟩
    obtain ⟨parentNode,parentPresent,member⟩ := parentData
    exact ⟨parentNode,parentPresent,member,ranked parent parentNode parentPresent child member⟩
  · intro parent node present child member
    by_cases completed : parent ∈ processed
    · exact repaired.children parent completed node present child member
    · have originalPresent := (stage.outside parent completed).symm.trans present
      obtain ⟨originalChild,childPresent,childEdge⟩ := metadata.children parent node originalPresent child member
      obtain ⟨current,currentPresent,parentEq,_⟩ := pending child originalChild childPresent (.inr ⟨parent,childEdge,completed⟩)
      exact ⟨current,currentPresent,parentEq.trans childEdge⟩
  · intro parent node present
    by_cases completed : parent ∈ processed
    · exact repaired.distinct parent completed node present
    · exact metadata.distinct parent node ((stage.outside parent completed).symm.trans present)

/-- Recompute bounded ParentDepth from the actual surviving sparse graph. Only
proof ranks are compressed; interpreter nodes and metadata are untouched. -/
def depth (rank : UniIndex → Nat) (tree : BorrowTree) (graph : Graph rank tree) : GeneralBorrowExposure.ParentDepth tree.nodes where
  depth := fun index => (GeneralBorrowCanonicalParentDepth.lower tree.nodes rank index).length
  bounded := fun index node present => Nat.le_of_lt (GeneralBorrowCanonicalParentDepth.strict tree.nodes rank index node present)
  parent := by
    intro child node present parent edge
    obtain ⟨parentNode,parentPresent,_,strict⟩ := graph.parents child node present parent edge
    exact ⟨parentNode,parentPresent,GeneralBorrowCanonicalParentDepth.edge tree.nodes rank parent child parentNode parentPresent strict⟩

end DuplicatePrefix.GeneralBorrowGcDfsGraphRestoration
