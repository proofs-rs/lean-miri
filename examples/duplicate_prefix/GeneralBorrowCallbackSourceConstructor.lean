import duplicate_prefix.GeneralBorrowSharedCallbacksSifa
import duplicate_prefix.GeneralBorrowCallbackSourceRange
import duplicate_prefix.GeneralBorrowSharedConstructorRuntime

namespace DuplicatePrefix.GeneralBorrowCallbackSourceConstructor
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowNodeUpdate GeneralRangeMapOrigins GeneralBorrowFreshAnchor
open GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

theorem staged (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode) (state : LocationState) (strongest : IdempotentForeignAccess)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode newNode))
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags) (selected : UniIndex) (maximum : Option BorTag)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (fun location => Nonempty (GeneralBorrowCallbackSource.Source tree location protections parent selected maximum)) offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len (fun _ location => GeneralBorrowFreshMaterialization.materialized location index state)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping changed.state
    let after := (sourceUpdateSifa stage parent strongest).1
    OwnedOn (Callbacks after protections selected maximum) offset.bytes (offset.bytes+len.bytes) after.locations := by
  dsimp only
  let changed := tree.locations.modifyRange offset len (fun _ location => GeneralBorrowFreshMaterialization.materialized location index state)
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping changed.state
  have initial := GeneralBorrowCallbackSourceRange.ranged tree formed depth index parent parentNode newNode state
    vacant parentPresent hidden size nextDepth mapping protections selected maximum offset len well bounds owned
  have different : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;cases parentPresent
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent _ different).trans parentPresent
  have stagePresent : stage.nodes.get parent = some {parentNode with children := parentNode.children.push index} :=
    insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ parentAfter
  exact GeneralBorrowSharedCallbacksSifa.owned stage nextDepth parent _ stagePresent strongest protections selected maximum
    offset.bytes (offset.bytes+len.bytes) initial

end DuplicatePrefix.GeneralBorrowCallbackSourceConstructor
