import duplicate_prefix.GeneralBorrowExposureGraphTransport
import duplicate_prefix.GeneralBorrowExposurePermissionUpdate
import duplicate_prefix.GeneralBorrowFreshModify
namespace DuplicatePrefix.GeneralBorrowExposureChildAttach
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Attaching an unexposed child preserves every old cache contribution; its
new permission is irrelevant until exposure. Sparse reused slots are allowed. -/
theorem attach (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (location : LocationTree) (protections : ProtectedTags) (initial : LocationCoherent tree location protections) :
    LocationCoherent {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} location protections := by
  have parentDifferent : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;cases parentPresent
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode parentDifferent).trans parentPresent
  let after := attachedNodes tree.nodes index parent parentNode newNode
  have oldFrame : ∀ query node,tree.nodes.get query = some node → ∃ next,after.get query = some next ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed ∧
      effective location protections query next = effective location protections query node := by
    intro query node present
    have different : query ≠ index := by intro same;rw [same,vacant] at present;cases present
    by_cases isParent : query = parent
    · subst query
      have equal : node = parentNode := Option.some.inj (present.symm.trans parentPresent)
      subst node
      exact ⟨{parentNode with children := parentNode.children.push index},
        insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ parentAfter,rfl,rfl,rfl⟩
    · refine ⟨node,?_,rfl,rfl,rfl⟩
      change ((tree.nodes.insert index newNode).insert parent _).get query = _
      rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
        GeneralBorrowFreshLocation.get_other _ index query _ different,present]
  have back : ∀ query node,after.get query = some node → node.isExposed = true → ∃ old,tree.nodes.get query = some old := by
    intro query node present exposed
    by_cases isIndex : query = index
    · subst query
      have newPresent : after.get index = some newNode := by
        change ((tree.nodes.insert index newNode).insert parent _).get index = _
        rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm parentDifferent),GeneralBorrowFreshLocation.get_same]
      have equal := Option.some.inj (newPresent.symm.trans present)
      subst node;rw [hidden] at exposed;cases exposed
    · by_cases isParent : query = parent
      · subst query;exact ⟨parentNode,parentPresent⟩
      · refine ⟨node,?_⟩
        change ((tree.nodes.insert index newNode).insert parent _).get query = some node at present
        rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
          GeneralBorrowFreshLocation.get_other _ index query _ isIndex] at present
        exact present
  intro query kind
  rw [initial query kind]
  exact congrArg UInt16.ofNat (GeneralBorrowExposureGraphTransport.extension tree.nodes after depth _ _ size oldFrame back query kind).symm

/-- Actual bounded range modification preserves any per-value invariant whose
pure callback preserves it. Preparation and modifier execution are derived. -/
theorem modify_every {α : Type} [DecidableEq α] (predicate : α → Prop) (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α) (well : map.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (initial : Every predicate map) (step : ∀ range value,predicate value → predicate (modify range value)) :
    Every predicate (map.modifyRange offset len modify).state := by
  have prepared := GeneralRangeMapSafety.iter_mut predicate map offset len well initial bounds
  rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds]
  have fold : ∀ (positions : List Nat) (current : DedupRangeMap α),Every predicate current →
      Every predicate (positions.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position modify) current) := by
    intro positions
    induction positions with
    | nil => intro current good;exact good
    | cons position rest ih =>
      intro current good
      apply ih
      dsimp only [GeneralBorrowFreshModify.atPosition]
      split
      · rename_i valid
        exact replaced_every predicate current position valid _ good (step _ _ (good position valid))
      · exact good
  exact fold _ _ prepared.every

/-- Installing a stored permission at an actual unexposed child performs no
cache update and preserves the generic count invariant. -/
theorem materialize (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) (hidden : node.isExposed = false)
    (location : LocationTree) (protections : ProtectedTags) (state : LocationState)
    (initial : LocationCoherent tree location protections) :
    LocationCoherent tree {location with perms := location.perms.insert index state} protections := by
  have good := (GeneralBorrowExposurePermissionUpdate.preserves tree location protections depth initial index node present state).2
  simpa only [GeneralBorrowExposurePermissionUpdate.nextLocation,GeneralBorrowExposurePermissionUpdate.cacheUpdate,
    GeneralBorrowExposureLevelTransition.operation,hidden,Bool.false_eq_true,↓reduceIte] using good

end DuplicatePrefix.GeneralBorrowExposureChildAttach
