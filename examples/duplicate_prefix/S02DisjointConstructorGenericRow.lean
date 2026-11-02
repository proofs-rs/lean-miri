import duplicate_prefix.S02ConstructorOutsideGenericRow
import duplicate_prefix.S02DisjointConstructorMap
import duplicate_prefix.GeneralBorrowGcVacantClean

namespace DuplicatePrefix.S02DisjointConstructorGenericRow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralRangeMapOrigins DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 700000
attribute [local irreducible] UniValMap.insert

/-- The full destination Row survives actual disjoint mutable materialization
and physical attachment, for arbitrary concrete/wildcard source and selected
root. The result is the exact pre-SIFA stage of the mutable constructor. -/
theorem owned (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode) (inside : LocationState)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode newNode).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth
      (attached tree index parent parentNode newNode).nodes)
    (hidden : newNode.isExposed = false) (leaf : newNode.children = #[]) (childParent : newNode.parent = some parent)
    (foreign : ∀ kind held,DuplicatePrefixScalarAuthorization.Compatible newNode.defaultLocationState kind .ForeignAccess held)
    (foreignQuery : ∀ kind held,DuplicatePrefixCallbackVisitAuthorization.Authorized newNode.defaultLocationState kind held
      (some .ForeignAccess) (some .ForeignAccess))
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (sourcePresent : ∀ anchor,source = some anchor → ∃ node,tree.nodeAt anchor = some node)
    (offset len : Size) (lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.bytes.toNat+len.bytes.toNat ≤ lower.toNat ∨ upper.toNat ≤ offset.bytes.toNat)
    (old : OwnedOn (fun location => Nonempty (Row tree location protections source selected maximum)) lower upper tree.locations) :
    let changed := tree.locations.modifyRange offset len (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index inside)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
      newNode mapping changed.state
    OwnedOn (fun location => Nonempty (Row stage location protections source selected maximum)) lower upper changed.state := by
  let predicate (location : LocationTree) := Nonempty (Row tree location protections source selected maximum) ∧
      location.perms.get index = none
  have paired : OwnedOn predicate lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨old position valid positive start stop,clean index vacant position valid⟩
  have preserved := S02DisjointConstructorMap.modify_outside tree.locations offset len
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location index inside)
    predicate lower upper well bounds outside paired
  dsimp only
  intro position valid positive start stop
  obtain ⟨⟨oldRow⟩,vacantSlot⟩ := preserved position valid positive start stop
  obtain ⟨row⟩ := S02ConstructorOutsideGenericRow.row tree formed depth index parent parentNode newNode vacant parentPresent slot fits
    size nextDepth hidden leaf childParent foreign foreignQuery _ protections vacantSlot source selected maximum sourcePresent oldRow
  exact S02ConstructorOutsideGenericRow.context _ mapping _ _ protections source selected maximum row

end DuplicatePrefix.S02DisjointConstructorGenericRow

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointConstructorGenericRow.owned) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
