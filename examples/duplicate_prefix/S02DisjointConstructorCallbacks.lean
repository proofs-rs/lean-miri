import duplicate_prefix.S02ConstructorCallbackExtension
import duplicate_prefix.S02DisjointConstructorMap
import duplicate_prefix.GeneralBorrowGcVacantClean

namespace DuplicatePrefix.S02DisjointConstructorCallbacks
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralRangeMapOrigins
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 700000
attribute [local irreducible] UniValMap.insert

/-- Real disjoint mutable materialization and physical child attachment preserve
all destination callbacks. The destination's source and selected root are
arbitrary, including wildcard; neither must equal the constructor parent.
The fresh scalar obligation is derived from vacant-slot cleanliness and the
actual mutable child's defaults, rather than supplied by the caller. -/
theorem owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth
      (attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)).nodes)
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len : Size) (lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.bytes.toNat+len.bytes.toNat ≤ lower.toNat ∨ upper.toNat ≤ offset.bytes.toNat)
    (old : OwnedOn (fun location => Nonempty
      (DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum)) lower upper tree.locations) :
    let changed := tree.locations.modifyRange offset len (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
      (GeneralBorrowFreshChild.child newTag parent) mapping changed.state
    OwnedOn (fun location => ∀ position,(valid : position < stage.roots.size) →
      selected ≠ some stage.roots[position] → ∃ support,
        Authorization stage location protections stage.roots[position] position maximum .Read support ∧
        Authorization stage location protections stage.roots[position] position maximum .Write support)
      lower upper changed.state := by
  let predicate (location : LocationTree) := Nonempty
    (DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum) ∧
      location.perms.get index = none
  have paired : OwnedOn predicate lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨old position valid positive start stop,clean index vacant position valid⟩
  have preserved := S02DisjointConstructorMap.mutable_materialized tree.locations offset len index predicate lower upper
    well bounds outside paired
  dsimp only
  intro position valid positive start stop rootPosition rootValid different
  obtain ⟨⟨row⟩,vacantSlot⟩ := preserved position valid positive start stop
  obtain ⟨support,read,write⟩ := row.callbacks rootPosition rootValid different
  have freshState :
      (((tree.locations.modifyRange offset len (fun _ location => GeneralBorrowFreshMaterialization.materialized
        location index GeneralBorrowFreshChild.inside)).state.entries[position]'valid).data.perms.get index).getD
          (GeneralBorrowFreshChild.child newTag parent).defaultLocationState = ⟨.ReservedFrz false,false,.None⟩ := by
    rw [vacantSlot]
    rfl
  have extend (kind : AccessKind)
      (authorization : Authorization tree _ protections tree.roots[rootPosition] rootPosition maximum kind support) :=
    S02ConstructorCallbackExtension.authorization tree depth index parent parentNode (GeneralBorrowFreshChild.child newTag parent)
      vacant parentPresent rfl rfl rfl size nextDepth _ _ protections (fun _ _ _ => rfl) freshState
      tree.roots[rootPosition] rootPosition maximum kind support authorization
  refine ⟨S02ConstructorSupportTopology.Extended support index parent,?_,?_⟩
  · exact GeneralBorrowSharedCallbacksData.authorization_context _ mapping _ _ protections _ _ _ _ _ (extend .Read read)
  · exact GeneralBorrowSharedCallbacksData.authorization_context _ mapping _ _ protections _ _ _ _ _ (extend .Write write)

end DuplicatePrefix.S02DisjointConstructorCallbacks

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointConstructorCallbacks.owned) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
