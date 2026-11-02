import duplicate_prefix.S04ZeroSifaEffectiveFrame
import duplicate_prefix.S04ZeroSifaAuthorization
import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry

namespace DuplicatePrefix.S04ZeroSifaCallbacks
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralBorrowSifa GeneralBorrowExposureCardinality
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowSharedAuthorizationGeometry
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- Actual protected-constructor SIFA weakening preserves a complete callback
component even when that component contains the constructor parent/ancestors.
Unlike an outside-component frame, scalar consistency and the raw universal
query authorization justify the reset branches. No success is assumed. -/
theorem at_row (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (protections : ProtectedTags) (position : Nat) (valid : position < tree.locations.entries.size)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree (tree.locations.entries[position]'valid).data protections)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop)
    (old : Authorization tree (tree.locations.entries[position]'valid).data protections root rootPosition maximum kind support) :
    let after := (sourceUpdateSifa tree start .None).1
    ∃ nextValid : position < after.locations.entries.size,
      Authorization after (after.locations.entries[position]'nextValid).data protections root rootPosition maximum kind support := by
  let after := (sourceUpdateSifa tree start .None).1
  let beforeLocation := (tree.locations.entries[position]'valid).data
  have shape := GeneralBorrowSifaView.preserves tree start .None
  have ranges := congrArg (fun value => value.2.2.1) shape
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have sizes := congrArg Array.size ranges
  simp only [Array.size_map] at sizes
  have nextValid : position < after.locations.entries.size := by omega
  let afterLocation := (after.locations.entries[position]'nextValid).data
  have point := congrArg (fun rows => rows[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem nextValid,Option.map_some] at point
  have locations : locationShape afterLocation = locationShape beforeLocation := congrArg Prod.snd (Option.some.inj point)
  let nextDepth := GeneralBorrowFreshMetadata.parent_depth tree after shape depth
  have size : tree.nodes.size ≤ after.nodes.size := by
    rw [GeneralBorrowFreshMetadata.node_size tree after shape]
    exact Nat.le_refl _
  have metadata (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node) :=
    GeneralBorrowFreshMetadataChildSifa.node_fields tree start .None query node present
  have oldStates (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node)
      (next : TreeNode) (found : after.nodes.get query = some next) :
      ((afterLocation.perms.get query).getD next.defaultLocationState) = ((beforeLocation.perms.get query).getD node.defaultLocationState) ∨
      ((afterLocation.perms.get query).getD next.defaultLocationState) = {((beforeLocation.perms.get query).getD node.defaultLocationState) with idempotentForeignAccess := .None} := by
    obtain ⟨actual,lookup,tag,heldValid,states⟩ := S04ZeroSifaEffectiveFrame.effective tree start query node present position valid
    have same := Option.some.inj (found.symm.trans lookup)
    subst actual
    exact states
  have levels (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node)
      (next : TreeNode) (found : after.nodes.get query = some next) (tag : next.tag = node.tag) :
      effective afterLocation protections query next = effective beforeLocation protections query node := by
    obtain same | reset := oldStates query node present next found
    · simp only [effective,same,tag]
    · simp only [effective,reset,tag]
  have count (removed : List UniIndex) (query : UniIndex) :
      residualCount after afterLocation protections kind removed query = residualCount tree beforeLocation protections kind removed query := by
    apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension tree after beforeLocation afterLocation protections depth size _ _ removed query kind
    · intro query node present
      obtain ⟨next,found,tag,parent,children,permission,exposed⟩ := metadata query node present
      exact ⟨next,found,parent,exposed,levels query node present next found tag⟩
    · intro query next found exposed
      obtain ⟨node,present,rest⟩ := GeneralBorrowFreshMetadata.node_fields after tree shape.symm query next found
      exact ⟨node,present⟩
  have removal (removed : List UniIndex) (legal : Removal after afterLocation protections maximum kind removed) :
      Removal tree beforeLocation protections maximum kind removed := by
    refine ⟨legal.distinct,?_⟩
    intro query member
    obtain ⟨next,found,allowed⟩ := legal.allowed query member
    obtain ⟨node,present,rest⟩ := GeneralBorrowFreshMetadata.node_fields after tree shape.symm query next found
    obtain ⟨actual,lookup,tag,parent,children,permission,exposed⟩ := metadata query node present
    have same := Option.some.inj (found.symm.trans lookup)
    subst actual
    refine ⟨node,present,?_⟩
    have scalar := oldStates query node present next found
    rcases scalar with scalar | scalar <;>
      simpa only [removable,effective,aboveMaximum,scalar,tag,exposed] using allowed
  refine ⟨nextValid,?_⟩
  change Authorization after afterLocation protections root rootPosition maximum kind support
  refine ⟨old.rooted,?_,?_,?_,?_,?_,?_⟩
  · intro query inside
    obtain ⟨node,present⟩ := old.present query inside
    obtain ⟨next,found,rest⟩ := metadata query node present
    exact ⟨next,found⟩
  · intro query next inside found child member
    obtain ⟨node,present⟩ := old.present query inside
    obtain ⟨actual,lookup,tag,parent,children,permission,exposed⟩ := metadata query node present
    have same := Option.some.inj (found.symm.trans lookup)
    subst actual
    rw [children] at member
    exact old.children query node inside present child member
  · intro query inside
    obtain ⟨node,present⟩ := old.present query inside
    apply covers_of_path after nextDepth root query
    apply path_extension tree after _ root query
      (GeneralBorrowWildcardControlWitness.path_of_covers tree depth root query node present (old.covers query inside))
    intro index value present
    obtain ⟨next,found,tag,parent,rest⟩ := metadata index value present
    exact ⟨next,found,parent⟩
  · intro query next inside found
    obtain ⟨node,present⟩ := old.present query inside
    have possible := old.possible query node inside present
    rcases oldStates query node present next found with same | reset
    · simpa only [same] using possible
    · simpa only [reset,LocationState.possible] using possible
  · intro entry exit legalEntry legalExit subset query next inside found retained
    obtain ⟨node,present⟩ := old.present query inside
    obtain ⟨actual,lookup,tag,parent,children,permission,exposed⟩ := metadata query node present
    have same := Option.some.inj (found.symm.trans lookup)
    subst actual
    have beforeLegal := removal entry legalEntry
    have afterLegal := removal exit legalExit
    have authorized := old.queries entry exit beforeLegal afterLegal subset query node inside present retained
    simp only [residualRelation,count,aboveMaximum,tag]
    rcases oldStates query node present next found with equal | reset
    · simpa only [equal,residualRelation,aboveMaximum,beforeLocation] using authorized
    · rw [reset]
      exact S04ZeroSifaAuthorization.reset_query tree beforeLocation protections root rootPosition maximum kind support old
        entry exit beforeLegal afterLegal subset query node inside present retained (profile.present query node present)
  · intro primary
    obtain ⟨query,node,inside,present,eligible⟩ := old.witness primary
    obtain ⟨next,found,tag,parent,children,permission,exposed⟩ := metadata query node present
    refine ⟨query,next,inside,found,?_⟩
    have same := levels query node present next found tag
    refine ⟨exposed.trans eligible.1,?_,?_⟩
    · change (effective afterLocation protections query next).allows kind = true
      rw [same]
      exact eligible.2.1
    · simpa only [tag] using eligible.2.2

end DuplicatePrefix.S04ZeroSifaCallbacks
