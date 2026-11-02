import duplicate_prefix.S02ConstructorOutsideGenericNormal
import duplicate_prefix.S02ConstructorCallbackForeign

namespace DuplicatePrefix.S02ConstructorOutsideGenericRow
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshGraph GeneralBorrowExposureCardinality
open DuplicatePrefixBorrowAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] UniValMap.insert

/-- Full destination Row after actual physical mutable-child attachment on a
row outside the constructor window. The source and selected root remain
arbitrary, including wildcard; every fresh-child query is derived internally. -/
theorem row (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode newNode).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth
      (attached tree index parent parentNode newNode).nodes)
    (hidden : newNode.isExposed = false) (leaf : newNode.children = #[]) (childParent : newNode.parent = some parent)
    (foreign : ∀ kind held,DuplicatePrefixScalarAuthorization.Compatible newNode.defaultLocationState kind .ForeignAccess held)
    (foreignQuery : ∀ kind held,DuplicatePrefixCallbackVisitAuthorization.Authorized newNode.defaultLocationState kind held
      (some .ForeignAccess) (some .ForeignAccess))
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (sourcePresent : ∀ anchor,source = some anchor → ∃ node,tree.nodeAt anchor = some node)
    (old : Row tree location protections source selected maximum) :
    Nonempty (Row (attached tree index parent parentNode newNode)
      location protections source selected maximum) := by
  obtain ⟨forest⟩ := formed.forest location protections
  have paths : GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree location protections).topology
      (source_normal_projection (attached tree index parent parentNode newNode) location protections).topology
      parent.toNat index.toNat := by
    rcases slot with atEnd | bounded
    · exact (S02ConstructorOutsideGenericProjection.append_extension tree index parent parentNode newNode atEnd vacant parentPresent fits childParent leaf
        location protections clean forest).paths
    · exact (S02ConstructorOutsideGenericProjection.reuse_extension tree index parent parentNode newNode bounded vacant parentPresent fits childParent leaf
        location protections clean forest).paths
  have different (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node) : query ≠ index := by
    intro same
    change tree.nodes.get query = some node at present
    rw [same,vacant] at present
    cases present
  refine ⟨{wildcard := old.wildcard,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := ?_}⟩
  · intro anchor same
    obtain ⟨node,present⟩ := sourcePresent anchor same
    have valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
      rw [S02ConstructorOutsideProjection.topology_size]
      exact (array_of_node tree anchor node present).1
    have neq : anchor.toNat ≠ index.toNat := by
      intro equal
      exact different anchor node present (GeneralBorrowNodeUpdate.index_injective anchor index equal)
    rw [paths.oldPath anchor.toNat valid neq]
    exact old.rootPath anchor same
  · intro root same
    obtain ⟨node,present⟩ := old.rootPresent root same
    exact GeneralBorrowFreshMetadataChildReuseGraph.old_present tree index parent root parentNode _ node vacant parentPresent present
  · cases selected with
    | none => exact old.cutoff
    | some root =>
      obtain ⟨node,present⟩ := old.rootPresent root rfl
      have tags := GeneralBorrowFreshReuseProtection.tags_other tree index parent root parentNode
        newNode vacant parentPresent (different root node present)
      exact old.cutoff.trans tags.symm
  · intro anchor same
    obtain ⟨node,present⟩ := sourcePresent anchor same
    obtain ⟨normal⟩ := old.normal anchor same
    exact S02ConstructorOutsideGenericNormal.normal tree index parent anchor parentNode node newNode vacant parentPresent present slot fits childParent leaf foreign
      location protections clean forest normal
  · intro position valid neq
    obtain ⟨support,read,write⟩ := old.callbacks position valid neq
    have state : (location.perms.get index).getD newNode.defaultLocationState = newNode.defaultLocationState := by rw [clean];rfl
    have extend (kind : AccessKind)
        (authorization : Authorization tree location protections tree.roots[position] position maximum kind support) :=
      S02ConstructorCallbackForeign.authorization tree depth index parent parentNode newNode
        vacant parentPresent hidden leaf childParent size nextDepth location location protections (fun _ _ _ => rfl)
        newNode.defaultLocationState state foreignQuery tree.roots[position] position maximum kind support authorization
    exact ⟨S02ConstructorSupportTopology.Extended support index parent,extend .Read read,extend .Write write⟩

/-- Allocation mapping and partition storage do not enter one fixed row's
capability or scalar/topology projection. -/
theorem context (tree : BorrowTree) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (old : Row tree location protections source selected maximum) :
    Nonempty (Row {tree with tagMapping := mapping,locations := locations} location protections source selected maximum) := by
  refine ⟨{wildcard := old.wildcard,rootPath := old.rootPath,rootPresent := old.rootPresent,cutoff := old.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro anchor same
    obtain ⟨normal⟩ := old.normal anchor same
    exact ⟨⟨normal.component,normal.permissions⟩⟩
  · intro position valid neq
    obtain ⟨support,read,write⟩ := old.callbacks position valid neq
    exact ⟨support,
    GeneralBorrowSharedCallbacksData.authorization_context tree mapping locations location protections _ _ _ _ support read,
    GeneralBorrowSharedCallbacksData.authorization_context tree mapping locations location protections _ _ _ _ support write⟩

end DuplicatePrefix.S02ConstructorOutsideGenericRow

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ConstructorOutsideGenericRow.row,``DuplicatePrefix.S02ConstructorOutsideGenericRow.context] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
