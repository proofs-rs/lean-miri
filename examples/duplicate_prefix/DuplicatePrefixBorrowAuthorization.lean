import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.DuplicatePrefixResidualSupportAuthorization

namespace DuplicatePrefix.DuplicatePrefixBorrowAuthorization
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection

set_option autoImplicit false in
/-- Exact scalar Read and Write capabilities inside the concrete source
component. Unlike a global Unique/Disabled profile, permissions elsewhere are
unconstrained by this normal-phase field. This is initial data, not an access
outcome or a post-constructor certificate. -/
structure Normal (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (source : UniIndex) where
  component : GeneralBorrowExposedScopedNormal.Component
    (source_normal_projection tree default protections).topology source.toNat
  permissions : ∀ kind index, component.support index → index < tree.nodes.data.size →
    ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
      DuplicatePrefixScalarAuthorization.Compatible state kind
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index)

set_option autoImplicit false in
/-- Candidate whole-row borrow capability: concrete normal component, then
each other physical root's callback; wildcard input has callbacks on all roots.
Both access kinds are authorized independently of duplicate_prefix's count.
The selected ROOT determines the tag cutoff. The residual callback policy is
conservative: equivalence with every ordinary valid mutable reference and its
preservation through the real call are not claimed by defining this record. -/
structure Row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) where
  wildcard : source = none → selectedRoot = none
  rootPath : ∀ anchor, source = some anchor →
    ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
      selectedRoot.map UniIndex.toNat
  rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node
  cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag)
  normal : ∀ anchor, source = some anchor → Nonempty (Normal tree location protections anchor)
  callbacks : ∀ position, (valid : position < tree.roots.size) →
    selectedRoot ≠ some tree.roots[position] → ∃ support,
      DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections
        tree.roots[position] position maximum .Read support ∧
      DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections
        tree.roots[position] position maximum .Write support

set_option autoImplicit false in
/-- Positive byte-window candidate with shared graph/source metadata and
permission requirements only on intersecting rows. No shape restriction on
outside roots, outside tag ordering, free-pool emptiness or outside-window
Unique/Disabled permissions occurs here. Runtime coherence, storage, provenance
resolution, caller ABI and numeric resources remain separate requirements.
This candidate is not renamed complete ValidCaller. -/
structure Positive (tree : BorrowTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64) where
  positive : 0 < len.toNat
  bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat
  sourcePresent : ∀ anchor, source = some anchor → ∃ node, tree.nodeAt anchor = some node
  wildcardRoot : source = none → 0 < tree.roots.size
  rows : GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (Row tree location protections source selectedRoot maximum))
    offset (offset + len) tree.locations

/-- Wildcard capability has no artificial selected component or tag cutoff. -/
theorem Row.wildcard_cutoff {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {selectedRoot : Option UniIndex} {maximum : Option BorTag}
    (row : Row tree location protections none selectedRoot maximum) : maximum = none := by
  rw [row.cutoff, row.wildcard rfl]
  rfl

end DuplicatePrefix.DuplicatePrefixBorrowAuthorization
