import duplicate_prefix.OrdinaryConcreteNormalBridge
import duplicate_prefix.S05RetainedConeNumericAdapter
namespace DuplicatePrefix.OrdinaryConcreteWindowBridge
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralBorrowWildcardParentTagOrder
open OrdinaryBorrowAuthority OrdinaryBorrowAuthorityBridge S05RetainedConeNumericAdapter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Independent concrete authority supplies Snapshot.normal throughout this
byte window. Cross-root CallbackOwnership, numeric soundness and exposed-count
coherence remain explicit representation/authority obligations; this bridge
does not define them to be ordinary validity or establish their formation. -/
theorem positive (tree : BorrowTree) (protections : ProtectedTags)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tagOrder : ParentTagOrder tree) (short : tree.nodes.size < 65536)
    (mapped : tree.tagMapping.get tag = some anchor)
    (anchorNode : TreeNode) (anchorPresent : tree.nodes.get anchor = some anchorNode)
    (rootNode : TreeNode) (rootPresent : tree.nodeAt selected = some rootNode)
    (rootPath : ((source_normal_projection tree default protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (cutoff : maximum = some rootNode.tag)
    (positiveLength : 0 < len.toNat)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (authority : OwnedOn (fun location => ConcreteComponentAuthority tree location protections tag)
      offset (offset+len) tree.locations)
    (representation : OwnedOn (fun location => Representation tree location protections)
      offset (offset+len) tree.locations)
    (callbacks : OwnedOn (fun location =>
      ∀ position, (valid : position < tree.roots.size) → selected ≠ tree.roots[position] →
        ∃ rights : S05RetainedConeOwnership.CallbackOwnership tree location protections tree.roots[position] position maximum,
          S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains)
      offset (offset+len) tree.locations)
    (coherent : OwnedOn (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
      offset (offset+len) tree.locations) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections (some anchor) (some selected) maximum offset len := by
  apply callback_positive tree protections (some anchor) (some selected) maximum offset len graph tagOrder short positiveLength bounds
    (fun query same => by cases Option.some.inj same;exact ⟨anchorNode,anchorPresent⟩) (by intro impossible;cases impossible) ?_ coherent
  intro position valid nonempty start stop
  let location := tree.locations.entries[position].data
  obtain ⟨actual,node,tagged,_present,_tag,⟨normal⟩⟩ := OrdinaryConcreteNormalBridge.normal tree graph location protections tag
    (authority position valid nonempty start stop) (representation position valid nonempty start stop)
  have actualAnchor : actual = anchor := Option.some.inj (tagged.symm.trans mapped)
  subst actual
  refine ⟨{wildcard := ?_,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,ownership := ?_}⟩
  · intro impossible;cases impossible
  · intro query same
    cases Option.some.inj same
    exact rootPath
  · intro root same
    cases Option.some.inj same
    exact ⟨rootNode,rootPresent⟩
  · simpa only [Option.bind_some,rootPresent,Option.map_some] using cutoff
  · intro query same
    cases Option.some.inj same
    exact ⟨normal.component,normal.permissions .Write⟩
  · intro rootIndex rootValid different
    apply callbacks position valid nonempty start stop rootIndex rootValid
    intro same
    exact different (congrArg some same)
end DuplicatePrefix.OrdinaryConcreteWindowBridge
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.OrdinaryConcreteWindowBridge." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary concrete window bridge dependency {dependency}"
