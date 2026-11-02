import duplicate_prefix.GeneralBorrowGcCacheFrame
import duplicate_prefix.GeneralBorrowGcExposedRetained
import duplicate_prefix.GeneralBorrowGcSurvivingPathFormation
import duplicate_prefix.GeneralBorrowGcNodeMetadata
import duplicate_prefix.GeneralBorrowGcTreeComplete

namespace DuplicatePrefix.GeneralBorrowGcCachePreservation
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowExposureAncestorFold DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem effective_same (original current : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (metadata : GeneralBorrowGcNodeMetadata.Metadata original current)
    (frame : GeneralBorrowGcCacheFrame.Frame before current.nodes after)
    (source : UniIndex) (next : TreeNode) (found : current.nodes.get source = some next)
    (old : TreeNode) (present : original.nodes.get source = some old) :
    effective after protections source next = effective before protections source old := by
  obtain ⟨actual,actualFound,fields⟩ := metadata source next found
  have same := Option.some.inj (present.symm.trans actualFound)
  subst actual
  simp only [effective,frame.stored source next found,fields.tag,TreeNode.defaultLocationState,fields.permission,fields.sifa]

private theorem counts (original current : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (metadata : GeneralBorrowGcNodeMetadata.Metadata original current)
    (retained : GeneralBorrowGcExposedRetained.Retained original current)
    (paths : GeneralBorrowGcSurvivingPaths.Relation original.nodes current.nodes)
    (frame : GeneralBorrowGcCacheFrame.Frame before current.nodes after)
    (query : UniIndex) (queryNode : TreeNode) (queryPresent : current.nodes.get query = some queryNode) (kind : AccessKind) :
    cardinality current.nodes (effective after protections) query kind =
      cardinality original.nodes (effective before protections) query kind := by
  have same : ∀ source,
      source ∈ GeneralBorrowExposureGraphTransport.sources current.nodes (effective after protections) query kind ↔
      source ∈ GeneralBorrowExposureGraphTransport.sources original.nodes (effective before protections) query kind := by
    intro source
    rw [GeneralBorrowExposureGraphTransport.member,GeneralBorrowExposureGraphTransport.member]
    constructor
    · rintro ⟨next,found,exposed,supported,ancestor⟩
      obtain ⟨old,present,fields⟩ := metadata source next found
      refine ⟨old,present,fields.exposed.symm.trans exposed,?_,(paths source next found query queryNode queryPresent).mp ancestor⟩
      rw [←effective_same original current before after protections metadata frame source next found old present]
      exact supported
    · rintro ⟨old,present,exposed,supported,ancestor⟩
      obtain ⟨next,found,_⟩ := retained source old present exposed
      obtain ⟨actual,actualFound,fields⟩ := metadata source next found
      have equal := Option.some.inj (present.symm.trans actualFound)
      subst actual
      refine ⟨next,found,fields.exposed.trans exposed,?_,(paths source next found query queryNode queryPresent).mpr ancestor⟩
      rw [effective_same original current before after protections metadata frame source next found old present]
      exact supported
  have permutation := (List.perm_ext_iff_of_nodup
      (GeneralBorrowExposureGraphTransport.sources_nodup current.nodes (effective after protections) query kind)
      (GeneralBorrowExposureGraphTransport.sources_nodup original.nodes (effective before protections) query kind)).mpr same
  simpa only [GeneralBorrowExposureGraphTransport.sources,List.length_map,cardinality] using permutation.length_eq

private theorem absent_count (tree : BorrowTree) (depth : ParentDepth tree.nodes) (location : LocationTree)
    (protections : ProtectedTags) (query : UniIndex) (missing : tree.nodes.get query = none) (kind : AccessKind) :
    cardinality tree.nodes (effective location protections) query kind = 0 := by
  have absent : GeneralBorrowExposureGraphTransport.sources tree.nodes (effective location protections) query kind = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index member
    obtain ⟨node,present,_,_,walked⟩ := (GeneralBorrowExposureGraphTransport.member _ _ _ _ _).mp member
    obtain ⟨⟨value,found⟩,_⟩ := GeneralBorrowExposureAncestorDistinct.present_depth tree.nodes depth
      (tree.nodes.size+1) index node present query walked
    rw [missing] at found
    cases found
  have size := congrArg List.length absent
  simpa only [GeneralBorrowExposureGraphTransport.sources,List.length_map,List.length_nil,cardinality] using size

/-- Data-only join of actual lookup-origin, surviving-node metadata, exposed
source retention and exact surviving ancestry certificates. Neither cache
cardinality nor target-operation success is assumed in the final tree. -/
theorem transfer (original current : BorrowTree) (protections : ProtectedTags)
    (metadata : GeneralBorrowGcNodeMetadata.Metadata original current)
    (retained : GeneralBorrowGcExposedRetained.Retained original current)
    (paths : GeneralBorrowGcSurvivingPaths.Valid original.nodes current.nodes)
    (lookup : GeneralBorrowGcCacheFrame.Property original protections current) :
    Every (fun location => LocationCoherent current location protections) current.locations := by
  obtain ⟨depth,ancestry⟩ := paths
  intro position valid
  obtain ⟨before,initial,frame⟩ := lookup position valid
  intro query kind
  cases present : current.nodes.get query with
  | none =>
    rw [frame.vacant query present kind,absent_count current depth _ protections query present kind]
    rfl
  | some queryNode =>
    rw [frame.counters query queryNode present kind,initial query kind,
      counts original current before _ protections metadata retained ancestry frame query queryNode present kind]

/-- FULL production GC on ANY single-root reciprocal forest preserves the
actual modular exposed-support cardinality invariant, every partition, either
access kind and arbitrary protections/exposure flags. Exposed tags are explicitly
in the initial liveness vector; traversal/success/retention/ancestry/cache
postconditions are all internally derived. No Rust correspondence is required. -/
theorem single (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) (closed : GeneralBorrowGraph.ChildNodes tree)
    (root : UniIndex) (node : TreeNode) (present : tree.nodes.get root = some node)
    (roots : tree.roots = #[root]) (well : tree.locations.WellFormed)
    (live : Array BorTag) (exposedLive : GeneralBorrowGcExposedRetained.ExposedLive tree live)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
      Every (fun location => LocationCoherent (tree.removeUnreachableTags live).tree location protections)
        (tree.removeUnreachableTags live).tree.locations := by
  refine ⟨(GeneralBorrowGcTreeComplete.complete tree location protections forest closed root node live present roots well).1,?_⟩
  exact transfer tree (tree.removeUnreachableTags live).tree protections
    (GeneralBorrowGcNodeMetadata.collect tree live)
    (GeneralBorrowGcExposedRetained.collect tree live exposedLive)
    (GeneralBorrowGcSurvivingPathFormation.single tree location protections forest depth closed root node present roots live)
    (GeneralBorrowGcCacheFrame.collect tree protections depth initial live)

end DuplicatePrefix.GeneralBorrowGcCachePreservation
