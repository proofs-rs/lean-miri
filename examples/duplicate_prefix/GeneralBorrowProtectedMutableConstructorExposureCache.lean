import duplicate_prefix.GeneralBorrowExposureChildAttach
import duplicate_prefix.GeneralBorrowExposureSifaTransport
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
namespace DuplicatePrefix.GeneralBorrowProtectedMutableConstructorExposureCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshChild (child inside)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Generic cache formation for the actual attachment and range-installation
stages before the real ancestor-SIFA loop. Both append and reuse instantiate
this from initial allocator geometry, with no final-state invariant premise. -/
private theorem stage (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag) (mapping : UniKeyMap BorTag)
    (vacant : tree.nodes.get index = none) (present : tree.nodeAt parent = some parentNode)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode (child newTag parent)).size)
    (newDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode (child newTag parent)))
    (offset len : UInt64) (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let result := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode (child newTag parent) mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)).state
    Every (fun location => LocationCoherent result location protections) result.locations := by
  dsimp only
  let base := {tree with nodes := attachedNodes tree.nodes index parent parentNode (child newTag parent)}
  let predicate := fun location => LocationCoherent base location protections
  have baseGood : Every predicate tree.locations := by
    intro position valid
    exact GeneralBorrowExposureChildAttach.attach tree depth index parent parentNode (child newTag parent)
      vacant present rfl size _ protections (initial position valid)
  have different : index ≠ parent := by
    intro same
    change tree.nodes.get parent = some parentNode at present
    rw [←same,vacant] at present
    cases present
  have newPresent : base.nodeAt index = some (child newTag parent) := by
    change ((tree.nodes.insert index (child newTag parent)).insert parent _).get index = _
    rw [GeneralBorrowFreshLocation.get_other _ parent index _ different,GeneralBorrowFreshLocation.get_same]
  have modifyStep : ∀ range location,predicate location → predicate
      ((fun (_ : ByteRange) location => GeneralBorrowFreshMaterialization.materialized location index inside) range location) := by
    intro range location good
    change LocationCoherent base {location with perms := location.perms.insert index inside} protections
    exact GeneralBorrowExposureChildAttach.materialize base newDepth index (child newTag parent)
      newPresent rfl location protections inside good
  have modified := GeneralBorrowExposureChildAttach.modify_every predicate tree.locations
    (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside) well bounds baseGood
    modifyStep
  exact modified

/-- The actual positive unprotected Default append constructor preserves the generic
per-range cache invariant on arbitrary forests and exposure flags. -/
theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (initial : Every (fun location => LocationCoherent input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Every (fun location => LocationCoherent (GeneralBorrowFreshMetadataChildMutable.result input) location protections)
      (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutable.append input).success,?_⟩
  let index := GeneralBorrowFreshMetadataChildMutable.index input
  have atEnd : index.toNat = input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
  have vacant : input.tree.nodes.get index = none := by simp [UniValMap.get,atEnd]
  have different := parent_not_fresh input.tree.nodes index input.parent input.parentNode atEnd input.parentPresent
  have parentAfter : (input.tree.nodes.insert index (child input.newTag input.parent)).get input.parent = some input.parentNode :=
    (GeneralBorrowFreshLocation.get_other _ index input.parent _ different).trans input.parentPresent
  have size : input.tree.nodes.size ≤ (attachedNodes input.tree.nodes index input.parent input.parentNode (child input.newTag input.parent)).size := by
    unfold attachedNodes
    rw [insert_existing_size _ input.parent input.parentNode _ parentAfter,append_size _ index _ atEnd]
    omega
  let certificate := attached_depth input.tree.nodes input.depth index input.parent input.parentNode
    (child input.newTag input.parent) atEnd input.parentPresent rfl
  have stageGood := stage input.tree input.depth index input.parent input.parentNode input.newTag
    (GeneralBorrowFreshMetadataChildMutable.mapping input) vacant input.parentPresent size certificate input.offset input.len
    input.well input.bounds protections initial
  change Every (fun location => LocationCoherent (GeneralBorrowFreshMetadataChildMutable.stage input) location protections)
    (GeneralBorrowFreshMetadataChildMutable.stage input).locations at stageGood
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq input]
  exact GeneralBorrowExposureSifaTransport.sifa (GeneralBorrowFreshMetadataChildMutable.stage input) protections certificate input.parent .None stageGood

/-- The same real constructor cache closure for a bounded vacant reusable slot.
No permission Clean assumption is inferred from node vacancy or needed here:
the new node is unexposed, and this theorem claims cache coherence only. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (protections : ProtectedTags)
    (initial : Every (fun location => LocationCoherent input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Every (fun location => LocationCoherent (GeneralBorrowFreshMetadataChildMutableReuse.result input) location protections)
      (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).success,?_⟩
  let index := GeneralBorrowFreshMetadataChildMutableReuse.index input
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant input.tree.nodes index input.parent input.parentNode input.vacant input.parentPresent
  have parentAfter : (input.tree.nodes.insert index (child input.newTag input.parent)).get input.parent = some input.parentNode :=
    (GeneralBorrowFreshLocation.get_other _ index input.parent _ different).trans input.parentPresent
  have size : input.tree.nodes.size ≤ (attachedNodes input.tree.nodes index input.parent input.parentNode (child input.newTag input.parent)).size := by
    unfold attachedNodes
    rw [insert_existing_size _ input.parent input.parentNode _ parentAfter,
      GeneralBorrowFreshReuseNode.bounded_size _ index _ input.valid]
    exact Nat.le_refl _
  let certificate := GeneralBorrowFreshReuseNode.attached_depth input.tree.nodes input.depth index input.parent input.parentNode
    (child input.newTag input.parent) input.valid input.vacant input.parentPresent rfl input.parentSlack
  have stageGood := stage input.tree input.depth index input.parent input.parentNode input.newTag
    (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) input.vacant input.parentPresent size certificate input.offset input.len
    input.well input.bounds protections initial
  change Every (fun location => LocationCoherent (GeneralBorrowFreshMetadataChildMutableReuse.stage input) location protections)
    (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations at stageGood
  rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq input]
  exact GeneralBorrowExposureSifaTransport.sifa (GeneralBorrowFreshMetadataChildMutableReuse.stage input) protections certificate input.parent .None stageGood

end DuplicatePrefix.GeneralBorrowProtectedMutableConstructorExposureCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedMutableConstructorExposureCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved Default constructor cache dependency {dependency}"
