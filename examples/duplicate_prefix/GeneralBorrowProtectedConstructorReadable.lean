import duplicate_prefix.GeneralBorrowProtectedReadProfileShape
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowConstructorPriorPermissionRange
namespace DuplicatePrefix.GeneralBorrowProtectedConstructorReadable
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshChild
open DuplicatePrefix.GeneralBorrowProtectedReadInvariant DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem projection_slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (query : UniIndex) (converted : UniIndex.ofNat? position = some query)
    (equal : query.toNat = position) (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get query).getD (((tree.nodeAt query).map TreeNode.defaultLocationState).getD ⟨.Disabled,false,.None⟩)) := by
  have nodeValue : tree.nodeAt query = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    converted,Option.map_some]
  rw [nodeValue]
  generalize stateEq : location.perms.get query = stored
  clear stateEq
  generalize nodeEq : tree.nodes.data[position] = node
  clear nodeEq
  cases stored <;> cases node <;> rfl

private theorem attached_size (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode) :
    (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.size = tree.nodes.data.size+1 := by
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  change ((tree.nodes.insert index newNode).insert parent {parentNode with children := parentNode.children.push index}).size = tree.nodes.size+1
  rw [insert_existing_size (tree.nodes.insert index newNode) parent parentNode _ old,append_size tree.nodes index newNode atEnd]


private theorem insert (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (state : LocationState) (fits : tree.nodes.data.size ≤ 4294967296) (initial : Data (source_normal_projection tree location protections))
    (readable : ∀ held,Readable state held) :
    Data (source_normal_projection tree (materialized location index state) protections) := by
  intro position valid
  have bound : position < tree.nodes.data.size := by rw [(projection_sizes tree _ protections).1] at valid;exact valid
  obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
  by_cases same : query = index
  · subst query
    refine ⟨state,?_,readable _⟩
    rw [projection_slot tree _ protections position index converted equal bound]
    simp only [materialized,GeneralBorrowFreshLocation.get_same,Option.getD_some]
  · obtain ⟨old,present,good⟩ := initial position (by rw [(projection_sizes tree location protections).1];exact bound)
    refine ⟨old,?_,?_⟩
    · rw [projection_slot tree location protections position query converted equal bound] at present
      rw [projection_slot tree _ protections position query converted equal bound]
      simpa only [materialized,GeneralBorrowFreshLocation.get_other _ index query state same] using present
    · exact good

/-- An actual fresh Default child has a readable lazy outside state and a
readable materialized inside state, regardless of whether its protector is held. -/
private theorem attached (tree : BorrowTree) (index parent : UniIndex) (node : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some node)
    (location : LocationTree) (protections : ProtectedTags)
    (clean : location.perms.get index = none) (initial : Data (source_normal_projection tree location protections)) :
    Data (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent node (child tag parent)) location protections) := by
  let next := GeneralBorrowFreshGraph.attached tree index parent node (child tag parent)
  have size : next.nodes.data.size = tree.nodes.data.size+1 := attached_size tree index parent node (child tag parent) atEnd present
  intro position valid
  have bound : position < next.nodes.data.size := by rw [(projection_sizes next location protections).1] at valid;exact valid
  by_cases fresh : position = index.toNat
  · subst position
    have leaf : next.nodeAt index = some (child tag parent) := GeneralBorrowFreshGraph.new_lookup tree index parent node (child tag parent) atEnd present
    refine ⟨(child tag parent).defaultLocationState,?_,?_⟩
    · rw [projection_slot next location protections index.toNat index (index_self index) rfl bound]
      simp only [clean,Option.getD_none,leaf,Option.map_some,Option.getD_some]
    · exact reservation false false .None _
  · have oldBound : position < tree.nodes.data.size := by omega
    obtain ⟨old,stored,good⟩ := initial position (by rw [(projection_sizes tree location protections).1];exact oldBound)
    have stateEq := state_old tree index parent node (child tag parent) atEnd present location inside protections position oldBound
    have endBound : index.toNat < 4294967296 := UInt32.toNat_lt index.idx
    obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
    have different : query ≠ index := by intro same;subst query;exact fresh equal.symm
    have sameState : (source_normal_projection next (materialized location index inside) protections).stateAt position =
        (source_normal_projection next location protections).stateAt position := by
      rw [projection_slot next _ protections position query converted equal bound,
        projection_slot next location protections position query converted equal bound]
      simp only [materialized,GeneralBorrowFreshLocation.get_other _ index query inside different]
    refine ⟨old,sameState.symm.trans (stateEq.trans stored),?_⟩
    rw [protection_old tree index parent node (child tag parent) atEnd present location location protections position oldBound]
    exact good

private theorem modify_every {α : Type} [DecidableEq α] (predicate : α → Prop) (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α) (well : map.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat) (initial : Every predicate map)
    (step : ∀ range value,predicate value → predicate (modify range value)) :
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

/-- Actual protected Default append preserves all-tag Read compatibility,
including the earlier active protected siblings needed by real release scans.
The fresh slot's old permission must be Clean throughout the initial map. -/
theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (initial : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (clean : Every (fun location => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none) input.tree.locations) :
    Every (GeneralBorrowProtectedReadRelease.Profile (GeneralBorrowFreshMetadataChildMutable.result input) protections)
      (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  let next := GeneralBorrowFreshGraph.attached input.tree (GeneralBorrowFreshMetadataChildMutable.index input)
    input.parent input.parentNode (child input.newTag input.parent)
  have before : Every (GeneralBorrowProtectedReadRelease.Profile next protections) input.tree.locations := by
    intro position valid
    obtain ⟨⟨forest⟩,data⟩ := initial position valid
    refine ⟨⟨GeneralBorrowFreshProjection.projected_forest input.tree _ input.parent input.parentNode (child input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildMutable.at_end input) input.parentPresent rfl rfl _ _ protections forest⟩,?_⟩
    exact attached input.tree _ input.parent input.parentNode input.newTag (GeneralBorrowFreshMetadataChildMutable.at_end input)
      input.parentPresent _ protections (clean position valid) data
  have nextFits : next.nodes.data.size ≤ 4294967296 := by
    have size := attached_size input.tree (GeneralBorrowFreshMetadataChildMutable.index input) input.parent input.parentNode
      (child input.newTag input.parent) (GeneralBorrowFreshMetadataChildMutable.at_end input) input.parentPresent
    have aligned := input.aligned
    have bound := input.fits
    change next.nodes.data.size = _ at size
    omega
  have modified := modify_every (GeneralBorrowProtectedReadRelease.Profile next protections) input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len) (fun _ location => materialized location (GeneralBorrowFreshMetadataChildMutable.index input) inside)
    input.well input.bounds before (fun _ location good => ⟨good.1,insert next location protections _ inside nextFits good.2 (reservation false true .None)⟩)
  have staged : Every (GeneralBorrowProtectedReadRelease.Profile (GeneralBorrowFreshMetadataChildMutable.stage input) protections)
      (GeneralBorrowFreshMetadataChildMutable.stage input).locations := modified
  exact GeneralBorrowProtectedReadProfileShape.shape _ _ protections (GeneralBorrowFreshMetadataChildMutable.shape input) staged
end DuplicatePrefix.GeneralBorrowProtectedConstructorReadable
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedConstructorReadable.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected constructor readable dependency {dependency}"
