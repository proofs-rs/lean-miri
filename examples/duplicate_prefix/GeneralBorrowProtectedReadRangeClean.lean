import duplicate_prefix.GeneralBorrowProtectedReadRelease
import duplicate_prefix.GeneralBorrowRange
namespace DuplicatePrefix.GeneralBorrowProtectedReadRangeClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem preserves (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (mode : ChildrenVisitMode)
    (query : UniIndex) (outside : tree.nodes.data.size ≤ query.toNat)
    (clean : Every (fun location : LocationTree => location.perms.get query = none) tree.locations)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed)
    (all : Every (GeneralBorrowProtectedReadRelease.Profile tree protections) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read protections mode
    result.status = .Completed ∧ Every (fun location => GeneralBorrowProtectedReadRelease.Profile result.tree protections location ∧ location.perms.get query = none) result.tree.locations := by
  let predicate := fun location => GeneralBorrowProtectedReadRelease.Profile tree protections location ∧ location.perms.get query = none
  have before : Every predicate tree.locations := fun position valid => ⟨all position valid,clean position valid⟩
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate
    tree.locations offset len well before bounds
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧ Every predicate state.1
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,mapProfile⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by
      rw [←preparedGood.lengths]
      exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have ownedHere : predicate segment.data := by
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedGood.every position positionBound
    obtain ⟨⟨⟨forest⟩,data⟩,vacant⟩ := ownedHere
    have callback := GeneralBorrowProtectedReadInvariantLocation.location tree segment.data protections anchor root mode segment.range
      forest fits depth children anchorNode anchorPresent roots covered data
    have accessGood := callback.1
    have preservedClean : (source_access_location (source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range)).perms.get query = none := by
      have sizes := projection_sizes tree segment.data protections
      have valid : anchor.toNat < (source_normal_projection tree segment.data protections).topology.nodes.size := by
        obtain ⟨bounded,_⟩ := array_of_node tree anchor anchorNode anchorPresent
        unfold_general_projection;unfold_general_topology;simpa only [Array.size_map] using bounded
      have compatible : ∀ index,index < (source_normal_projection tree segment.data protections).topology.nodes.size → ∃ state,
          (source_normal_projection tree segment.data protections).stateAt index = some state ∧
          GeneralBorrowProtectedReadCompatible.Compatible state (GeneralBorrowAnchor.relation (source_normal_projection tree segment.data protections) anchor.toNat index)
            ((source_normal_projection tree segment.data protections).protectedNodes.contains index) := by
        intro index bounded
        have aligned : (source_normal_projection tree segment.data protections).locationStates.size =
            (source_normal_projection tree segment.data protections).topology.nodes.size := by
          unfold_general_projection;unfold_general_topology;simp only [Array.size_mapIdx,Array.size_map]
        obtain ⟨state,present,good⟩ := data index (by omega)
        exact ⟨state,present,GeneralBorrowProtectedReadInvariant.compatible state _ _ good⟩
      rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree segment.data protections anchor root mode segment.range
        forest valid compatible depth children anchorNode anchorPresent roots covered]
      exact GeneralBorrowFreshActiveOnClean.normal_append tree segment.data protections anchor query .Read mode outside vacant
    let access := source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range
    let mutation := current.setAtPos position (source_access_location access)
    have currentBound : position < current.entries.size := by
      rw [sizeEq]
      exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position :=
      Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment :=
      Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal access⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,
        positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound (source_access_location access)).trans sizeEq,?_⟩
    change Every predicate mutation.state
    dsimp only [mutation]
    rw [setAtPos_exact current position currentBound]
    exact replaced_every _ current position currentBound _ mapProfile ⟨⟨⟨forest⟩,callback.2⟩,preservedClean⟩
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,rfl,preparedGood.every⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ initial
  refine ⟨final.1,?_⟩
  exact final.2.2


end DuplicatePrefix.GeneralBorrowProtectedReadRangeClean
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadRangeClean.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read range invariant dependency {dependency}"
