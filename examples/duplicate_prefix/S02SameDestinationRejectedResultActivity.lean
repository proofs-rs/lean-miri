import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.S02HiddenLeafActivityRange
import duplicate_prefix.S02HiddenLeafActiveRelease
import duplicate_prefix.GeneralBorrowRawTargetActivity
namespace DuplicatePrefix.S02SameDestinationRejectedResultActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshInstallation
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem replace_write (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (preserved : location.perms.get anchor = map.entries[position].data.perms.get anchor) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    have valueEq : value = location := by simpa only [replaced,Array.getElem_set_self] using dataEq.symm
    rw [valueEq,preserved] at stored
    exact active point map.entries[position].data ⟨position,oldBound,startPoint,pointStop,rfl⟩ state stored accessed kind associated
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by
      simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

/-- A modifier retaining a target permission entry preserves its exact activity interval, independently of the requested interval. -/
theorem modified (map : DedupRangeMap LocationTree) (anchor : UniIndex) (offset len : Size)
    (modify : ByteRange → LocationTree → LocationTree) (lower upper : UInt64)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (preserved : ∀ range location, (modify range location).perms.get anchor = location.perms.get anchor)
    (active : Profile map anchor .Write lower upper) :
    Profile (map.modifyRange offset len modify).state anchor .Write lower upper := by
  let prepared := map.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have good := preparedData.1
  have preparedActive := refines map prepared.state preparedData.2.1 anchor .Write lower upper active
  let property := fun current : DedupRangeMap LocationTree =>
    current.entries.map (·.range) = prepared.state.entries.map (·.range) ∧ Profile current anchor .Write lower upper
  have fold : ∀ (items : List Nat), (∀ position ∈ items, position ∈ prepared.positions.toList) →
      ∀ current, property current →
        property (items.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position modify) current) := by
    intro items
    induction items with
    | nil => intro _ current maintained;exact maintained
    | cons position rest ih =>
      intro included current maintained
      rcases maintained with ⟨ranges,currentActive⟩
      have sizeEq : current.entries.size = prepared.state.entries.size := by
        have known := congrArg Array.size ranges
        simpa only [Array.size_map] using known
      obtain ⟨cursor,cursorBound,same⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr (included position (by simp)))
      have known := good.selected cursor cursorBound
      have positionBound : position < prepared.state.entries.size := by
        have valid := known.choose
        change prepared.positions[cursor] < prepared.state.entries.size at valid
        simpa only [same] using valid
      have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
      have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
      have selected : prepared.segments[cursor] = prepared.state.entries[position] := by
        have selected := known.choose_spec
        change prepared.segments[cursor] = prepared.state.entries[prepared.positions[cursor]] at selected
        simpa only [same] using selected
      have rangeSame : current.entries[position].range = prepared.segments[cursor].range := by
        have range := congrArg (fun rows => rows[position]?) ranges
        simp only [Array.getElem?_map,
          Array.getElem?_eq_getElem (xs := current.entries) (i := position) currentBound,
          Array.getElem?_eq_getElem (xs := prepared.state.entries) (i := position) positionBound,
          Option.map_some,Option.some.injEq] at range
        exact range.trans (congrArg (fun segment : RangeMapSegment LocationTree => segment.range) selected).symm
      let updated := modify current.entries[position].range current.entries[position].data
      have actual : GeneralBorrowFreshModify.atPosition current position modify = replaced current position currentBound updated := by
        dsimp only [GeneralBorrowFreshModify.atPosition]
        simp only [currentBound,↓reduceDIte]
        rfl
      have next : property (replaced current position currentBound updated) :=
        ⟨(replaced_ranges current position currentBound updated).trans ranges,
          replace_write current position currentBound updated anchor lower upper currentActive (preserved _ _)⟩
      have later := ih (fun other member => included other (by simp [member])) _ next
      simpa only [List.foldl_cons,actual] using later
  rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds]
  exact (fold prepared.positions.toList (fun _ member => member) prepared.state ⟨rfl,preparedActive⟩).2
private theorem modified_sifa (tree : BorrowTree) (index parent target : UniIndex)
    (offset len : Size) (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (different : target ≠ index)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin
      (sourceUpdateSifa {tree with locations := (tree.locations.modifyRange offset len
        (fun _ location => materialized location index sharedState)).state} parent .Read).1 target .Write lower upper := by
  have updated := DuplicatePrefix.S02SameDestinationRejectedResultActivity.modified tree.locations target offset len
    (fun _ location => materialized location index sharedState) lower upper well bounds (by
      intro range location
      exact GeneralBorrowFreshLocation.get_other location.perms index target sharedState different) active
  exact sifa_preserves
    {tree with locations := (tree.locations.modifyRange offset len
      (fun _ location => materialized location index sharedState)).state} parent .Read target .Write lower upper updated

set_option autoImplicit false in
/-- A real shared append preserves an older anchor's strong Write activity.
This is a data-preservation statement, not a claim that an arbitrary access succeeds. -/
theorem append (tree : BorrowTree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none) (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected).tree target .Write lower upper := by
  rw [GeneralBorrowFreshSharedChild.append_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits isProtected offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let base : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩}
  have wellBase : base.locations.WellFormed := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact well
  have boundsBase : offset.toNat+len.toNat ≤ base.locations.size.bytes.toNat := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact bounds
  have activeBase : ActiveWithin base target .Write lower upper := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact active
  have different : target ≠ index := by
    intro equal
    have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes target targetNode targetPresent
    have atEnd : index.toNat = tree.nodes.data.size := by
      dsimp only [index,UniIndex.toNat]
      rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
      exact aligned
    rw [equal,atEnd] at valid
    omega
  have saved := modified_sifa base index parent target (Size.ofBytes offset) (Size.ofBytes len) lower upper
    wellBase boundsBase different activeBase
  simpa only [base,index,materialized,GeneralBorrowFreshGraph.attached,Size.ofBytes] using saved

set_option autoImplicit false in
/-- Reusing a vacant slot likewise preserves the older anchor's strong profile. -/
theorem reuse (tree : BorrowTree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected).tree target .Write lower upper := by
  have different : target ≠ index := by
    intro equal
    change tree.nodes.get target = some targetNode at targetPresent
    rw [equal,vacant] at targetPresent
    cases targetPresent
  have returned : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected).tree =
      (sourceUpdateSifa
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent)) with
          tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩
          locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
            (fun _ location => materialized location index sharedState)).state} parent .Read).1 := by
    simpa only [GeneralBorrowFreshGraph.attached,materialized] using GeneralBorrowFreshSharedChild.reuse_tree tree
      parentTag newTag parent parentNode parentTagPresent parentPresent fresh index available indexBound vacant isProtected offset len nonzero well bounds
  rw [returned]
  let base : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩}
  have wellBase : base.locations.WellFormed := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact well
  have boundsBase : offset.toNat+len.toNat ≤ base.locations.size.bytes.toNat := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact bounds
  have activeBase : ActiveWithin base target .Write lower upper := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact active
  have saved := modified_sifa base index parent target (Size.ofBytes offset) (Size.ofBytes len) lower upper
    wellBase boundsBase different activeBase
  simpa only [base,materialized,GeneralBorrowFreshGraph.attached,Size.ofBytes] using saved

theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295) (isProtected : Bool)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected).tree target .Write lower upper := by
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    exact append tree parentTag newTag parent parentNode tagged present fresh
      noFree aligned fits isProtected offset len nonzero runtime.formed.well bounds target lower upper targetNode targetPresent active
  | reuse child available valid vacant slack =>
    exact reuse tree parentTag newTag parent parentNode tagged present fresh
      child available valid vacant isProtected offset len nonzero runtime.formed.well bounds target lower upper targetNode targetPresent active


end DuplicatePrefix.S02SameDestinationRejectedResultActivity

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02SameDestinationRejectedResultActivity.modified, ``DuplicatePrefix.S02SameDestinationRejectedResultActivity.construct] do
   for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved exact target activity dependency {dependency}"
