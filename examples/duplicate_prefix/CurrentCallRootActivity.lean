import duplicate_prefix.S02HiddenLeafQuietTreeAccess
import duplicate_prefix.GeneralBorrowProtectedSiblingPartialActive
import duplicate_prefix.S05CompletedAncestryNormal
import duplicate_prefix.S05CompletedAncestryReadMutable

namespace DuplicatePrefix.CurrentCallRootActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem replace_write (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (preserved : ∀ (point : UInt64), map.entries[position].range.start.toNat ≤ point.toNat → point.toNat < map.entries[position].range.stop.toNat →
      ∀ state,location.perms.get anchor = some state → state.accessed = true → ∀ kind,state.permission.associatedAccess = some kind →
        lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    have sameData : location = value := by simpa only [replaced,Array.getElem_set_self] using dataEq
    rw [←sameData] at stored
    have bounds := preserved point startPoint pointStop state stored accessed kind associated
    exact ⟨bounds.1,bounds.2,by intro h;cases h⟩
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

/-- An arbitrary-root concrete Read or Write preserves a distinct hidden old
leaf's bytewise activity interval through its normal visitor and every callback.
No singleton root, sibling relation, successful operation or extra caller
permission profile is assumed. The access and owner intervals may overlap. -/
theorem concrete_of_normal (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (source query : UniIndex) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode)
    (offset len : UInt64) (requestBounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (normalRows : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source))
      offset (offset+len) tree.locations)
    (tagged : tree.indexOfTag tag = some source)
    (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    ActiveWithin (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len)
      kind global.protectedTags mode).tree query .Write lower upper := by
  let requestedOffset := Size.ofBytes offset
  let requestedLen := Size.ofBytes len
  let protections := global.protectedTags
  have well := runtime.formed.well
  have bounds : requestedOffset.bytes.toNat+requestedLen.bytes.toNat ≤ tree.locations.size.bytes.toNat := requestBounds
  let prepared := tree.locations.iterMut requestedOffset requestedLen
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations requestedOffset requestedLen well bounds
  have good := preparedData.1
  have preparedActive := refines tree.locations prepared.state preparedData.2.1 query .Write lower upper active
  have preparedCoherent := GeneralRangeMapSafety.iter_mut
    (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    tree.locations requestedOffset requestedLen well runtime.coherent bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations requestedOffset requestedLen well bounds
    (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location protections source))
    offset (offset+len) normalRows (Nat.le_refl _) (Nat.le_refl _)
  have preparedOutcome : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).outcome = .ok () := good.outcome
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,preparedOutcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.1.entries.map (·.range) = prepared.state.entries.map (·.range) ∧ Profile state.1 query .Write lower upper
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state maintained
    rcases state with ⟨current,visited,status⟩
    rcases maintained with ⟨ranges,currentActive⟩
    by_cases completed : status = .Completed
    · subst status
      have sizeEq : current.entries.size = prepared.state.entries.size := by
        have known := congrArg Array.size ranges
        simpa only [Array.size_map] using known
      have cursorBound : cursor < prepared.positions.size := by have := List.mem_range'_1.mp member;omega
      have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selected⟩ := good.selected cursor cursorBound
      have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
      have rangeSame : current.entries[position].range = segment.range := by
        have known := congrArg (fun rows => rows[position]?) ranges
        simp only [Array.getElem?_map,
          Array.getElem?_eq_getElem (xs := current.entries) (i := position) currentBound,
          Array.getElem?_eq_getElem (xs := prepared.state.entries) (i := position) positionBound,
          Option.map_some,Option.some.injEq] at known
        have selectedRange : prepared.state.entries[position].range = segment.range :=
          (congrArg (fun entry : RangeMapSegment LocationTree => entry.range) selected).symm
        exact known.trans selectedRange
      let access := source_tree_access_at tree segment.data (some source) kind protections mode segment.range
      let mutation := current.setAtPos position (source_access_location access)
      have afterRanges : mutation.state.entries.map (·.range) = prepared.state.entries.map (·.range) := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound,replaced_ranges]
        exact ranges
      have afterActive : Profile mutation.state query .Write lower upper := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        apply replace_write current position currentBound _ query lower upper currentActive
        intro point startPoint pointStop state stored accessed accessKind associated
        by_cases inside : lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat
        · exact inside
        · have oldRange : prepared.state.entries[position].range = segment.range := (congrArg (fun entry : RangeMapSegment LocationTree => entry.range) selected).symm
          have oldData : prepared.state.entries[position].data = segment.data := (congrArg (fun entry : RangeMapSegment LocationTree => entry.data) selected).symm
          have atPoint : ValueAt prepared.state point segment.data := ⟨position,positionBound,by rw [oldRange,←rangeSame];exact startPoint,by rw [oldRange,←rangeSame];exact pointStop,oldData⟩
          have oldQuiet : S02HiddenLeafQuietNormal.LocationTyped segment.data query := by
            intro old oldStored
            by_cases cell : old.permission = .Cell
            · exact Or.inr cell
            · apply Or.inl
              by_cases notFalse : old.accessed = false
              · exact notFalse
              · have oldAccessed : old.accessed = true := by
                  cases flag : old.accessed with
                  | false => exact False.elim (notFalse flag)
                  | true => first | exact flag | rfl
                have oldAssociated : ∃ accessKind,old.permission.associatedAccess = some accessKind := by
                  cases permission : old.permission <;> simp_all [Permission.associatedAccess]
                obtain ⟨oldKind,oldAssociated⟩ := oldAssociated
                have wasInside := preparedActive point segment.data atPoint old oldStored oldAccessed oldKind oldAssociated
                exact False.elim (inside ⟨wasInside.1,wasInside.2.1⟩)
          have segmentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree segment.data global.protectedTags := by
            have property := preparedCoherent.every position positionBound
            rw [←selected] at property
            exact property
          obtain ⟨normal⟩ := preparedOwners.2.2 cursor segmentBound
          have oldEffectiveQuiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective segment.data query node) := by
            cases oldStored : segment.data.perms.get query with
            | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_none,TreeNode.defaultLocationState]
            | some old => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_some] using oldQuiet old oldStored
          have newEffectiveQuiet := (S02HiddenLeafQuietTreeAccess.concrete tree runtime.formed.toGraphState segment.data global.protectedTags
            query source node sourceNode present sourcePresent leaf hidden different normal segmentCoherent kind mode segment.range oldEffectiveQuiet).1
          have newQuiet : S02HiddenLeafQuietNormal.LocationTyped
              (source_access_location access) query := by
            intro value valueStored
            change S02HiddenLeafQuietNormal.Quiet value
            change S02HiddenLeafQuietNormal.Quiet (((source_access_location access).perms.get query).getD node.defaultLocationState) at newEffectiveQuiet
            simpa only [valueStored,Option.getD_some] using newEffectiveQuiet
          rcases newQuiet state stored with inactive | cell
          · rw [accessed] at inactive;cases inactive
          · rw [cell,Permission.associatedAccess] at associated;cases associated
      have positionLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
      dsimp only [mutation,access,protections] at afterRanges afterActive
      cases failure : source_access_status access
      all_goals dsimp only [access,protections] at failure
      all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
          setAtPos_success current position currentBound,failure,property,ForInStep.value]
          using And.intro afterRanges afterActive
    · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using And.intro ranges currentActive
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedActive⟩
  have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step (prepared.state,#[],.Completed) initial
  exact final.2
theorem concrete (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (completion : CandidateStableCallOwnership.Completion) (complete : CandidateStableCallOwnership.Completes tree completion)
    (position : Nat) (root source query : UniIndex) (rootNode sourceNode : TreeNode)
    (slot : tree.roots[position]? = some root) (rootAt : tree.nodes.get root = some rootNode)
    (sourceAt : tree.nodeAt source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (tag : BorTag) (tagged : tree.indexOfTag tag = some source) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
      offset (offset+len) tree.locations)
    (node : TreeNode) (present : tree.nodeAt query = some node) (leaf : node.children = #[])
    (hidden : node.isExposed = false) (different : query ≠ source)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    ActiveWithin (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len)
      kind global.protectedTags mode).tree query .Write lower upper := by
  obtain ⟨depth⟩ := runtime.formed.depth
  apply concrete_of_normal tree global runtime tag source query sourceNode sourceAt offset len bounds _ tagged
    node present leaf hidden different lower upper active kind mode
  intro cursor valid positive start stop
  have authority := owned cursor valid positive start stop
  exact S05CompletedAncestryNormal.normal tree completion _ global.protectedTags complete runtime.formed.toGraphState
    depth runtime.formed.fits position root source rootNode slot rootAt sourcePath
    (fun index node found _ => (authority index node found).1)
    (fun index node found _ => (authority index node found).2)

end DuplicatePrefix.CurrentCallRootActivity
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallRootActivity." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved root activity dependency {dependency}"
