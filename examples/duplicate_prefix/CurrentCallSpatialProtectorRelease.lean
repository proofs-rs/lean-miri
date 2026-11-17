import duplicate_prefix.CurrentCallSpatialRead
import duplicate_prefix.CurrentCallSpatialWrite
import duplicate_prefix.CurrentCallSpatialSourceCover
import duplicate_prefix.CurrentCallResourceReleaseFrame

/-! The existing release iterator consumes spatial ORIGINAL-row certificates.
The finite cell assignment is fixed; no completion is selected per operation. -/
namespace DuplicatePrefix.CurrentCallSpatialProtectorRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposureCardinality
open GeneralBorrowExposedNonleafPrimaryPath BorrowRangeAccess
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

variable {before tracker ctx mode offset length} (role : RoleCover before tracker ctx mode offset length)

abbrev RowRuntime (location : LocationTree) : Prop :=
  LocationCoherent role.backing.allocation.extra location tracker.global.protectedTags ∧
  GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra location tracker.global.protectedTags ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra location

/-- Each returned row retains every cell intersecting its saved actual initial
segment. The existential names an original segment, never a new completion. -/
def SavedCells (range : ByteRange) (location : LocationTree) : Prop :=
  ∃ original∈role.backing.allocation.extra.locations.entries.toList,
    original.range=range ∧ CurrentCallSpatialRows.Frame role original.data location

private theorem cell_access (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (concrete : ∃ id tag,role.family.value.provenance=.concrete id tag)
    (segment : RangeMapSegment LocationTree) (member : segment∈role.backing.allocation.extra.locations.entries.toList)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i)
    (byte : AllocId×Nat) (request : Window role.backing.id offset length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (lower : segment.range.start.toNat≤byte.2) (upper : byte.2<segment.range.stop.toNat)
    (kind : AccessKind) (visit : ChildrenVisitMode) (range : ByteRange) :
    let actual:=source_tree_access_at role.backing.allocation.extra segment.data (CurrentCallSpatialRows.source role)
      kind tracker.global.protectedTags visit range
    source_access_status actual=none ∧ RowRuntime role (source_access_location actual) ∧
      S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion tracker.global.protectedTags
        (role.roles i overlap).grant (source_access_location actual) := by
  cases kind with
  | Write =>
    have result:=CurrentCallSpatialWrite.row role exclusive runtime distinct short segment member i overlap byte request cell lower upper visit range
    exact ⟨result.1,⟨result.2.1,result.2.2.1,result.2.2.2.1⟩,result.2.2.2.2⟩
  | Read =>
    let W:=CurrentCallSpatialRows.singleByte role i overlap byte request cell
    obtain ⟨G⟩:=geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) exclusive
    obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    have coherent:=runtime.coherent position valid
    have profile:=runtime.formed.profile position valid
    have possible:=runtime.possible position valid
    rw [same] at coherent profile possible
    have result:=CurrentCallResourceRead.concrete_read W G exclusive byte
      (CurrentCallSpatialRows.singleByte_inside role i overlap byte request cell) segment member lower upper concrete
      distinct coherent short profile possible visit range
    obtain ⟨id,tag,value⟩:=concrete
    have sourceAt:=CurrentCallSpatialRows.source_at role i overlap
    simp only [value] at sourceAt
    rw [sourceAt]
    exact ⟨result.1,⟨result.2.1,result.2.2.1,result.2.2.2.1⟩,result.2.2.2.2.2⟩

private theorem row_access (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (concrete : ∃ id tag,role.family.value.provenance=.concrete id tag)
    (segment : RangeMapSegment LocationTree) (member : segment∈role.backing.allocation.extra.locations.entries.toList)
    (byte : AllocId×Nat) (request : Window role.backing.id offset length byte)
    (lower : segment.range.start.toNat≤byte.2) (upper : byte.2<segment.range.stop.toNat)
    (kind : AccessKind) (visit : ChildrenVisitMode) (range : ByteRange) :
    let actual:=source_tree_access_at role.backing.allocation.extra segment.data (CurrentCallSpatialRows.source role)
      kind tracker.global.protectedTags visit range
    source_access_status actual=none ∧ RowRuntime role (source_access_location actual) ∧
      CurrentCallSpatialRows.Frame role segment.data (source_access_location actual) := by
  obtain ⟨i,cell⟩:=role.covered byte request
  let overlap : CurrentCallSpatialSourceCover.Active role i:=⟨byte,request,cell⟩
  have result:=cell_access role exclusive runtime distinct short concrete segment member i overlap byte request cell lower upper kind visit range
  refine ⟨result.1,result.2.1,?_⟩
  intro original originalMember same j joint hit
  obtain ⟨point,pointRequest,pointCell,pointLower,pointUpper⟩:=hit
  have all:=cell_access role exclusive runtime distinct short concrete original originalMember j joint point pointRequest pointCell
    pointLower pointUpper kind visit range
  rw [same] at all
  exact all.2.2

/-- ONE actual release scan retains runtime and all saved fixed-cell frames.
Both associated Read and Write use the existing scalar access theorems. -/
theorem release (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (anchor : UniIndex) (node : TreeNode) (present : role.backing.allocation.extra.nodes.get anchor=some node)
    (concrete : role.family.value.provenance=.concrete role.backing.id node.tag)
    (hidden : node.isExposed=false) (start amount : UInt64)
    (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (positive : start.toNat<(start+amount).toNat) (noWrap : (start+amount).toNat=start.toNat+amount.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra anchor .Write start (start+amount)) :
    let result:=role.backing.allocation.extra.releaseProtector node.tag tracker.global.protectedTags
    result.status=.Released ∧ result.tree={role.backing.allocation.extra with locations:=result.tree.locations} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree tracker.global ∧
      result.tree.locations.size=role.backing.allocation.extra.locations.size ∧
      S05CurrentReleaseIterator.Rows (SavedCells role) result.tree.locations := by
  let P:=fun (range : ByteRange) (location : LocationTree)=>RowRuntime role location ∧ SavedCells role range location
  have initialFrames:=CurrentCallSpatialRows.initial_authority role exclusive
    (by intro segment member;obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member);rw [←same];exact runtime.formed.profile position valid)
    (by intro segment member;obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member);rw [←same];exact runtime.possible position valid)
  have rows : S05CurrentReleaseIterator.Rows P role.backing.allocation.extra.locations:=by
    intro position valid
    exact ⟨⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩,
      role.backing.allocation.extra.locations.entries[position],Array.mem_toList_iff.mpr (Array.getElem_mem valid),rfl,initialFrames _⟩
  have mapped:=runtime.formed.allocator.nodeTags anchor node present
  have sourceAt : CurrentCallSpatialRows.source role=some anchor:=by simp only [CurrentCallSpatialRows.source,concrete,BorrowTree.indexOfTag,mapped]
  have activeRows:=GeneralBorrowFreshActiveWithin.active_on _ _ .Write start (start+amount) runtime.formed.well active
  obtain ⟨done,shape,afterRows,well,ranges,capacity⟩:=S05CurrentReleaseIterator.release role.backing.allocation.extra tracker.global.protectedTags
    node.tag anchor node present hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨lower,upper,_⟩:=activeRows position valid state stored accessed kind associated
      have rowPositive:=(GeneralRangeMapGeometry.facts role.backing.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
      have point : ∃byte,Window role.backing.id offset length byte ∧
          role.backing.allocation.extra.locations.entries[position].range.start.toNat≤byte.2 ∧byte.2<role.backing.allocation.extra.locations.entries[position].range.stop.toNat:=by
        by_cases earlier : start.toNat≤role.backing.allocation.extra.locations.entries[position].range.start.toNat
        · exact ⟨(role.backing.id,role.backing.allocation.extra.locations.entries[position].range.start.toNat),⟨rfl,by omega,by omega⟩,Nat.le_refl _,rowPositive⟩
        · exact ⟨(role.backing.id,start.toNat),⟨rfl,by omega,by omega⟩,by omega,upper⟩
      obtain ⟨byte,inside,low,high⟩:=point
      have member : role.backing.allocation.extra.locations.entries[position]∈role.backing.allocation.extra.locations.entries.toList:=Array.mem_toList_iff.mpr (Array.getElem_mem valid)
      have result:=row_access role exclusive runtime distinct short ⟨role.backing.id,node.tag,concrete⟩
        _ member byte inside low high kind .SkipChildrenOfAccessed role.backing.allocation.extra.locations.entries[position].range
      rw [sourceAt] at result
      exact ⟨result.1,result.2.1,_,member,rfl,result.2.2⟩)
  refine ⟨done,shape,?_,capacity,fun position valid=>(afterRows position valid).2⟩
  rw [shape]
  refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations role.backing.allocation.extra _ runtime.formed.toGraphState,well⟩,?_⟩,
    ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
  · intro position valid;exact ⟨(afterRows position valid).1.2.1.present,(afterRows position valid).1.2.1.vacant⟩
  · intro position valid;exact (afterRows position valid).1.1
  · intro position valid;exact (afterRows position valid).1.2.2

/-- The original Bool cell retains its OWN authority and activity across q
release; its completion is unrelated to q's spatial cell assignment. -/
theorem preserve
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (anchor : UniIndex)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (node : TreeNode) (present : role.backing.allocation.extra.nodes.get anchor=some node)
    (value : role.family.value.provenance=.concrete role.backing.id node.tag)
    (hidden : node.isExposed=false) (start amount : UInt64)
    (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (positive : start.toNat<(start+amount).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra anchor .Write start (start+amount))
    (targetLower targetUpper : UInt64) (targetPositive : targetLower.toNat<targetUpper.toNat)
    (disjoint : (start+amount).toNat≤targetLower.toNat ∨ targetUpper.toNat≤start.toNat)
    (predicate : LocationTree→Prop)
    (owned : OwnedOn predicate targetLower targetUpper role.backing.allocation.extra.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetAt : role.backing.allocation.extra.nodes.get target=some targetNode)
    (targetLeaf : targetNode.children=#[]) (targetHidden : targetNode.isExposed=false) (different : target≠anchor)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra target .Write targetLower targetUpper) :
    let result:=role.backing.allocation.extra.releaseProtector node.tag tracker.global.protectedTags
    OwnedOn predicate targetLower targetUpper result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree target .Write targetLower targetUpper := by
  have concrete : ∃id tag,role.family.value.provenance=.concrete id tag:=⟨role.backing.id,node.tag,value⟩
  have witness (position : Nat) (valid : position<role.backing.allocation.extra.locations.entries.size)
      (lower : role.backing.allocation.extra.locations.entries[position].range.start.toNat<(start+amount).toNat)
      (upper : start.toNat<role.backing.allocation.extra.locations.entries[position].range.stop.toNat) :
      ∃ byte : AllocId × Nat,Window role.backing.id offset length byte ∧
        role.backing.allocation.extra.locations.entries[position].range.start.toNat≤byte.2 ∧
        byte.2<role.backing.allocation.extra.locations.entries[position].range.stop.toNat := by
    have segmentPositive:=(GeneralRangeMapGeometry.facts role.backing.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
    by_cases earlier : start.toNat≤role.backing.allocation.extra.locations.entries[position].range.start.toNat
    · exact ⟨(role.backing.id,role.backing.allocation.extra.locations.entries[position].range.start.toNat),⟨rfl,by omega,by omega⟩,Nat.le_refl _,segmentPositive⟩
    · exact ⟨(role.backing.id,start.toNat),⟨rfl,by omega,by omega⟩,by omega,upper⟩
  let P:=fun (range : ByteRange) (location : LocationTree)=>
    LocationCoherent role.backing.allocation.extra location tracker.global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra location tracker.global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra location ∧
    (range.start.toNat<targetUpper.toNat→targetLower.toNat<range.stop.toNat→predicate location) ∧
    (∀ point : UInt64,range.start.toNat≤point.toNat→point.toNat<range.stop.toNat→∀ state,
      location.perms.get target=some state→state.accessed=true→∀ kind,state.permission.associatedAccess=some kind→
      targetLower.toNat≤point.toNat ∧ point.toNat<targetUpper.toNat)
  have rows : S05CurrentReleaseIterator.Rows P role.backing.allocation.extra.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid,
      (fun lower upper=>owned position valid targetPositive lower upper),by
        intro point lower upper state stored accessed kind associated
        have initial:=targetActive point _ ⟨position,valid,lower,upper,rfl⟩ state stored accessed kind associated
        exact ⟨initial.1,initial.2.1⟩⟩
  have activeRows:=GeneralBorrowFreshActiveWithin.active_on _ _ .Write start (start+amount) runtime.formed.well active
  have mapped:=runtime.formed.allocator.nodeTags anchor node present
  obtain ⟨_,_,afterRows,_,_,_⟩:=S05CurrentReleaseIterator.release role.backing.allocation.extra tracker.global.protectedTags
    node.tag anchor node present hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨lower,upper,_⟩:=activeRows position valid state stored accessed kind associated
      obtain ⟨byte,byteInside,low,high⟩:=witness position valid lower upper
      have member : role.backing.allocation.extra.locations.entries[position]∈role.backing.allocation.extra.locations.entries.toList:=Array.mem_toList_iff.mpr (Array.getElem_mem valid)
      obtain ⟨i,cell⟩:=role.covered byte byteInside
      let overlap : CurrentCallSpatialSourceCover.Active role i:=⟨byte,byteInside,cell⟩
      let W:=CurrentCallSpatialRows.singleByte role i overlap byte byteInside cell
      have localInside:=CurrentCallSpatialRows.singleByte_inside role i overlap byte byteInside cell
      obtain ⟨G⟩:=geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) exclusive
      have sourceAt:=CurrentCallSpatialRows.source_at role i overlap
      simp only [value] at sourceAt
      have sourceAnchor : CurrentCallSpatialRows.source role=some anchor:=by
        simp only [CurrentCallSpatialRows.source,value,BorrowTree.indexOfTag,mapped]
      have grant : W.pointer.grant=anchor:=Option.some.inj (sourceAt.symm.trans sourceAnchor)
      have current:=rows position valid
      have outside : ¬ (role.backing.allocation.extra.locations.entries[position].range.start.toNat < targetUpper.toNat ∧
          targetLower.toNat < role.backing.allocation.extra.locations.entries[position].range.stop.toNat) := by
        have activeAtStart := active role.backing.allocation.extra.locations.entries[position].range.start role.backing.allocation.extra.locations.entries[position].data
          ⟨position,valid,Nat.le_refl _,(GeneralRangeMapGeometry.facts role.backing.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid,rfl⟩
          state stored accessed kind associated
        -- Whole active rows lie inside the anchor interval by pointwise activity.
        have insideStop : role.backing.allocation.extra.locations.entries[position].range.stop.toNat ≤ (start+amount).toNat := by
          by_cases greater : role.backing.allocation.extra.locations.entries[position].range.stop.toNat ≤ (start+amount).toNat
          · exact greater
          have atEnd := active (start+amount) role.backing.allocation.extra.locations.entries[position].data
            ⟨position,valid,by omega,by omega,rfl⟩ state stored accessed kind associated
          omega
        intro overlaps
        rcases disjoint with left | right <;> omega
      have nextActive : ∀ point : UInt64, role.backing.allocation.extra.locations.entries[position].range.start.toNat ≤ point.toNat →
          point.toNat < role.backing.allocation.extra.locations.entries[position].range.stop.toNat → ∀ state,
          (source_access_location (source_tree_access_at role.backing.allocation.extra role.backing.allocation.extra.locations.entries[position].data (some anchor) kind tracker.global.protectedTags
            .SkipChildrenOfAccessed role.backing.allocation.extra.locations.entries[position].range)).perms.get target = some state → state.accessed = true →
          ∀ accessKind, state.permission.associatedAccess = some accessKind → targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat := by
        intro point atStart atStop state afterStored afterAccessed accessKind afterAssociated
        by_cases inside : targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
        · exact inside
        have quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective role.backing.allocation.extra.locations.entries[position].data target targetNode) := by
          cases beforeStored : role.backing.allocation.extra.locations.entries[position].data.perms.get target with
          | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,beforeStored,Option.getD_none,TreeNode.defaultLocationState]
          | some old =>
            simp only [GeneralBorrowWildcardVirtualLeaf.effective,beforeStored,Option.getD_some]
            by_cases cell : old.permission = .Cell
            · exact .inr cell
            · left
              cases h : old.accessed with
              | false => rfl
              | true =>
                have associated : ∃ k,old.permission.associatedAccess = some k := by cases p : old.permission <;> simp_all [Permission.associatedAccess]
                obtain ⟨k,associated⟩ := associated
                exact False.elim (inside (current.2.2.2.2 point atStart atStop old beforeStored h k associated))
        obtain ⟨normal⟩:=CurrentCallResourceAccess.selected_normal W G exclusive byte localInside _ member low high current.2.1 current.2.2.1
        rw [grant] at normal
        have afterQuiet := (S02HiddenLeafQuietTreeAccess.concrete role.backing.allocation.extra runtime.formed.toGraphState role.backing.allocation.extra.locations.entries[position].data tracker.global.protectedTags
          target anchor targetNode node targetAt present targetLeaf targetHidden different normal current.1 kind .SkipChildrenOfAccessed
          role.backing.allocation.extra.locations.entries[position].range quiet).1
        change S02HiddenLeafQuietNormal.Quiet (((source_access_location (source_tree_access_at role.backing.allocation.extra role.backing.allocation.extra.locations.entries[position].data (some anchor) kind tracker.global.protectedTags
          .SkipChildrenOfAccessed role.backing.allocation.extra.locations.entries[position].range)).perms.get target).getD targetNode.defaultLocationState) at afterQuiet
        rw [afterStored] at afterQuiet
        rcases afterQuiet with inactive | cell
        · simp only [Option.getD_some] at inactive;rw [afterAccessed] at inactive;cases inactive
        · simp only [Option.getD_some] at cell;rw [cell,Permission.associatedAccess] at afterAssociated;cases afterAssociated
      cases kind with
      | Read =>
        have result:=CurrentCallResourceRead.concrete_read W G exclusive byte localInside _ member low high concrete distinct current.1 short current.2.1 current.2.2.1
          .SkipChildrenOfAccessed role.backing.allocation.extra.locations.entries[position].range
        rw [grant] at result
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,(fun lower upper=>False.elim (outside ⟨lower,upper⟩)),nextActive⟩
      | Write =>
        have result:=CurrentCallResourceAccess.concrete_write W G exclusive byte localInside _ member low high concrete distinct current.1 short current.2.1 current.2.2.1
          .SkipChildrenOfAccessed role.backing.allocation.extra.locations.entries[position].range
        rw [grant] at result
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,(fun lower upper=>False.elim (outside ⟨lower,upper⟩)),nextActive⟩)
  constructor
  · intro position valid _ lower upper
    exact (afterRows position valid).2.2.2.1 lower upper
  · intro point location atPoint state stored accessed kind associated
    obtain ⟨position,valid,lower,upper,dataEq⟩:=atPoint
    have inside:=(afterRows position valid).2.2.2.2 point lower upper state (by rw [dataEq];exact stored) accessed kind associated
    exact ⟨inside.1,inside.2,by intro impossible;cases impossible⟩


end
end DuplicatePrefix.CurrentCallSpatialProtectorRelease

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialProtectorRelease.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial protector release dependency {dependency}"
