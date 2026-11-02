import duplicate_prefix.GeneralBorrowConcreteRowReadRange
import duplicate_prefix.S02HiddenLeafQuietTreeAccess
namespace DuplicatePrefix.S02HiddenLeafActiveReleaseScan
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

private theorem row_within (map : DedupRangeMap LocationTree) (anchor : UniIndex) (ownerKind : AccessKind)
    (lower upper : UInt64) (well : map.WellFormed) (active : Profile map anchor ownerKind lower upper)
    (position : Nat) (valid : position < map.entries.size) (state : LocationState)
    (stored : map.entries[position].data.perms.get anchor = some state) (accessed : state.accessed = true)
    (kind : AccessKind) (associated : state.permission.associatedAccess = some kind) :
    lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat := by
  have positive := (GeneralRangeMapGeometry.facts map well (by omega)).2.1 position valid
  have first := active map.entries[position].range.start map.entries[position].data
    ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored accessed kind associated
  refine ⟨first.1,?_⟩
  by_cases outside : map.entries[position].range.stop.toNat ≤ upper.toNat
  · exact outside
  · have last := active upper map.entries[position].data
      ⟨position,valid,by omega,by omega,rfl⟩ state stored accessed kind associated
    omega

private theorem replace_write (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (inside : lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    exact ⟨Nat.le_trans inside.1 startPoint,Nat.lt_of_lt_of_le pointStop inside.2,by intro h;cases h⟩
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by
      simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

private theorem replaced_owned_on (predicate : LocationTree → Prop) (lower upper : UInt64)
    (map : DedupRangeMap LocationTree) (position : Nat) (valid : position < map.entries.size) (data : LocationTree)
    (owned : OwnedOn predicate lower upper map) (newOwned : predicate data) :
    OwnedOn predicate lower upper (replaced map position valid data) := by
  intro index bounded positive beforeUpper afterLower
  have oldBound : index < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid data index oldBound] at beforeUpper afterLower
  by_cases same : position = index
  · subst index
    simpa [replaced] using newOwned
  · have previous := owned index oldBound positive beforeUpper afterLower
    simpa [replaced,Array.getElem_set,same] using previous

private theorem quiet_outside (tree : BorrowTree) (target : UniIndex) (node : TreeNode)
    (lower upper point : UInt64) (location : LocationTree)
    (active : ActiveWithin tree target .Write lower upper)
    (atPoint : ValueAt tree.locations point location)
    (outside : ¬ (lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat)) :
    S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective location target node) := by
  cases stored : location.perms.get target with
  | none => left; simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_none,TreeNode.defaultLocationState]
  | some state =>
    simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some]
    by_cases accessed : state.accessed = true
    · cases associated : state.permission.associatedAccess with
      | none =>
        right
        cases permission : state.permission <;> simp_all [Permission.associatedAccess]
      | some kind =>
        have within := active point location atPoint state stored accessed kind associated
        exact False.elim (outside ⟨within.1,within.2.1⟩)
    · left; cases h : state.accessed <;> simp_all

/-- The real release scan executes each real associated Read or Write callback confined by the fresh
child's current activity window. Every row visitor is derived from Both Row. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor selected : UniIndex)
    (maximum : Option BorTag) (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) (notExposed : anchorNode.isExposed = false)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write lower upper)
    (well : tree.locations.WellFormed)
    (runtime : Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree protections) tree.locations)
    (owned : OwnedOn (GeneralBorrowConcreteRowReadRange.Row tree protections anchor selected maximum) lower upper tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (targetLeaf : targetNode.children = #[]) (targetHidden : targetNode.isExposed = false)
    (different : target ≠ anchor) (targetLower targetUpper : UInt64)
    (targetActive : ActiveWithin tree target .Write targetLower targetUpper) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      OwnedOn (GeneralBorrowConcreteRowReadRange.Row result.tree protections anchor selected maximum) lower upper result.tree.locations ∧
      Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime result.tree protections) result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree anchor .Write lower upper ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size ∧
      ActiveWithin result.tree target .Write targetLower targetUpper := by
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree anchor .Write lower upper well active
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := GeneralBorrowConcreteRowReadRange.Row tree protections anchor selected maximum
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      OwnedOn predicate lower upper map ∧
      Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree protections) map ∧ GeneralBorrowFreshActiveWithin.Profile map anchor .Write lower upper ∧ map.WellFormed ∧
      map.entries.map (·.range) = tree.locations.entries.map (·.range) ∧
      Profile map target .Write targetLower targetUpper ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapRuntime,mapActive,mapWell,mapRanges,mapTargetActive,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapOwned,mapRuntime,mapActive,mapWell,mapRanges,mapTargetActive,?_⟩
      intro other member
      exact untouched other (by simp [member])
    cases stored : (tree.locations.entries[position]'oldValid).data.perms.get anchor with
    | none =>
      refine ⟨(none,{tree with locations := map}),?_,skipped⟩
      simp only [scan,index_exact map position currentValid,same,stored]
    | some before =>
      cases associated : before.permission.associatedAccess with
      | none =>
        refine ⟨(none,{tree with locations := map}),?_,skipped⟩
        simp only [scan,index_exact map position currentValid,same,stored,associated]
      | some accessKind =>
        cases accessed : before.accessed with
        | false =>
          refine ⟨(none,{tree with locations := map}),?_,skipped⟩
          simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,Bool.false_eq_true,↓reduceIte]
        | true =>
          have profile := activeRows position oldValid before stored accessed accessKind associated
          have here := owned position oldValid positive profile.1 profile.2.1
          have succeeded := GeneralBorrowConcreteRowReadRange.location_kind tree protections formed anchor selected anchorNode anchorPresent
            maximum accessKind (tree.locations.entries[position]'oldValid).data here distinct order
            (runtime position oldValid) short .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let access := source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
            accessKind protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size :=
            setAtPos_length map position currentValid (source_access_location access)
          have actual : scan position (none,{tree with locations := map}) =
              .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,succeeded.1]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,
            (setAtPos_length map position currentValid _).trans sizeEq,?_,?_,?_,?_,?_,?_,?_⟩
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_owned_on predicate lower upper map position currentValid _ mapOwned succeeded.2.1
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_every _ map position currentValid _ mapRuntime succeeded.2.2.1
          · have inside := row_within tree.locations anchor .Write lower upper well active position oldValid before stored accessed accessKind associated
            have currentInside : lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat := by
              rw [same]
              exact inside
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replace_write map position currentValid _ anchor lower upper mapActive currentInside
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_wellFormed map position currentValid _ mapWell
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact (replaced_ranges map position currentValid _).trans mapRanges
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            intro point location atPoint state storedTarget accessedTarget kindTarget associatedTarget
            obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
            have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
            rw [replaced_range map position currentValid _ query oldBound] at startPoint pointStop
            by_cases sameQuery : position = query
            · subst query
              by_cases insideTarget : targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
              · exact ⟨insideTarget.1,insideTarget.2,by intro h;cases h⟩
              · have originalPoint : ValueAt tree.locations point tree.locations.entries[position].data := by
                  refine ⟨position,oldValid,?_,?_,rfl⟩
                  · rw [same] at startPoint;exact startPoint
                  · rw [same] at pointStop;exact pointStop
                have quiet := quiet_outside tree target targetNode targetLower targetUpper point _ targetActive originalPoint insideTarget
                obtain ⟨row⟩ := here
                obtain ⟨normal⟩ := row.normal anchor rfl
                have transferred := (S02HiddenLeafQuietTreeAccess.concrete tree formed _ protections target anchor targetNode anchorNode
                  targetPresent anchorPresent targetLeaf targetHidden different normal (runtime position oldValid).coherent
                  accessKind .SkipChildrenOfAccessed tree.locations.entries[position].range quiet).1
                have outputSame : location = source_access_location access := by
                  simpa only [replaced,Array.getElem_set_self] using dataEq.symm
                rw [outputSame] at storedTarget
                have effective : GeneralBorrowWildcardVirtualLeaf.effective (source_access_location access) target targetNode = state := by
                  simp only [GeneralBorrowWildcardVirtualLeaf.effective,storedTarget,Option.getD_some]
                change S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective (source_access_location access) target targetNode) at transferred
                rw [effective] at transferred
                rcases transferred with inactive | cell
                · rw [inactive] at accessedTarget;cases accessedTarget
                · rw [cell,Permission.associatedAccess] at associatedTarget;cases associatedTarget
            · have dataSame : (replaced map position currentValid (source_access_location access)).entries[query].data = map.entries[query].data := by
                simp only [replaced,Array.getElem_set,sameQuery,↓reduceIte]
              rw [dataSame] at dataEq
              exact mapTargetActive point location ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state storedTarget accessedTarget kindTarget associatedTarget
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro equal;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,owned,runtime,active,well,rfl,targetActive,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapRuntime,mapActive,mapWell,mapRanges,mapTargetActive,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag tag = some anchor := tagPresent
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some anchorNode := anchorPresent
  simp only [lookup,nodeLookup,notExposed,Bool.not_false,↓reduceIte,Id.run,pure]
  have capacity : map.size = tree.locations.size := by
    rw [size_from_ranges,mapRanges,←size_from_ranges]
  refine ⟨True.intro,True.intro,?_,?_,mapActive,mapWell,capacity,mapTargetActive⟩
  · intro position valid positive start stop
    exact GeneralBorrowConcreteRowReadRange.row_locations tree map _ protections anchor selected maximum
      (mapOwned position valid positive start stop)
  · intro position valid
    exact GeneralBorrowSnapshotWildcardRangeBoth.runtime_locations tree map _ protections (mapRuntime position valid)

end DuplicatePrefix.S02HiddenLeafActiveReleaseScan

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02HiddenLeafActiveReleaseScan.release) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved hidden leaf active release dependency {dependency}"
