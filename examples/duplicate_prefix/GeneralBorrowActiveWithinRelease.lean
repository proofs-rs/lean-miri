import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
namespace DuplicatePrefix.GeneralBorrowActiveWithinRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowFreshReleaseLoop
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowStructuralReleaseGeometryFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private theorem replace_confined (map : DedupRangeMap LocationTree) (position : Nat) (valid : position<map.entries.size)
    (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (inside : ∀point : UInt64,map.entries[position].range.start.toNat≤point.toNat→point.toNat<map.entries[position].range.stop.toNat→
      lower.toNat≤point.toNat ∧ point.toNat<upper.toNat) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩:=atPoint
  have oldBound : query<map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position=query
  · subst query
    exact ⟨(inside point startPoint pointStop).1,(inside point startPoint pointStop).2,by intro impossible;cases impossible⟩
  · have dataSame : (replaced map position valid location).entries[query].data=map.entries[query].data := by
      simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

/-- Every actual helper-release callback stays in its source-formed window.
Replacing that row therefore preserves an older mutable target's outside
inactivity, even on early access failure. No callback success is assumed. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (helper target : UniIndex)
    (node : TreeNode) (tagPresent : tree.indexOfTag tag=some helper) (present : tree.nodeAt helper=some node)
    (hidden : node.isExposed=false) (lower upper : UInt64)
    (helperActive : ActiveWithin tree helper .Write lower upper)
    (targetActive : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.releaseProtector tag protections).tree target .Write lower upper := by
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let invariant := fun current : BorrowTree=> Frame tree current ∧ current.locations.entries.size=tree.locations.entries.size ∧
    ActiveWithin current helper .Write lower upper ∧ ActiveWithin current target .Write lower upper
  let property := fun state : Option BorrowTree.ProtectorReleaseResult × BorrowTree=>
    invariant state.2 ∧ ∀returned,state.1=some returned→invariant returned.tree
  have step : ∀position∈List.range' 0 tree.locations.entries.size,∀state,property state→property (scan position state).value := by
    intro position member state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨currentGood,returnedGood⟩
    have valid : position<current.locations.entries.size := by
      rw [currentGood.2.1]
      have bounded:=List.mem_range'_1.mp member;omega
    have skipped : property (none,current) := ⟨currentGood,by simp⟩
    cases stored : current.locations.entries[position].data.perms.get helper with
    | none=>simpa only [scan,index_exact current.locations position valid,stored,ForInStep.value] using skipped
    | some before=>
      cases associated : before.permission.associatedAccess with
      | none=>simpa only [scan,index_exact current.locations position valid,stored,associated,ForInStep.value] using skipped
      | some accessKind=>
        cases accessed : before.accessed with
        | false=>simpa only [scan,index_exact current.locations position valid,stored,associated,accessed,Bool.false_eq_true,↓reduceIte,ForInStep.value] using skipped
        | true=>
          have inside : ∀point : UInt64,current.locations.entries[position].range.start.toNat≤point.toNat→
              point.toNat<current.locations.entries[position].range.stop.toNat→lower.toNat≤point.toNat ∧ point.toNat<upper.toNat := by
            intro point start stop
            have owned:=currentGood.2.2.1 point current.locations.entries[position].data ⟨position,valid,start,stop,rfl⟩ before stored accessed accessKind associated
            exact ⟨owned.1,owned.2.1⟩
          let access:=source_tree_access_at current current.locations.entries[position].data (some helper) accessKind protections .SkipChildrenOfAccessed current.locations.entries[position].range
          let next : BorrowTree:={current with locations:=(current.locations.setAtPos position (source_access_location access)).state}
          have nextGood : invariant next := by
            refine ⟨?_,?_,?_,?_⟩
            · dsimp only [next,Frame]
              rw [show current={tree with locations:=current.locations} from currentGood.1]
            · exact (setAtPos_length current.locations position valid _).trans currentGood.2.1
            · change Profile (current.locations.setAtPos position (source_access_location access)).state helper .Write lower upper
              rw [setAtPos_exact current.locations position valid]
              exact replace_confined _ _ valid _ helper lower upper currentGood.2.2.1 inside
            · change Profile (current.locations.setAtPos position (source_access_location access)).state target .Write lower upper
              rw [setAtPos_exact current.locations position valid]
              exact replace_confined _ _ valid _ target lower upper currentGood.2.2.2 inside
          cases failure : source_access_status access
          · have nextProperty : property (none,next) := ⟨nextGood,by simp⟩
            simpa only [scan,index_exact current.locations position valid,stored,associated,accessed,↓reduceIte,
              setAtPos_success current.locations position valid,failure,ForInStep.value,next,access] using nextProperty
          · rename_i error
            have nextProperty : property (some ⟨next,.AccessFailure current.locations.entries[position].range error⟩,next) := by
              exact ⟨nextGood,fun result same=>by cases same;exact nextGood⟩
            simpa only [scan,index_exact current.locations position valid,stored,associated,accessed,↓reduceIte,
              setAtPos_success current.locations position valid,failure,ForInStep.value,next,access] using nextProperty
  have initial : property (none,tree) := ⟨⟨rfl,rfl,helperActive,targetActive⟩,by simp⟩
  have final:=GeneralBorrowLoop.list_invariant _ scan property step _ initial
  split
  · exact (final.2 _ (by assumption)).2.2.2
  · have currentGood:=final.1
    have sameTag : (forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2.indexOfTag tag=some helper := by
      rw [show (forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2={tree with locations:=(forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2.locations} from currentGood.1]
      exact tagPresent
    have sameNode : (forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2.nodeAt helper=some node := by
      rw [show (forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2={tree with locations:=(forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2.locations} from currentGood.1]
      exact present
    unfold BorrowTree.updateExposureForProtectorRelease
    simp only [sameTag,sameNode,hidden,Bool.not_false,↓reduceIte,Id.run,pure]
    exact currentGood.2.2.2
end DuplicatePrefix.GeneralBorrowActiveWithinRelease
