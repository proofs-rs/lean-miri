import duplicate_prefix.GeneralBorrowExposedKnownRootRangeData
import duplicate_prefix.GeneralBorrowFreshReleaseMixed
namespace DuplicatePrefix.GeneralBorrowExposedScopedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open GeneralBorrowExposedKnownRootRangeData (Data)
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The actual protector-end callbacks complete and retain the whole scoped
Read contract, including mixed mutable ancestors. Other roots may be exposed. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (kind : AccessKind) (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (notExposed : context.anchorNode.isExposed = false)
    (tagPresent : tree.indexOfTag tag = some anchor) (active : ActiveOn tree anchor kind lower upper)
    (matching : ∀ position (valid : position<tree.locations.entries.size) state,
      tree.locations.entries[position].data.perms.get anchor=some state → state.accessed=true →
      ∀ associated,state.permission.associatedAccess=some associated → associated=kind)
    (owned : OwnedOn (fun location => Nonempty (Data tree location protections anchor selected head tail kind))
      lower upper tree.locations) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} := by
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,?_⟩
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
          have profile := active position oldValid before stored accessed accessKind associated
          have readOnly : accessKind = kind := matching position oldValid before stored accessed accessKind associated
          subst accessKind
          have here := owned position oldValid positive profile.1 profile.2.1
          obtain ⟨data⟩ := here
          have succeeded := GeneralBorrowExposedKnownRootRangeData.access tree
            (tree.locations.entries[position]'oldValid).data protections anchor selected head tail kind .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range context data
          let access := source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
            kind protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size :=
            setAtPos_length map position currentValid (source_access_location access)
          have actual : scan position (none,{tree with locations := map}) =
              .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,succeeded.1]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,
            (setAtPos_length map position currentValid _).trans sizeEq,?_⟩
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro equal;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag tag = some anchor := tagPresent
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some context.anchorNode := context.anchorPresent
  simp only [lookup,nodeLookup,notExposed,Bool.not_false,↓reduceIte,Id.run,pure]
  exact ⟨True.intro,True.intro⟩

end DuplicatePrefix.GeneralBorrowExposedScopedRelease
