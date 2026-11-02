import duplicate_prefix.GeneralBorrowStructuralHistorySifaInsert
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcardAllocator
import duplicate_prefix.GeneralBorrowStructuralHistoryGraphOperations
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedWildcard
namespace DuplicatePrefix.GeneralBorrowStructuralHistorySifaWildcard
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowLocationSifaConsistency GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] UniValMap.insert

open GeneralBorrowStructuralHistoryMixedWildcard (Bounded)

/-- Arbitrary inside permission maps retain structural State through the real
wildcard constructor. Raw outside checks and segment bounds ensure allocation
and partition structure; inside permission errors remain actual error results. -/
theorem profile (tree : BorrowTree) (initial : State tree) (protections : ProtectedTags)
    (formed : Every (fun location => Profile tree location protections) tree.locations) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (initialOutside : outside.isInitial=true) (notUnique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (aligned : protections.contains tag=held)
    (base : Size) (inside : DedupRangeMap LocationState) (bounded : Bounded inside base tree.locations.size)
    (insideConsistent : ∀segment∈inside.iterAll.toList,
      GeneralBorrowSifaPermissionConsistency.Consistent segment.data (protections.contains tag)) :
    let actual := tree.newChild base .wildcard tag inside outside held
    Every (fun location => Profile actual.tree location protections) actual.tree.locations := by
  obtain ⟨mapping,index,inserted,graph,growth⟩ := GeneralBorrowStructuralHistoryWildcardAllocator.select tree initial.toGraphState tag fresh room outside sifa
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,initialOutside,notUnique,foreign,Bool.not_true,Id.run,bind,pure,←Array.forIn_toList]
  name_fresh_modify_scan
  let newNode := WildcardHitZeroConstructor.rootNode tag outside sifa
  let Good := fun current : BorrowTree =>
    (State current ∧ current.locations.size=tree.locations.size ∧ current.nodes.size≤tree.nodes.size+1) ∧
    Every (fun location => Profile current location protections) current.locations ∧ current.nodeAt index=some newNode
  let property := fun current : Option BorrowTree.ChildInsertResult × BorrowTree × IdempotentForeignAccess =>
    Good current.2.1 ∧ ∀result,current.1=some result→Good result.tree
  have step : ∀segment∈inside.iterAll.toList,∀current,property current→property (scan segment current).value := by
    intro segment member current good
    rcases current with ⟨returned,current,minimum⟩
    have currentGood : Good current := good.1
    have stopped : ∀next,Good next→∀error minimum,property (some ({tree:=next,outcome:=.error error}:BorrowTree.ChildInsertResult),next,minimum) := by
      intro next valid error minimum
      refine ⟨valid,?_⟩
      intro result equal
      have same := Option.some.inj equal
      subst result
      exact valid
    have yielded : ∀next,Good next→∀minimum,property (none,next,minimum) := by
      intro next valid minimum
      exact ⟨valid,by intro result equal;cases equal⟩
    cases init : segment.data.permission.isInitial with
    | false => simpa only [scan,init,Bool.not_false,↓reduceIte,ForInStep.value] using stopped current currentGood (.InsidePermissionNotInitial _) minimum
    | true =>
      cases expected : segment.data.permission.strongestIdempotentForeignAccess held with
      | ImpossibleProtectedReservedIM =>
        simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,ForInStep.value] using stopped current currentGood (.InsidePermissionInvariant _) minimum
      | Access expectedSifa =>
        cases mismatch : (segment.data.idempotentForeignAccess != expectedSifa) with
        | true =>
          simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,ForInStep.value] using stopped current currentGood (.InsideSifaMismatch _) minimum
        | false =>
          cases added : (Size.ofBytes segment.range.start).add base with
          | error error =>
            simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,ForInStep.value] using
              stopped current currentGood (.SizeError error) (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
          | ok start =>
            have rangeBound := bounded segment member start added
            rw [←currentGood.1.2.1] at rangeBound
            let modify := fun (_ : ByteRange) (location : LocationTree) => {location with perms:=location.perms.insert index segment.data}
            let changed := current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify
            let next := {current with locations:=changed.state}
            have geometry := GeneralBorrowStructuralHistoryGraphOperations.modify_range current currentGood.1.1 start
              (Size.ofBytes (segment.range.stop-segment.range.start)) modify rangeBound
            have every := GeneralBorrowExposureChildAttach.modify_every (fun location => Profile current location protections)
              current.locations start (Size.ofBytes (segment.range.stop-segment.range.start)) modify currentGood.1.1.well rangeBound currentGood.2.1
              (fun range location profile => GeneralBorrowConstructorSifaProfile.materialize current location protections index newNode currentGood.2.2 segment.data profile
                (by simpa only [newNode,WildcardHitZeroConstructor.rootNode] using insideConsistent segment member))
            have nextEvery : Every (fun location => Profile next location protections) next.locations := by
              intro position valid
              have data := every position valid
              exact ⟨data.present,data.vacant⟩
            have nextGood : Good next := ⟨⟨geometry.1,geometry.2.trans currentGood.1.2.1,currentGood.1.2.2⟩,nextEvery,currentGood.2.2⟩
            cases outcome : changed.outcome with
            | error error =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                stopped next nextGood (.RangeMapError error) (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
            | ok unit =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                yielded next nextGood (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
  let installed := WildcardHitZeroConstructor.installed tree mapping index tag outside sifa
  have vacant := GeneralBorrowStructuralHistorySifaState.vacant_of_insert tree initial tag fresh room mapping index inserted
  have newPresent : installed.nodeAt index=some newNode := by
    exact GeneralBorrowFreshLocation.get_same tree.nodes index newNode
  have newDefault : GeneralBorrowSifaPermissionConsistency.Consistent newNode.defaultLocationState (protections.contains tag) := by
    refine ⟨sifa,?_,Nat.le_refl _⟩
    change outside.strongestIdempotentForeignAccess (protections.contains tag)=.Access sifa
    rw [aligned]
    exact foreign
  have stageEvery : Every (fun location => Profile installed location protections) installed.locations := by
    intro position valid
    change position<tree.locations.entries.size at valid
    have data := GeneralBorrowStructuralHistorySifaInsert.insert tree tree.locations.entries[position].data protections index newNode vacant
      (formed position valid) newDefault
    exact ⟨data.present,data.vacant⟩
  have initialGood : property (none,installed,sifa) :=
    ⟨⟨⟨⟨graph,initial.well⟩,rfl,growth⟩,stageEvery,newPresent⟩,by intro result equal;cases equal⟩
  have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,installed,sifa) initialGood
  dsimp only [installed,WildcardHitZeroConstructor.installed,WildcardHitZeroConstructor.rootNode] at maintained
  generalize folded : forIn inside.iterAll.toList (none,
    ({tree with tagMapping:=mapping,nodes:=tree.nodes.insert index ⟨tag,none,#[],outside,sifa,false,none⟩,roots:=tree.roots.push index}:BorrowTree),sifa) scan = final at maintained ⊢
  rcases final with ⟨returned,current,minimum⟩
  cases returned with
  | none => exact maintained.1.2.1
  | some result => exact (maintained.2 result rfl).2.1

end DuplicatePrefix.GeneralBorrowStructuralHistorySifaWildcard
