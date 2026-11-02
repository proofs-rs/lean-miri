import duplicate_prefix.GeneralBorrowStructuralHistoryActivityGenericRange
import duplicate_prefix.GeneralBorrowStructuralHistoryGraphOperations
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedConcrete
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryActivityGenericConcrete
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowLocationSifaConsistency GeneralRangeMapState GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] UniValMap.insert

open GeneralBorrowStructuralHistoryMixedConcrete (Bounded)

def Window (inside : DedupRangeMap LocationState) (base : Size) (lower upper : UInt64) : Prop :=
  ∀segment∈inside.iterAll.toList,∀start,(Size.ofBytes segment.range.start).add base=.ok start →
    lower.toNat≤start.bytes.toNat ∧ (start.bytes+(segment.range.stop-segment.range.start)).toNat≤upper.toNat


/-- Initial physical SIFA/vacancy formation and raw inside-segment windows
form the actual new child's bytewise activity confinement. No incoming or final
activity certificate or successful constructor outcome is supplied. -/
theorem form (tree : BorrowTree) (initial : State tree) (protections : ProtectedTags)
    (formed : Every (fun location => Profile tree location protections) tree.locations) (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (initialOutside : outside.isInitial=true) (notUnique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (base : Size) (inside : DedupRangeMap LocationState) (bounded : Bounded inside base tree.locations.size)
    (ownerKind : AccessKind) (lower upper : UInt64)
    (window : Window inside base lower upper)
    (readOnly : ownerKind=.Read→∀segment∈inside.iterAll.toList,segment.data.accessed=true→∀kind,segment.data.permission.associatedAccess=some kind→kind=.Read) :
    let actual := tree.newChild base (.concrete parentTag) tag inside outside held
    ∃index,actual.tree.tagMapping.get tag=some index ∧ ActiveWithin actual.tree index ownerKind lower upper := by
  obtain ⟨mapping,index,inserted,parentLookup,graph,growth⟩ := GeneralBorrowStructuralHistoryConcreteAllocator.select tree initial parent parentNode present tag fresh room outside sifa
  refine ⟨index,?_⟩
  have parentTagged : tree.tagMapping.get parentTag=some parent := tagged
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,parentTagged,Option.map_some,initialOutside,notUnique,foreign,Bool.not_true,Id.run,bind,pure]
  have rawLookup : (tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).get parent=some parentNode := by
    simpa only [GeneralBorrowStructuralHistoryConcreteAllocator.node] using parentLookup
  rw [rawLookup]
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_fresh_modify_scan
  let newNode := GeneralBorrowStructuralHistoryConcreteAllocator.node tag parent outside sifa
  let Good := fun current : BorrowTree =>
    (State current ∧ current.locations.size=tree.locations.size ∧ current.nodes.size≤tree.nodes.size+1) ∧
    ActiveWithin current index ownerKind lower upper ∧ current.nodeAt index=some newNode
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
            have confined := window segment member start added
            have nextActive := GeneralBorrowStructuralHistoryActivityGenericRange.materialize current index segment.data ownerKind lower upper start
              (Size.ofBytes (segment.range.stop-segment.range.start)) currentGood.1.1.well rangeBound confined.1 confined.2 currentGood.2.1
              (fun mode accessed kind associated=>readOnly mode segment member accessed kind associated)
            have nextGood : Good next := ⟨⟨geometry.1,geometry.2.trans currentGood.1.2.1,currentGood.1.2.2⟩,nextActive,currentGood.2.2⟩
            cases outcome : changed.outcome with
            | error error =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                stopped next nextGood (.RangeMapError error) (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
            | ok unit =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                yielded next nextGood (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
  let installed := GeneralBorrowStructuralHistoryConcreteAllocator.installed tree mapping index parent parentNode tag outside sifa
  have vacant := GeneralBorrowStructuralHistorySifaState.vacant_of_insert tree initial tag fresh room mapping index inserted
  have different : index≠parent := by
    intro same
    rw [same] at vacant
    rw [show tree.nodes.get parent=some parentNode from present] at vacant
    cases vacant
  have newPresent : installed.nodeAt index=some newNode := by
    simpa only [installed,GeneralBorrowStructuralHistoryConcreteAllocator.installed,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,BorrowTree.nodeAt,newNode] using
      (GeneralBorrowFreshLocation.get_other (tree.nodes.insert index newNode) parent index
        {parentNode with children:=parentNode.children.push index} different).trans (GeneralBorrowFreshLocation.get_same tree.nodes index newNode)
  have initialActive : ActiveWithin installed index ownerKind lower upper := by
    apply GeneralBorrowStructuralHistoryActivityGenericRange.clean
    intro position valid
    exact (formed position valid).vacant index vacant
  have initialGood : property (none,installed,sifa) :=
    ⟨⟨⟨⟨graph,initial.well⟩,rfl,growth⟩,initialActive,newPresent⟩,by intro result equal;cases equal⟩
  have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,installed,sifa) initialGood
  dsimp only [installed,GeneralBorrowStructuralHistoryConcreteAllocator.installed,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowStructuralHistoryConcreteAllocator.node] at maintained
  generalize folded : forIn inside.iterAll.toList (none,
    ({tree with tagMapping:=mapping,nodes:=(tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).insert parent {parentNode with children:=parentNode.children.push index}}:BorrowTree),sifa) scan = final at maintained ⊢
  rcases final with ⟨returned,current,minimum⟩
  cases returned with
  | none =>
    have nextState := (GeneralBorrowStructuralHistoryGraphOperations.sifa current maintained.1.1.1 parent minimum).1
    have shape := GeneralBorrowSifaView.preserves current parent minimum
    obtain ⟨node,present,tagged,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields current _ shape index newNode maintained.1.2.2
    have mapped := nextState.allocator.nodeTags index node present
    rw [tagged] at mapped
    change (sourceUpdateSifa current parent minimum).1.tagMapping.get tag=some index at mapped
    have active := GeneralBorrowFreshActiveWithin.sifa_preserves current parent minimum index ownerKind lower upper maintained.1.2.1
    cases actual : sourceUpdateSifa current parent minimum with
    | mk next outcome => simpa only [actual] using And.intro mapped active
  | some result =>
    have good := maintained.2 result rfl
    have mapped := good.1.1.allocator.nodeTags index newNode good.2.2
    exact ⟨mapped,good.2.1⟩

end DuplicatePrefix.GeneralBorrowStructuralHistoryActivityGenericConcrete
