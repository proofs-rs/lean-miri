import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityState
import duplicate_prefix.GeneralBorrowStructuralHistoryGraphOperations
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedConcrete
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryRootAuthorityConcrete
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowStructuralHistoryRootAuthorityAt GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] UniValMap.insert

open GeneralBorrowStructuralHistoryMixedConcrete (Bounded)

/-- Actual concrete mixed-map reservation retains latent owning-root authority,
including active protected children. This asserts neither current-table Write
ownership nor constructor success; raw inside states need only be possible. -/
theorem profile (tree : BorrowTree) (initial : State tree) (root : UniIndex) (rootMember : root∈tree.roots.toList)
    (formed : Profile tree root) (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (initialOutside : outside.isInitial=true) (notUnique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (base : Size) (inside : DedupRangeMap LocationState) (bounded : Bounded inside base tree.locations.size)
    (insidePossible : ∀segment∈inside.iterAll.toList,segment.data.possible=true) :
    let actual := tree.newChild base (.concrete parentTag) tag inside outside held
    root∈actual.tree.roots.toList ∧ Profile actual.tree root := by
  obtain ⟨mapping,index,inserted,parentLookup,graph,growth⟩ := GeneralBorrowStructuralHistoryConcreteAllocator.select tree initial parent parentNode present tag fresh room outside sifa
  have parentTagged : tree.tagMapping.get parentTag=some parent := tagged
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,parentTagged,Option.map_some,initialOutside,notUnique,foreign,Bool.not_true,Id.run,bind,pure]
  have rawLookup : (tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).get parent=some parentNode := by
    simpa only [GeneralBorrowStructuralHistoryConcreteAllocator.node] using parentLookup
  rw [rawLookup]
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_fresh_modify_scan
  have vacant := GeneralBorrowStructuralHistorySifaState.vacant_of_insert tree initial tag fresh room mapping index inserted
  have differentRoot : index≠root := by
    intro same
    obtain ⟨node,found,_⟩:=initial.rootNodes root rootMember
    rw[same,found] at vacant
    cases vacant
  let newNode := GeneralBorrowStructuralHistoryConcreteAllocator.node tag parent outside sifa
  let Good := fun current : BorrowTree =>
    (State current ∧ current.locations.size=tree.locations.size ∧ current.nodes.size≤tree.nodes.size+1) ∧
    (root∈current.roots.toList ∧ Profile current root) ∧ current.nodeAt index=some newNode
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
            have every := GeneralBorrowExposureChildAttach.modify_every (fun location => At current location root)
              current.locations start (Size.ofBytes (segment.range.stop-segment.range.start)) modify currentGood.1.1.well rangeBound currentGood.2.1.2
              (fun range location profile => GeneralBorrowStructuralHistoryRootAuthorityAt.materialize current location root index newNode currentGood.2.2 segment.data profile
                (by simp only [Allowed,GeneralBorrowGcPartitionOwnership.Allowed,differentRoot,ite_false];exact insidePossible segment member))
            have nextEvery : Profile next root := by
              intro position valid
              have data := every position valid
              exact ⟨data.present,data.vacant⟩
            have nextGood : Good next := ⟨⟨geometry.1,geometry.2.trans currentGood.1.2.1,currentGood.1.2.2⟩,⟨currentGood.2.1.1,nextEvery⟩,currentGood.2.2⟩
            cases outcome : changed.outcome with
            | error error =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                stopped next nextGood (.RangeMapError error) (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
            | ok unit =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                yielded next nextGood (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
  let installed := GeneralBorrowStructuralHistoryConcreteAllocator.installed tree mapping index parent parentNode tag outside sifa
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
  have newDefault : Allowed root index newNode.defaultLocationState := by
    simp only [Allowed,GeneralBorrowGcPartitionOwnership.Allowed,differentRoot,ite_false]
    change (false || !outside.isUnique)=true
    rw[notUnique]
    rfl
  have stageEvery : Profile installed root := by
    intro position valid
    change position<tree.locations.entries.size at valid
    have data := GeneralBorrowStructuralHistoryRootAuthorityAt.attach tree tree.locations.entries[position].data root index parent parentNode newNode vacant present
      (formed position valid) newDefault
    exact ⟨data.present,data.vacant⟩
  have stageMember : root∈installed.roots.toList := rootMember
  have initialGood : property (none,installed,sifa) :=
    ⟨⟨⟨⟨graph,initial.well⟩,rfl,growth⟩,⟨stageMember,stageEvery⟩,newPresent⟩,by intro result equal;cases equal⟩
  have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,installed,sifa) initialGood
  dsimp only [installed,GeneralBorrowStructuralHistoryConcreteAllocator.installed,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowStructuralHistoryConcreteAllocator.node] at maintained
  generalize folded : forIn inside.iterAll.toList (none,
    ({tree with tagMapping:=mapping,nodes:=(tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).insert parent {parentNode with children:=parentNode.children.push index}}:BorrowTree),sifa) scan = final at maintained ⊢
  rcases final with ⟨returned,current,minimum⟩
  cases returned with
  | none =>
    have profile := GeneralBorrowStructuralHistoryRootAuthorityAt.sifa current root parent minimum maintained.1.2.1.2
    have roots := GeneralBorrowFreshMetadata.roots current (sourceUpdateSifa current parent minimum).1 (GeneralBorrowSifaView.preserves current parent minimum)
    have member : root∈(sourceUpdateSifa current parent minimum).1.roots.toList := by rw[roots];exact maintained.1.2.1.1
    cases actual : sourceUpdateSifa current parent minimum with
    | mk next outcome => simpa only [actual] using And.intro member profile
  | some result => exact (maintained.2 result rfl).2.1

end DuplicatePrefix.GeneralBorrowStructuralHistoryRootAuthorityConcrete
