import duplicate_prefix.GeneralBorrowForestTagHighWaterCtorFrame
import duplicate_prefix.GeneralBorrowStructuralHistoryConcreteAllocator
namespace DuplicatePrefix.GeneralBorrowForestTagHighWaterConcreteFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestTagHighWater GeneralBorrowStructuralHistoryState GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual mixed concrete construction retains its selected mapping through
all source inside-error/range-error branches and the final real ancestor SIFA. -/
theorem mapping (tree : BorrowTree) (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (inserted : tree.tagMapping.insert tag=.Inserted mapping index)
    (tagged : tree.indexOfTag parentTag=some parent)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (parentLookup : (tree.nodes.insert index (GeneralBorrowStructuralHistoryConcreteAllocator.node tag parent outside sifa)).get parent=some parentNode)
    (initialOutside : outside.isInitial=true) (notUnique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (base : Size) (inside : DedupRangeMap LocationState) :
    (tree.newChild base (.concrete parentTag) tag inside outside held).tree.tagMapping=mapping := by
  have parentTagged : tree.tagMapping.get parentTag=some parent := tagged
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,parentTagged,Option.map_some,initialOutside,notUnique,foreign,Bool.not_true,Id.run,bind,pure]
  have rawLookup : (tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).get parent=some parentNode := by
    simpa only [GeneralBorrowStructuralHistoryConcreteAllocator.node] using parentLookup
  rw [rawLookup]
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_fresh_modify_scan
  let Good := fun current : BorrowTree => current.tagMapping=mapping
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
            let modify := fun (_ : ByteRange) (location : LocationTree) => {location with perms:=location.perms.insert index segment.data}
            let changed := current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify
            let next := {current with locations:=changed.state}
            have nextGood : Good next := currentGood
            cases outcome : changed.outcome with
            | error error =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                stopped next nextGood (.RangeMapError error) (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
            | ok unit =>
              simpa only [scan,init,Bool.not_true,Bool.false_eq_true,↓reduceIte,expected,mismatch,added,changed,modify,outcome,ForInStep.value] using
                yielded next nextGood (source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
  let installed := GeneralBorrowStructuralHistoryConcreteAllocator.installed tree mapping index parent parentNode tag outside sifa
  have initialGood : property (none,installed,sifa) :=
    ⟨rfl,by intro result equal;cases equal⟩
  have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,installed,sifa) initialGood
  dsimp only [installed,GeneralBorrowStructuralHistoryConcreteAllocator.installed,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowStructuralHistoryConcreteAllocator.node] at maintained
  generalize folded : forIn inside.iterAll.toList (none,
    ({tree with tagMapping:=mapping,nodes:=(tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).insert parent {parentNode with children:=parentNode.children.push index}}:BorrowTree),sifa) scan = final at maintained ⊢
  rcases final with ⟨returned,current,minimum⟩
  cases returned with
  | none =>
    exact (GeneralBorrowFreshMetadata.mapping current (sourceUpdateSifa current parent minimum).1
      (GeneralBorrowSifaView.preserves current parent minimum)).trans maintained.1
  | some result => exact maintained.2 result rfl
private theorem inserted_bound (tree : BorrowTree) (initial : GraphState tree) (tag : BorTag)
    (protections : ProtectedTags) (counter : BorTag) (below : Below tree protections counter)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (inserted : tree.tagMapping.insert tag=.Inserted mapping index)
    (newBound : tag.value.toNat<counter.value.toNat) :
    ∀row∈mapping.mapping,row.1.value.toNat<counter.value.toNat := by
  have pushBound : ∀(chosen : UniIndex) (free : Array UniIndex),
      ∀row∈(⟨tree.tagMapping.mapping.push (tag,chosen),free⟩ : UniKeyMap BorTag).mapping,
        row.1.value.toNat<counter.value.toNat := by
    intro chosen free row member
    rcases Array.mem_push.mp member with old | same
    · exact below.mapping row old
    · subst row;exact newBound
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree initial.allocator.accounting available
    have fits : tree.tagMapping.mapping.size≤4294967295 := by change tree.nodes.data.size+1≤_ at room;omega
    have actual := GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh available fits
    have equal := UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)
    rw [←equal.1]
    exact pushBound _ _
  | some chosen =>
    have actual := GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh chosen available
    have equal := UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)
    rw [←equal.1]
    exact pushBound _ _

/-- Concrete newChild's returned mapping preserves the raw high-water data,
including actual partial inside/range/SIFA error outcomes. Success is separate. -/
theorem concrete (tree : BorrowTree) (initial : State tree) (protections : ProtectedTags) (counter : BorTag)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode) (tag : BorTag)
    (below : Below tree protections counter) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+1≤4294967295) (newBound : tag.value.toNat<counter.value.toNat)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (initialOutside : outside.isInitial=true) (notUnique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (base : Size) (inside : DedupRangeMap LocationState) :
    Below (tree.newChild base (.concrete parentTag) tag inside outside held).tree protections counter := by
  obtain ⟨allocated,index,inserted,parentLookup,_,_⟩ := GeneralBorrowStructuralHistoryConcreteAllocator.select tree initial parent parentNode present tag fresh room outside sifa
  have tagMap := mapping tree parentTag parent parentNode tag allocated index inserted tagged outside sifa held parentLookup initialOutside notUnique foreign base inside
  refine ⟨?_,below.protectors⟩
  rw [tagMap]
  exact inserted_bound tree initial.toGraphState tag protections counter below fresh room allocated index inserted newBound

end DuplicatePrefix.GeneralBorrowForestTagHighWaterConcreteFrame
