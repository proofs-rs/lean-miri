import duplicate_prefix.GeneralBorrowSharedGeneratorCache
namespace DuplicatePrefix.GeneralBorrowSharedGeneratorReadyStep
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowExposeReadParentRead DuplicatePrefix.RangeMapNonempty
open DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem homogeneous_inj (left right : LocationTree)
    (same : homogeneous (1 : UInt64) left = homogeneous 1 right) : left = right := by
  have projected := congrArg (fun locations : DedupRangeMap LocationTree =>
    (locations.entries[0]?).map (fun segment => segment.data)) same
  simpa [homogeneous] using projected

/-- One actual Read/append both forms the same-parent next Input and extends a
Ready family in that very state. The family's root is the next Input's actual
parentNode, derived by lookup uniqueness, rather than an assumed post-root. -/
theorem step (input : Input) (location : LocationTree) (good : State input location)
    (nextTag : BorTag) (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping nextTag) (different : input.newTag ≠ nextTag) :
    (read input {}).status = .Completed ∧ (child input {}).outcome = .ok () ∧
    ∃ nextInput postLocation newNode,
      nextInput.tree = (child input {}).tree ∧ nextInput.parent = input.parent ∧
      nextInput.newTag = nextTag ∧ State nextInput postLocation ∧ nextInput.tree.tagMapping = mapping input ∧
      postLocation.exposedCache = location.exposedCache ∧
      Ready nextInput.tree postLocation nextInput.parent nextInput.parentNode
        ⟨input.newTag,index input,newNode⟩ ∧
      ∀ request, Ready input.tree location input.parent input.parentNode request →
        ∃ node, Ready nextInput.tree postLocation nextInput.parent nextInput.parentNode
          ⟨request.tag,request.leaf,node⟩ := by
  obtain ⟨readDone,childDone,nextInput,postLocation,treeEq,parentEq,newTag,nextGood,mappingEq,cacheEq⟩ :=
    GeneralBorrowSharedGeneratorCache.step input location good nextTag room fresh different
  obtain ⟨_,_,actualLocation,actualRoot,newNode,locations,newReady,_,preserved⟩ :=
    GeneralBorrowSharedGeneratorCache.read_append_ready input location good
  have locationEq := homogeneous_inj postLocation actualLocation
    (nextGood.locations.symm.trans ((congrArg BorrowTree.locations treeEq).trans locations))
  have nextPresent := nextInput.parentPresent
  rw [treeEq,parentEq] at nextPresent
  have rootEq : actualRoot = nextInput.parentNode := Option.some.inj (newReady.rootPresent.symm.trans nextPresent)
  refine ⟨readDone,childDone,nextInput,postLocation,newNode,treeEq,parentEq,newTag,nextGood,mappingEq,cacheEq,?_,?_⟩
  · rw [treeEq,parentEq,locationEq,←rootEq]
    exact newReady
  · intro request oldReady
    obtain ⟨node,ready,_⟩ := preserved request input.parentNode oldReady
    refine ⟨node,?_⟩
    rw [treeEq,parentEq,locationEq,←rootEq]
    exact ready
end DuplicatePrefix.GeneralBorrowSharedGeneratorReadyStep
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedGeneratorReadyStep.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared generator Ready-step dependency {dependency}"
