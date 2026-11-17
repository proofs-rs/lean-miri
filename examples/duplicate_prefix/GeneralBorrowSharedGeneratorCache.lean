import duplicate_prefix.GeneralBorrowSharedGeneratorRepeat
import duplicate_prefix.GeneralBorrowReadNoopCache
namespace DuplicatePrefix.GeneralBorrowSharedGeneratorCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowExposeReadParentRead DuplicatePrefix.RangeMapNonempty
open DuplicatePrefix.GeneralBorrowSharedGeneratorRepeat
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The exact generator profile makes real normal Read cache-neutral, including
when the selected Unique parent or other Frozen nodes are exposed. -/
theorem read_cache (input : Input) (location : LocationTree) (good : State input location) :
    (readLocation input location {}).exposedCache = location.exposedCache := by
  obtain ⟨forest⟩ := good.forest
  apply GeneralBorrowReadNoopCache.selected_unique input.tree location input.parent {}
    .VisitChildrenOfAccessed GeneralBorrowWildcardLeaf.unique forest
    (GeneralBorrowSharedGeneratorProfile.read_owned input location good.parentless good.profile)
    good.profile.rootStored rfl
  intro event member index node converted present different exposed
  exact ⟨GeneralBorrowFreshAnchor.sharedState,good.profile.shared index node present different,rfl⟩

/-- A genuine ranged Read followed by the actual shared constructor has a
homogeneous location with the original exact cache; no completion is assumed. -/
theorem child_cache (input : Input) (location : LocationTree) (good : State input location) :
    ∃ postLocation, (child input {}).tree.locations = homogeneous 1 postLocation ∧
      postLocation.exposedCache = location.exposedCache := by
  obtain ⟨forest⟩ := good.forest
  let prepared := afterReadInput input location {} good.offset good.length
  have readFacts := GeneralBorrowSharedProfileParentRead.read_closed input location good.offset good.length
    good.locations good.roots good.parentless forest good.profile
  have actualChild : child input {} = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag (DedupRangeMap.new (Size.ofBytes prepared.len)
        GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    unfold child
    rw [readFacts.2.1]
    simp only [prepared,afterReadInput,good.offset,good.length]
  have childTree : (child input {}).tree = result prepared := by rw [actualChild];rfl
  obtain ⟨postLocation,locations,profile,cache⟩ := GeneralBorrowSharedProfileAppend.append prepared
    (readLocation input location {}) good.offset good.length rfl good.parentless readFacts.2.2.1
  exact ⟨postLocation,by rw [childTree];exact locations,cache.trans (read_cache input location good)⟩

private theorem homogeneous_inj (left right : LocationTree)
    (same : homogeneous (1 : UInt64) left = homogeneous 1 right) : left = right := by
  have projected := congrArg (fun locations : DedupRangeMap LocationTree =>
    (locations.entries[0]?).map (fun segment => segment.data)) same
  simpa [homogeneous] using projected

/-- Cache equality is independent of the existential post-location witness
chosen by the existing step theorem, since its actual tree fixes that location. -/
theorem cache_of_step (input : Input) (location : LocationTree) (good : State input location)
    (nextInput : Input) (postLocation : LocationTree)
    (actual : nextInput.tree = (child input {}).tree) (nextGood : State nextInput postLocation) :
    postLocation.exposedCache = location.exposedCache := by
  obtain ⟨actualLocation,locations,cache⟩ := child_cache input location good
  have same := homogeneous_inj postLocation actualLocation
    (nextGood.locations.symm.trans ((congrArg BorrowTree.locations actual).trans locations))
  exact (congrArg LocationTree.exposedCache same).trans cache

/-- The original real step, retaining exact cache equality in its constructed
next state as well as allocator metadata. -/
theorem step (input : Input) (location : LocationTree) (good : State input location)
    (nextTag : BorTag) (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping nextTag) (different : input.newTag ≠ nextTag) :
    (read input {}).status = .Completed ∧ (child input {}).outcome = .ok () ∧
    ∃ nextInput postLocation, nextInput.tree = (child input {}).tree ∧ nextInput.parent = input.parent ∧
      nextInput.newTag = nextTag ∧ State nextInput postLocation ∧ nextInput.tree.tagMapping = mapping input ∧
      postLocation.exposedCache = location.exposedCache := by
  obtain ⟨readDone,childDone,nextInput,postLocation,actual,parent,newTag,nextGood,mappingEq⟩ :=
    GeneralBorrowSharedGeneratorStep.step input location good nextTag room fresh different
  exact ⟨readDone,childDone,nextInput,postLocation,actual,parent,newTag,nextGood,mappingEq,
    cache_of_step input location good nextInput postLocation actual nextGood⟩

/-- The same actual Read/constructor result forms the new Ready leaf and
retains every prior Ready sibling, with unchanged cache. The exact State
profile replaces an all-nodes-unexposed assumption on the preceding Read. -/
theorem read_append_ready (input : Input) (location : LocationTree) (good : State input location) :
    (read input {}).status = .Completed ∧ (child input {}).outcome = .ok () ∧
    ∃ postLocation postRoot requestNode,
      (child input {}).tree.locations = homogeneous 1 postLocation ∧
      GeneralBorrowExposeReadFold.Ready (child input {}).tree postLocation input.parent postRoot
        ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache ∧
      ∀ (request : GeneralBorrowExposeReadFold.Request) (rootNode : TreeNode),
        GeneralBorrowExposeReadFold.Ready input.tree location input.parent rootNode request →
        ∃ nextNode, GeneralBorrowExposeReadFold.Ready (child input {}).tree postLocation input.parent postRoot
          ⟨request.tag,request.leaf,nextNode⟩ ∧ nextNode.tag = request.node.tag := by
  obtain ⟨forest⟩ := good.forest
  let prepared := afterReadInput input location {} good.offset good.length
  have readFacts := GeneralBorrowSharedProfileParentRead.read_closed input location good.offset good.length
    good.locations good.roots good.parentless forest good.profile
  have actualChild : child input {} = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag (DedupRangeMap.new (Size.ofBytes prepared.len)
        GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    unfold child
    rw [readFacts.2.1]
    simp only [prepared,afterReadInput,good.offset,good.length]
  have childTree : (child input {}).tree = result prepared := by rw [actualChild];rfl
  obtain ⟨postLocation,postRoot,requestNode,locations,newReady,cache,preserved⟩ :=
    GeneralBorrowExposeReadFormation.append_ready_preserves prepared (readLocation input location {})
      good.offset good.length rfl good.parentless
  refine ⟨readFacts.1,?_,postLocation,postRoot,requestNode,?_,?_,cache.trans (read_cache input location good),?_⟩
  · rw [actualChild]
    exact (GeneralBorrowFreshMetadataChildShared.append prepared).success
  · rw [childTree];exact locations
  · rw [childTree];exact newReady
  · intro request rootNode ready
    rw [childTree]
    exact preserved request rootNode (read_ready input location {} good.offset good.length request rootNode ready)

/-- Every finite sequence built by the real generator retains the initial
exact cache. Initial cache bounds can therefore be carried unchanged through
all these generated Read/append operations. General Rust histories remain out
of scope; State and fresh finite tags/resource headroom stay explicit. -/
theorem iterate (tags : List BorTag) (input : Input) (location : LocationTree)
    (good : State input location)
    (fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh input.tree.tagMapping tag)
    (distinct : tags.Nodup) (current : input.newTag ∉ tags)
    (room : input.tree.tagMapping.mapping.size + tags.length ≤ 4294967295) :
    ∃ final finalLocation, Run input tags final ∧ State final finalLocation ∧
      finalLocation.exposedCache = location.exposedCache := by
  induction tags generalizing input location with
  | nil => exact ⟨input,location,.nil input,good,rfl⟩
  | cons tag rest ih =>
    have tagFresh := fresh tag (by simp)
    have tagDifferent : input.newTag ≠ tag := fun same => current (by simp [same])
    have stepRoom : input.tree.tagMapping.mapping.size+1 ≤ 4294967295 := by
      simp only [List.length_cons] at room
      omega
    obtain ⟨readDone,childDone,next,nextLocation,tree,parent,newTag,nextGood,mappingEq,cache⟩ :=
      step input location good tag stepRoom tagFresh tagDifferent
    have nextFresh : ∀ future ∈ rest, GeneralBorrowTagMap.Fresh next.tree.tagMapping future := by
      intro future member
      have oldFresh := fresh future (by simp [member])
      have different : input.newTag ≠ future := fun same => current (by simp [same,member])
      have preserved := GeneralBorrowFreshMetadataChildAllocator.append_fresh input future oldFresh different
      rw [(GeneralBorrowFreshMetadataChildShared.append input).mapping] at preserved
      rw [mappingEq]
      exact preserved
    have nextCurrent : next.newTag ∉ rest := by rw [newTag];exact (List.nodup_cons.mp distinct).1
    have size : next.tree.tagMapping.mapping.size = input.tree.tagMapping.mapping.size+1 := by
      rw [mappingEq]
      simp only [mapping,Array.size_push]
    have nextRoom : next.tree.tagMapping.mapping.size+rest.length ≤ 4294967295 := by
      rw [size]
      simp only [List.length_cons] at room
      omega
    obtain ⟨final,finalLocation,history,finalGood,finalCache⟩ := ih next nextLocation nextGood nextFresh
      (List.nodup_cons.mp distinct).2 nextCurrent nextRoom
    exact ⟨final,finalLocation,.cons readDone childDone tree parent newTag history,finalGood,finalCache.trans cache⟩
end DuplicatePrefix.GeneralBorrowSharedGeneratorCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedGeneratorCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared generator cache dependency {dependency}"
