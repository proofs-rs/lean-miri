import duplicate_prefix.GeneralBorrowFullSharedEntryData
namespace DuplicatePrefix.GeneralBorrowFullSharedResources
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowFullSharedRead DuplicatePrefix.GeneralBorrowGcAllocator
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Map freshness entails live-node freshness when actual node/tag-map
correspondence has been derived. -/
theorem protector_fresh (tree : BorrowTree) (coherent : NodeTags tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) : GeneralBorrowProtector.Fresh tree tag := by
  intro row member same
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp
    (Array.mem_toList_iff.mpr member)
  have lookup := coherent row.1 row.2 present
  have absent : tree.tagMapping.get tag = none := by
    unfold UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh]
    rfl
  rw [same,absent] at lookup
  cases lookup

set_option autoImplicit false in
/-- Borrow-only resources for the whole-invocation factory, derived from actual
allocation/generation; physical caller-machine resources are separate. -/
structure Resources {n : Nat} (input : Input) (location : LocationTree) (reserve : Fin n → BorTag) : Prop where
  state : State input location
  allocator : Invariant input.tree
  futureMap : ∀ step, GeneralBorrowTagMap.Fresh input.tree.tagMapping (reserve step)
  futureNodes : ∀ step, GeneralBorrowProtector.Fresh input.tree (reserve step)
  nodeRoom : input.tree.nodes.size+4 ≤ 4294967295
  cleanVacant : ∀ query, input.tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean input.tree query

/-- Retain unused future tags and account for exact allocator growth along
actual Read/shared appends. No successful operation is an input. -/
theorem iterate {n : Nat} (tags : List BorTag) (input : Input) (location : LocationTree)
    (good : State input location) (initial : Invariant input.tree)
    (fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh input.tree.tagMapping tag)
    (distinct : tags.Nodup) (current : input.newTag ∉ tags)
    (reserve : Fin n → BorTag)
    (spareFresh : ∀ step, GeneralBorrowTagMap.Fresh input.tree.tagMapping (reserve step))
    (spareCurrent : ∀ step, input.newTag ≠ reserve step)
    (spareFuture : ∀ tag ∈ tags, ∀ step, tag ≠ reserve step)
    (room : input.tree.tagMapping.mapping.size + tags.length ≤ 4294967295) :
    ∃ final finalLocation, GeneralBorrowFullSharedRepeat.Run input tags final ∧ State final finalLocation ∧ Invariant final.tree ∧
      final.tree.tagMapping.mapping.size = input.tree.tagMapping.mapping.size+tags.length ∧
      (∀ step, GeneralBorrowTagMap.Fresh final.tree.tagMapping (reserve step)) := by
  induction tags generalizing input location with
  | nil => exact ⟨input,location,.nil input,good,initial,by simp,spareFresh⟩
  | cons tag rest ih =>
    have tagFresh := fresh tag (by simp)
    have tagDifferent : input.newTag ≠ tag := fun same => current (by simp [same])
    have stepRoom : input.tree.tagMapping.mapping.size+1 ≤ 4294967295 := by
      simp only [List.length_cons] at room
      omega
    obtain ⟨readDone,childDone,next,nextLocation,tree,parent,newTag,nextGood,mappingEq,lengthEq⟩ :=
      GeneralBorrowFullSharedStep.step input location good tag stepRoom tagFresh tagDifferent
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
    have nextInvariant : Invariant next.tree := by
      rw [tree]
      exact GeneralBorrowFullSharedEntryData.child_invariant input location good initial
    have nextSpare : ∀ step, GeneralBorrowTagMap.Fresh next.tree.tagMapping (reserve step) := by
      intro step
      rw [mappingEq]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push input.tree.tagMapping input.newTag
        (reserve step) (index input) input.tree.tagMapping.deassigned (spareFresh step) (spareCurrent step)
    have nextDifferent : ∀ step, next.newTag ≠ reserve step := by
      intro step
      rw [newTag]
      exact spareFuture tag (by simp) step
    obtain ⟨final,finalLocation,history,finalGood,finalInvariant,finalSize,finalSpare⟩ :=
      ih next nextLocation nextGood nextInvariant nextFresh (List.nodup_cons.mp distinct).2 nextCurrent
        nextSpare nextDifferent (fun future member => spareFuture future (by simp [member])) nextRoom
    exact ⟨final,finalLocation,.cons readDone childDone tree parent newTag lengthEq history,finalGood,finalInvariant,by simp only [List.length_cons] at *;omega,finalSpare⟩
/-- Actual allocation/generation derives every borrow-side resource of the
pooled invocation contract. Reserved tags are explicit unused input resources. -/
theorem generate {n : Nat} (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (reserve : Fin n → BorTag)
    (reserved : ∀ step, reserve step ∉ rootTag :: childTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    ∃ final finalLocation, GeneralBorrowFullSharedRepeat.Run seed tags final ∧
      Resources final finalLocation reserve ∧
      Nonempty (GenericAsMutPtrEntryValidity.Data final.tree {} final.parentTag final.newTag final.offset final.len) := by
  let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
  have singletonFresh : ∀ tag, rootTag ≠ tag → GeneralBorrowTagMap.Fresh seed.tree.tagMapping tag := by
    intro tag different row member
    change row ∈ (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).tagMapping.mapping at member
    rw [GeneralBorrowFullSharedSeed.tree_eq] at member
    have same := Array.mem_singleton.mp member
    subst row
    exact different
  have fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh seed.tree.tagMapping tag := by
    intro tag member
    exact singletonFresh tag (fun same => rootUnused (same.symm ▸ member))
  have spareFresh : ∀ step, GeneralBorrowTagMap.Fresh seed.tree.tagMapping (reserve step) := by
    intro step
    exact singletonFresh (reserve step) (fun same => reserved step (by simp [same]))
  have spareCurrent : ∀ step, seed.newTag ≠ reserve step := by
    intro step same
    exact reserved step (by simp [show childTag = reserve step from same])
  have spareFuture : ∀ tag ∈ tags, ∀ step, tag ≠ reserve step := by
    intro tag member step same
    exact reserved step (by simp [←same,member])
  have initialSize : seed.tree.tagMapping.mapping.size = 1 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).tagMapping.mapping.size = 1
    rw [GeneralBorrowFullSharedSeed.tree_eq]
    rfl
  have tagCapacity : seed.tree.tagMapping.mapping.size+tags.length ≤ 4294967295 := by omega
  have initial : Invariant seed.tree := GeneralBorrowGcAllocator.initial rootTag (Size.ofBytes capacity)
  obtain ⟨final,location,history,good,coherent,size,spares⟩ := iterate tags seed GeneralBorrowFullSharedSeed.location
    (GeneralBorrowFullSharedSeed.state capacity nonzero rootTag childTag different) initial fresh unique childUnused
    reserve spareFresh spareCurrent spareFuture tagCapacity
  have finalRoom : final.tree.nodes.size+4 ≤ 4294967295 := by
    have aligned := final.aligned
    change final.tree.nodes.data.size+4 ≤ 4294967295
    omega
  have resources : Resources final location reserve :=
    ⟨good,coherent,spares,(fun step => protector_fresh final.tree coherent.nodeTags (reserve step) (spares step)),
      finalRoom,GeneralBorrowFullSharedEntryData.vacant_clean final location good⟩
  exact ⟨final,location,history,resources,⟨GeneralBorrowFullSharedEntryData.data final location good coherent⟩⟩
end DuplicatePrefix.GeneralBorrowFullSharedResources
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedResources.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated call resource dependency {dependency}"
