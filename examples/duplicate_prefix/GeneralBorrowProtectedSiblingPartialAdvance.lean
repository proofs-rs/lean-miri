import duplicate_prefix.GeneralBorrowProtectedSiblingPartialCore
import duplicate_prefix.GeneralBorrowProtectedSiblingPartialFlags
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowMetadata
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialAdvance
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindowSeed GeneralRangeMapState GeneralBorrowExposureCardinality
open GeneralBorrowProtectedSiblingGenerationBounds GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingPartialCore
open GeneralBorrowProtectedSiblingGenerationWindowCore (Descriptor)
variable {capacity : UInt64}
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem generate {remaining : Nat} (before : Core capacity (remaining+1)) (window : Window capacity) : Nonempty (Advance before window) := by
  let input := slice before.input before.capacity window
  have pointerRoom : before.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room := before.tagRoom
    change before.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  let future := TypedRetagEmpty.successorTag before.global.nextPointerTag pointerRoom
  have futureNat : future.value.toNat = before.global.nextPointerTag.value.toNat+1 := successor_nat _ pointerRoom
  have futureFresh : GeneralBorrowTagMap.Fresh before.input.tree.tagMapping future := map_fresh _ _ before.mapBelow future (by omega)
  have different : before.input.newTag ≠ future := by
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    rw [before.tag,futureNat] at equal
    omega
  have unheld : before.global.protectedTags.get before.input.newTag = none :=
    GeneralBorrowProtectedSiblingGenerationBounds.unheld _ _ before.protectedBelow before.input.newTag (by rw [before.tag];exact Nat.le_refl _)
  obtain ⟨step⟩ := GeneralBorrowProtectedSiblingGenerationStep.generate input before.global before.frame allocation false before.tag pointerRoom unheld before.roots
    before.readable before.physical before.coherent before.allocator future rfl futureFresh different (by change before.input.tree.tagMapping.mapping.size+1 ≤ 4294967295;have room := before.nodeRoom;omega)
  have positive : capacity ≠ 0 := by simpa only [before.len] using before.input.nonzero
  let nextInput := full step.next (step.capacity.trans before.capacity) positive
  have oldDifferent : ∀ old ∈ before.tags,old ≠ before.input.newTag := by
    intro old member same
    have smaller := before.tagBelow old member
    rw [same,before.tag] at smaller
    exact Nat.lt_irrefl _ smaller
  have protectedBound : ProtectedBelow step.output.global.protectedTags step.output.global.nextPointerTag.value.toNat := by
    rw [step.globalTags,step.globalNext]
    exact protected_insert before.global.protectedTags _ future.value.toNat before.protectedBelow before.input.newTag .StrongProtector
      (by rw [before.tag,futureNat];omega) (by rw [futureNat];omega)
  have mapBound : KeysBelow step.next.tree.tagMapping step.output.global.nextPointerTag.value.toNat := by
    intro row member
    rw [step.mapping] at member
    simp only [Array.mem_push] at member
    rw [step.globalNext]
    rcases member with old | equal
    · exact Nat.lt_of_lt_of_le (before.mapBelow row old) (by rw [futureNat];omega)
    · subst row
      change before.input.newTag.value.toNat < future.value.toNat
      rw [before.tag,futureNat]
      omega
  have tagsBound : ∀ old ∈ before.tags++[before.input.newTag],old.value.toNat < step.output.global.nextPointerTag.value.toNat := by
    intro old member
    rw [step.globalNext]
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with previous | same
    · exact Nat.lt_of_lt_of_le (before.tagBelow old previous) (by rw [futureNat];omega)
    · subst old;rw [before.tag,futureNat];omega
  have tagsHeld : ∀ old ∈ before.tags++[before.input.newTag],step.output.global.protectedTags.contains old = true := by
    intro old member
    rw [step.globalTags]
    change (before.global.protectedTags.insert before.input.newTag .StrongProtector).contains old = true
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with previous | same
    · rw [ProtectorInsertion.contains_other _ _ _ _ (oldDifferent old previous)]
      exact before.held old previous
    · subst old;simp [ProtectedTags.contains]
  have tagsDistinct : (before.tags++[before.input.newTag]).Nodup := by
    rw [List.nodup_append]
    refine ⟨before.distinct,by simp,?_⟩
    intro old member current currentMember same
    have equal : current = before.input.newTag := by simpa using currentMember
    exact oldDifferent old member (same.trans equal)
  have descriptors : ∀ old ∈ before.tags++[before.input.newTag],Nonempty (Descriptor step.next.tree step.next.parent old) := by
    intro old member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with previous | same
    · exact (by
      obtain ⟨descriptor⟩ := before.descriptors old previous
      exact ⟨GeneralBorrowProtectedSiblingGenerationWindowMetadata.old_descriptor step old descriptor⟩)
    · subst old;exact ⟨GeneralBorrowProtectedSiblingGenerationWindowMetadata.new_descriptor step⟩
  let next : Core capacity remaining := {
    input := nextInput,global := step.output.global,frame := step.output.frame,tags := before.tags++[before.input.newTag]
    tag := step.nextTag.trans step.globalNext.symm,parentTag := step.parentTag.trans before.parentTag,parent := step.parent.trans before.parent,
    offset := rfl,len := rfl,roots := step.roots,capacity := step.capacity.trans before.capacity,
    allocator := step.allocator,readable := step.profile,physical := step.physical,coherent := step.coherent,mapBelow := mapBound,protectedBelow := protectedBound,
    tagBelow := tagsBound,tagRoom := by rw [step.globalNext,futureNat];have room := before.tagRoom;omega,
    nodeRoom := by
      change step.next.tree.tagMapping.mapping.size+remaining+1 ≤ 4294967295
      rw [step.mapping,Array.size_push]
      change before.input.tree.tagMapping.mapping.size+1+remaining+1 ≤ 4294967295
      have room := before.nodeRoom
      omega,
    held := tagsHeld,distinct := tagsDistinct,
    frameTags := by rw [step.frameTags,before.frameTags];simp [input,slice],
    descriptors := descriptors,
    hidden := GeneralBorrowProtectedSiblingPartialFlags.preserves input before.global before.frame step before.hidden,
    rootUnique := GeneralBorrowProtectedSiblingPartialRootUnique.step step before.roots before.rootUnique,
    nodes := by change step.next.tree.nodes.size = (before.tags++[before.input.newTag]).length+1;rw [step.growth];change before.input.tree.nodes.size+1 = _;rw [before.nodes];simp,
    origins := before.origins++[(before.input.newTag,window)],
    latest := .inr ⟨before.origins,before.input.newTag,window,GeneralBorrowFreshMetadataChildMutable.index step.prepared.next,rfl,step.lookup,step.typed⟩,originTags := by simp only [List.map_append,List.map_cons,List.map_nil,before.originTags] }
  refine ⟨{next := next,actual := ?_,count := ?_,origins := rfl}⟩
  · intro tail
    have invoked := step.invoked
    change GeneralBorrowForestFnEntry.operation before.input.tree before.global before.frame allocation before.input.parentTag window.offset window.len .VisitChildrenOfAccessed = .ok step.output at invoked
    rw [before.parentTag] at invoked
    simp only [loop,snapshot,invoked,Except.bind,bind,pure,Except.pure]
    have treeEq : step.next.tree = step.output.child.tree := by rw [step.nextTree,step.mutated];rfl
    change loop tail ⟨step.output.child.tree,step.output.global,step.output.frame,before.tags++[step.output.tag]⟩ = loop tail ⟨step.next.tree,step.output.global,step.output.frame,before.tags++[before.input.newTag]⟩
    rw [treeEq,step.outputTag]
    rfl
  · change (before.tags++[before.input.newTag]).length = _
    simp
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialAdvance
