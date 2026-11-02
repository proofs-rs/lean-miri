import duplicate_prefix.GeneralBorrowSharedGeneratorReadyStep
namespace DuplicatePrefix.GeneralBorrowSharedGeneratorReadyRepeat
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Stable tag/index keys; the actual node record is recovered in each current
state, so ancestor SIFA updates need not preserve old TreeNode values. -/
def ReadyKeys (input : Input) (location : LocationTree) (keys : List (BorTag × UniIndex)) : Prop :=
  ∀ key ∈ keys, ∃ node, Ready input.tree location input.parent input.parentNode ⟨key.1,key.2,node⟩

/-- Actual append indices are fresh even for initial sparse trees. -/
theorem fresh_key (input : Input) (location : LocationTree) (keys : List (BorTag × UniIndex))
    (ready : ReadyKeys input location keys) : index input ∉ keys.map Prod.snd := by
  intro member
  obtain ⟨key,inKeys,same⟩ := List.mem_map.mp member
  obtain ⟨node,facts⟩ := ready key inKeys
  have bounded := GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes key.2 node facts.present
  have equal := congrArg UniIndex.toNat same
  rw [at_end input] at equal
  omega

/-- Finite real Read/append generation retains every earlier Ready sibling and
creates a new one each time. No family of poststates or Ready outputs is input. -/
theorem iterate (tags : List BorTag) (input : Input) (location : LocationTree)
    (good : State input location) (keys : List (BorTag × UniIndex))
    (ready : ReadyKeys input location keys) (unique : (keys.map Prod.snd).Nodup)
    (fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh input.tree.tagMapping tag)
    (distinct : tags.Nodup) (current : input.newTag ∉ tags)
    (room : input.tree.tagMapping.mapping.size + tags.length ≤ 4294967295) :
    ∃ final finalLocation finalKeys, GeneralBorrowSharedGeneratorRepeat.Run input tags final ∧
      State final finalLocation ∧ finalLocation.exposedCache = location.exposedCache ∧
      ReadyKeys final finalLocation finalKeys ∧ (finalKeys.map Prod.snd).Nodup ∧
      finalKeys.length = keys.length+tags.length := by
  induction tags generalizing input location keys with
  | nil => exact ⟨input,location,keys,.nil input,good,rfl,ready,unique,by simp⟩
  | cons tag rest ih =>
    have tagFresh := fresh tag (by simp)
    have tagDifferent : input.newTag ≠ tag := fun same => current (by simp [same])
    have stepRoom : input.tree.tagMapping.mapping.size+1 ≤ 4294967295 := by
      simp only [List.length_cons] at room
      omega
    obtain ⟨readDone,childDone,next,nextLocation,newNode,tree,parent,newTag,nextGood,mappingEq,cache,newReady,preserved⟩ :=
      GeneralBorrowSharedGeneratorReadyStep.step input location good tag stepRoom tagFresh tagDifferent
    let nextKeys := (input.newTag,index input)::keys
    have nextReady : ReadyKeys next nextLocation nextKeys := by
      intro key member
      rcases List.mem_cons.mp member with same | old
      · subst key
        exact ⟨newNode,newReady⟩
      · obtain ⟨node,previous⟩ := ready key old
        exact preserved ⟨key.1,key.2,node⟩ previous
    have nextUnique : (nextKeys.map Prod.snd).Nodup :=
      List.nodup_cons.mpr ⟨fresh_key input location keys ready,unique⟩
    have nextFresh : ∀ future ∈ rest, GeneralBorrowTagMap.Fresh next.tree.tagMapping future := by
      intro future member
      have oldFresh := fresh future (by simp [member])
      have different : input.newTag ≠ future := fun same => current (by simp [same,member])
      have retained := GeneralBorrowFreshMetadataChildAllocator.append_fresh input future oldFresh different
      rw [(GeneralBorrowFreshMetadataChildShared.append input).mapping] at retained
      rw [mappingEq]
      exact retained
    have nextCurrent : next.newTag ∉ rest := by rw [newTag];exact (List.nodup_cons.mp distinct).1
    have size : next.tree.tagMapping.mapping.size = input.tree.tagMapping.mapping.size+1 := by
      rw [mappingEq]
      simp only [mapping,Array.size_push]
    have nextRoom : next.tree.tagMapping.mapping.size+rest.length ≤ 4294967295 := by
      rw [size]
      simp only [List.length_cons] at room
      omega
    obtain ⟨final,finalLocation,finalKeys,history,finalGood,finalCache,finalReady,finalUnique,length⟩ :=
      ih next nextLocation nextGood nextKeys nextReady nextUnique nextFresh
        (List.nodup_cons.mp distinct).2 nextCurrent nextRoom
    refine ⟨final,finalLocation,finalKeys,.cons readDone childDone tree parent newTag history,
      finalGood,finalCache.trans cache,finalReady,finalUnique,?_⟩
    simpa only [nextKeys,List.length_cons,Nat.add_assoc,Nat.add_comm 1 rest.length] using length

/-- Recover current request records from the generated keys, with exact leaves
and actual Ready data, rather than asking the final caller to supply requests. -/
theorem requests_exist (input : Input) (location : LocationTree) (keys : List (BorTag × UniIndex))
    (ready : ReadyKeys input location keys) :
    ∃ requests : List Request, requests.map Request.leaf = keys.map Prod.snd ∧
      ∀ request ∈ requests, Ready input.tree location input.parent input.parentNode request := by
  induction keys with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons key rest ih =>
    obtain ⟨node,first⟩ := ready key (by simp)
    obtain ⟨requests,leaves,others⟩ := ih (fun other member => ready other (by simp [member]))
    refine ⟨⟨key.1,key.2,node⟩::requests,?_,?_⟩
    · simp only [List.map_cons,leaves]
    · intro request member
      rcases List.mem_cons.mp member with same | later
      · subst request;exact first
      · exact others request later
end DuplicatePrefix.GeneralBorrowSharedGeneratorReadyRepeat
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedGeneratorReadyRepeat.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated Ready history dependency {dependency}"
