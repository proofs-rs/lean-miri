import duplicate_prefix.GenericFunctionTagFormation
import duplicate_prefix.GeneralBorrowGcAllocator
import duplicate_prefix.GeneralBorrowProtectorCacheMap
namespace DuplicatePrefix.GeneralBorrowForestTagHighWater
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Raw original high-water data, with no generated-tag or operation outcome.
Node-tag bounds follow separately from the intrinsic allocator NodeTags law. -/
structure Below (tree : BorrowTree) (protections : ProtectedTags) (counter : BorTag) : Prop where
  mapping : ∀ row ∈ tree.tagMapping.mapping, row.1.value.toNat < counter.value.toNat
  protectors : ∀ row ∈ protections.entries, row.1.value.toNat < counter.value.toNat

theorem mapped (tree : BorrowTree) (protections : ProtectedTags) (counter tag : BorTag)
    (below : Below tree protections counter) (index : UniIndex) (lookup : tree.tagMapping.get tag=some index) :
    tag.value.toNat < counter.value.toNat := by
  unfold UniKeyMap.get at lookup
  cases found : tree.tagMapping.mapping.find? (fun row => row.1==tag) with
  | none => simp [found] at lookup
  | some row =>
    have member := Array.mem_of_find?_eq_some found
    have same : row.1=tag := by simpa only [beq_iff_eq] using Array.find?_some found
    exact same ▸ below.mapping row member

theorem complete (tree : BorrowTree) (protections : ProtectedTags) (counter : BorTag)
    (below : Below tree protections counter) (tags : GeneralBorrowGcAllocator.NodeTags tree) :
    GenericFunctionTagFormation.Below tree protections counter := by
  refine ⟨below.mapping,?_,below.protectors⟩
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_def.mp member)
  exact mapped tree protections counter row.2.tag below row.1 (tags row.1 row.2 present)

theorem get_none (protections : ProtectedTags) (tag : BorTag) (free : protections.contains tag=false) : protections.get tag=none := by
  unfold ProtectedTags.contains at free
  cases found : protections.get tag with
  | none => rfl
  | some kind => simp [found] at free

theorem different (left right : BorTag) (less : left.value.toNat < right.value.toNat) : left≠right := by
  intro same
  have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
  omega

/-- Exact source registration/endCall for a singleton helper frame retains
other protectors, including the original caller slot child and free slot root. -/
theorem helper_flags (protections : ProtectedTags) (helper slotRoot slotChild : BorTag) (id : AllocId)
    (rootDifferent : slotRoot≠helper) (childDifferent : slotChild≠helper)
    (rootFree : protections.contains slotRoot=false) (childHeld : protections.contains slotChild=true) :
    ((protections.insert helper .StrongProtector).remove helper).contains slotRoot = false ∧
    ((protections.insert helper .StrongProtector).remove helper).contains slotChild = true := by
  constructor
  · unfold ProtectedTags.contains at rootFree ⊢
    rw [GeneralBorrowProtectorCacheMap.remove_other _ helper slotRoot rootDifferent,ProtectorInsertion.get_other _ helper slotRoot _ rootDifferent]
    exact rootFree
  · unfold ProtectedTags.contains at childHeld ⊢
    rw [GeneralBorrowProtectorCacheMap.remove_other _ helper slotChild childDifferent,ProtectorInsertion.get_other _ helper slotChild _ childDifferent]
    exact childHeld
end DuplicatePrefix.GeneralBorrowForestTagHighWater
