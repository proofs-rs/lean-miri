import duplicate_prefix.GeneralBorrowRecursiveSharedResources
import duplicate_prefix.GeneralBorrowFreshSharedStageAttachAny

namespace DuplicatePrefix.GeneralBorrowRecursiveSharedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRecursiveSharedResources DuplicatePrefix.GeneralBorrowFreshSharedSequence
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Data-oriented current descendant and its locally owned range. No completed
operation or successful execution is stored in this recurring state. -/
structure State (root : UniIndex) (offset len : UInt64) where
  tree : BorrowTree
  resources : Resources tree root
  parent : UniIndex
  node : TreeNode
  present : tree.nodeAt parent = some node
  protections : ProtectedTags
  writable : Nat → Bool
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations

def supplied {root : UniIndex} {offset len : UInt64} (s : State root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0) :
    Data s.tree tag s.parent offset len :=
  data s.tree root s.resources s.parent s.node s.present tag fresh offset len nonzero s.bounds

def metadata {root : UniIndex} {offset len : UInt64} (s : State root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0) (held : Bool) :=
  GeneralBorrowFreshStageMetadata.build s.tree tag s.parent offset len (supplied s tag fresh nonzero)
    s.protections held s.writable s.owned

/-- Perform the actual current-parent Read and child constructor, then move the
recurring state to that actual new child. Rank slack and Slot are internal. -/
noncomputable def next {root : UniIndex} {offset len : UInt64} (s : State root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0) (held : Bool)
    (room : s.tree.nodes.size+5 ≤ 4294967295) : State root offset len := by
  let d := supplied s tag fresh nonzero
  have facts := advance s.tree root s.resources s.parent s.node s.present tag fresh offset len nonzero s.bounds
    s.protections held s.writable s.owned room
  let info := metadata s tag fresh nonzero held
  let node := Classical.choose info.node
  exact {
    tree := (child d s.protections held).tree
    resources := Classical.choice facts.2.2.1
    parent := index d,node := node,present := (Classical.choose_spec info.node).1
    protections := registered s.protections tag held
    writable := GeneralBorrowFreshMixedChild.extend s.writable (index d).toNat
    bounds := by rw [info.capacity];exact s.bounds
    owned := facts.2.2.2.1 }

theorem next_tag {root : UniIndex} {offset len : UInt64} (s : State root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0) (held : Bool)
    (room : s.tree.nodes.size+5 ≤ 4294967295) : (next s tag fresh nonzero held room).node.tag = tag :=
  (Classical.choose_spec (metadata s tag fresh nonzero held).node).2.1

theorem next_size {root : UniIndex} {offset len : UInt64} (s : State root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0) (held : Bool)
    (room : s.tree.nodes.size+5 ≤ 4294967295) : (next s tag fresh nonzero held room).tree.nodes.size ≤ s.tree.nodes.size+1 := by
  let info := metadata s tag fresh nonzero held
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  have extension := info.extension location location s.protections
  have beforeSize : (source_normal_projection s.tree location s.protections).topology.nodes.size = s.tree.nodes.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size]
  have afterSize : (source_normal_projection (child (supplied s tag fresh nonzero) s.protections held).tree location s.protections).topology.nodes.size =
      (next s tag fresh nonzero held room).tree.nodes.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size,next]
  rcases extension with appended | reused
  · have count := appended.length
    rw [beforeSize,afterSize] at count
    omega
  · have count := reused.length
    rw [beforeSize,afterSize] at count
    omega

/-- Actual source ancestor-path length, independent of proof-only rank
normalization. A generated descendant has one additional real ancestor. -/
def height {root : UniIndex} {offset len : UInt64} (s : State root offset len) : Nat :=
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  (source_normal_projection s.tree location {}).topology.ancestorPath s.parent.toNat |>.length

theorem next_height {root : UniIndex} {offset len : UInt64} (s : State root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0) (held : Bool)
    (room : s.tree.nodes.size+5 ≤ 4294967295) : height (next s tag fresh nonzero held room) = height s+1 := by
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  have attached := GeneralBorrowFreshSharedStageAttachAny.attach s.tree tag s.parent offset len (supplied s tag fresh nonzero)
    s.protections held s.writable s.owned location location {}
  have path := attached.childPath
  have count := congrArg List.length path
  simpa only [height,next,List.length_cons,Nat.add_comm] using count

/-- Every constructor step is the actual Read/newChild pair, and the next
parent is its fresh child. Success and ActiveWithin are outputs of generation. -/
inductive Run {root : UniIndex} {offset len : UInt64} (nonzero : len ≠ 0) :
    State root offset len → List (BorTag × Bool) → State root offset len → Prop where
  | nil (s : State root offset len) : Run nonzero s [] s
  | cons (s : State root offset len) (tag : BorTag) (held : Bool) (rest : List (BorTag × Bool))
      (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (room : s.tree.nodes.size+5 ≤ 4294967295)
      (readDone : (read (supplied s tag fresh nonzero) s.protections held).status = .Completed)
      (childDone : (child (supplied s tag fresh nonzero) s.protections held).outcome = .ok ())
      (active : GeneralBorrowFreshActiveWithin.ActiveWithin (next s tag fresh nonzero held room).tree
        (next s tag fresh nonzero held room).parent .Read offset (offset+len))
      {final : State root offset len}
      (tail : Run nonzero (next s tag fresh nonzero held room) rest final) : Run nonzero s ((tag,held)::rest) final

/-- Arbitrary finite child→child→... chains are constructed from initial
metadata/local ownership. All Reads and constructors complete; next Resources,
mixed ownership and active-range facts are established at every actual step.
Fresh tags and conservative UInt32 storage headroom are explicit resources. -/
theorem generate {root : UniIndex} {offset len : UInt64} (s : State root offset len) (nonzero : len ≠ 0)
    (steps : List (BorTag × Bool)) (unique : (steps.map Prod.fst).Nodup)
    (fresh : ∀ tag ∈ steps.map Prod.fst, GeneralBorrowTagMap.Fresh s.tree.tagMapping tag)
    (room : s.tree.nodes.size+steps.length+4 ≤ 4294967295) :
    ∃ final : State root offset len, Run nonzero s steps final ∧
      final.tree.nodes.size ≤ s.tree.nodes.size+steps.length ∧
      (∀ tag, tag ∉ steps.map Prod.fst → GeneralBorrowTagMap.Fresh s.tree.tagMapping tag →
        GeneralBorrowTagMap.Fresh final.tree.tagMapping tag) := by
  induction steps generalizing s with
  | nil => exact ⟨s,.nil s,Nat.le_refl _,fun _ _ initial => initial⟩
  | cons action rest ih =>
    rcases action with ⟨tag,held⟩
    have distinct := List.nodup_cons.mp unique
    have available := fresh tag (by simp)
    have reserve : s.tree.nodes.size+5 ≤ 4294967295 := by simp only [List.length_cons] at room;omega
    let post := next s tag available nonzero held reserve
    have facts := advance s.tree root s.resources s.parent s.node s.present tag available offset len nonzero s.bounds
      s.protections held s.writable s.owned reserve
    have growth := next_size s tag available nonzero held reserve
    have laterFresh : ∀ nextTag ∈ rest.map Prod.fst, GeneralBorrowTagMap.Fresh post.tree.tagMapping nextTag := by
      intro nextTag member
      exact (metadata s tag available nonzero held).freshTag nextTag (fresh nextTag (by simp [member]))
        (fun same => distinct.1 (same ▸ member))
    have laterRoom : post.tree.nodes.size+rest.length+4 ≤ 4294967295 := by
      simp only [List.length_cons] at room
      change post.tree.nodes.size ≤ s.tree.nodes.size+1 at growth
      omega
    obtain ⟨final,history,bound,future⟩ := ih post distinct.2 laterFresh laterRoom
    refine ⟨final,.cons s tag held rest available reserve facts.1 facts.2.1 facts.2.2.2.2 history,?_,?_⟩
    · have combined := next_size s tag available nonzero held reserve
      change post.tree.nodes.size ≤ s.tree.nodes.size+1 at combined
      simp only [List.length_cons]
      omega
    · intro nextTag unused initial
      have parts : nextTag ≠ tag ∧ nextTag ∉ rest.map Prod.fst := by simpa only [List.map_cons,List.mem_cons,not_or] using unused
      exact future nextTag parts.2 ((metadata s tag available nonzero held).freshTag nextTag initial (Ne.symm parts.1))

/-- A generated chain's real source path grows by exactly its number of
shared stages, so the finite induction is genuinely arbitrary-depth formation. -/
theorem Run.height {root : UniIndex} {offset len : UInt64} {nonzero : len ≠ 0}
    {initial final : State root offset len} {steps : List (BorTag × Bool)}
    (history : Run nonzero initial steps final) : height final = height initial+steps.length := by
  induction history with
  | nil => simp
  | cons s tag held rest fresh room readDone childDone active tail ih =>
    have growth := next_height s tag fresh nonzero held room
    simp only [List.length_cons]
    omega

/-- Every nonempty generated chain ends at a real active shared descendant. -/
theorem Run.final_active {root : UniIndex} {offset len : UInt64} {nonzero : len ≠ 0}
    {initial final : State root offset len} {steps : List (BorTag × Bool)}
    (history : Run nonzero initial steps final) (nonempty : steps ≠ []) :
    GeneralBorrowFreshActiveWithin.ActiveWithin final.tree final.parent .Read offset (offset+len) := by
  induction history with
  | nil => exact False.elim (nonempty rfl)
  | cons s tag held rest fresh room readDone childDone active tail ih =>
    cases rest with
    | nil => cases tail;exact active
    | cons action more => exact ih (by simp)

end DuplicatePrefix.GeneralBorrowRecursiveSharedHistory
