import duplicate_prefix.CurrentCallResourceNormalization
import duplicate_prefix.AllocationRootHookFormation

namespace DuplicatePrefix.CurrentCallAllocationFormation
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exact fresh-cache output of the actual root-tag allocator. -/
def rootedGlobal (global : GlobalState) (id : AllocId) (next : BorTag) : GlobalState :=
  { global with
    nextPointerTag := next
    rootPointerTags := global.rootPointerTags.push (id,global.nextPointerTag) }

theorem root_created (global : GlobalState) (id : AllocId) (next : BorTag)
    (absent : global.rootTag? id = none) (room : BorTag.succ global.nextPointerTag = some next) :
    global.rootPointerTag id = .ok (rootedGlobal global id next,global.nextPointerTag) := by
  simp [GlobalState.rootPointerTag,absent,GlobalState.newPointerTag,room,rootedGlobal,
    bind,Except.bind,pure,Pure.pure,Except.pure]

theorem root_cached (global : GlobalState) (id : AllocId) (next : BorTag)
    (absent : global.rootTag? id = none) :
    (rootedGlobal global id next).rootTag? id = some global.nextPointerTag := by
  have missing : global.rootPointerTags.find? (fun row => row.1 == id) = none := by
    cases found : global.rootPointerTags.find? (fun row => row.1 == id) with
    | none => rfl
    | some row => simp [GlobalState.rootTag?,found] at absent
  simp [rootedGlobal,GlobalState.rootTag?,Array.find?_push,missing]

/-- The actual stack-extra initializer uses the same allocated root tag and
new tree as the capability below. Its shared extras update stays explicit. -/
theorem init_extra {K U P : Type} [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P)
    (before : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (size : Size) (align : Align) (next : BorTag)
    (enabled : before.borrowTracker = some tracker)
    (absent : tracker.global.rootTag? id = none)
    (room : BorTag.succ tracker.global.nextPointerTag = some next)
    (race : before.dataRace = none)
    (noExtras : ((extras.get before.user).allocations.any (fun row => row.1 == id)) = false) :
    PlaceMachine.initStackExtra (fun id _ _ => MemoryExtras.initAllocation extras id false) id size align before =
      .ok (BorrowTree.new tracker.global.nextPointerTag size)
        (MemoryExtras.putAllocation extras
          {before with borrowTracker := some {tracker with global := rootedGlobal tracker.global id next}}
          id ⟨none,#[]⟩) := by
  have allocated := root_created tracker.global id next absent room
  simp only [PlaceMachine.initStackExtra,enabled,allocated,race,MemoryExtras.initAllocation,noExtras,
    MemoryExtras.putAllocation,get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    modify,modifyGet,MonadStateOf.modifyGet,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,EStateM.tryCatch,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,Bool.false_eq_true,ite_false]

/-- Actual checked backing creation, actual fresh root allocation, and actual
new-tree constructors supply the base issuance capability once THAT allocation
is installed in the post heap. No final root witness or old capability is an
input. This establishes allocation-origin issuance, not active permissions. -/
theorem create (tracker : MachineHooks.BorrowState) (id : AllocId) (next : BorTag)
    (absent : tracker.global.rootTag? id = none)
    (room : BorTag.succ tracker.global.nextPointerTag = some next)
    (size : Size) (init : AllocInit) (bytes : Array UInt8)
    (storage : Size → Align → Option (Array UInt8))
    (provided : storage size Align.ONE = some bytes)
    (length : bytes.size = size.bytes.toNat)
    (zero : ∀ i (h : i < bytes.size), bytes[i] = 0) :
    ∃ allocation : Allocation Provenance Unit,
      Allocation.tryNew size Align.ONE init storage = .ok allocation ∧
      tracker.global.rootPointerTag id = .ok (rootedGlobal tracker.global id next,tracker.global.nextPointerTag) ∧
      ∀ post : Before,
        let installed := allocation.withExtra (BorrowTree.new tracker.global.nextPointerTag size)
        let postTracker := {tracker with global := rootedGlobal tracker.global id next}
        Present (ActualWorld post) id installed →
        AllocationCapability post postTracker id installed ∧
        ∀ completion, SpatialDelegation post postTracker id installed completion allocationRoot := by
  obtain ⟨allocation,created,extent,sizeEq,_,_,_,_,_⟩ :=
    AllocationStorageFormation.create (Prov := Provenance) size init bytes storage provided length zero
  refine ⟨allocation,created,root_created tracker.global id next absent room,?_⟩
  intro post
  dsimp only
  intro present
  have capability : AllocationCapability post {tracker with global := rootedGlobal tracker.global id next} id
      (allocation.withExtra (BorrowTree.new tracker.global.nextPointerTag size)) := by
    refine ⟨present,?_,?_,?_,?_⟩
    · change allocation.len = allocation.byteSize.bytes.toNat
      rw [sizeEq]
      exact extent
    · change (BorrowTree.new tracker.global.nextPointerTag size).locations.size = allocation.byteSize
      rw [sizeEq]
      cases size with
      | mk bytes =>
        by_cases zero : bytes = 0
        · subst bytes
          rfl
        · simp [BorrowTree.new,Miri.DataStructures.DedupRangeMap.new,
            Miri.DataStructures.DedupRangeMap.size,zero,Size.ofBytes]
    · rfl
    · refine ⟨_,BorrowTree.new_root_node _ _,rfl,rfl,?_⟩
      exact root_cached tracker.global id next absent
  exact ⟨capability,fun _ => SpatialDelegation.allocated capability⟩

end DuplicatePrefix.CurrentCallAllocationFormation
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallAllocationFormation.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved allocation formation dependency {dependency}"
