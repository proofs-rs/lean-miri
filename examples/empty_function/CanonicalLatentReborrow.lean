import empty_function.CanonicalLatentAt
import empty_function.LatentRetagPost
namespace EmptyFunction.CanonicalLatentReborrow
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem registered_world (machine : ChoiceExecution.S) (tracker : MachineHooks.BorrowState)
    (tag : BorTag) (world : TreeRuntimeInput.World machine tracker)
    (below : tag.value.toNat < tracker.global.nextPointerTag.value.toNat) :
    TreeRuntimeInput.World (registeredMachine machine tracker tag) (registeredTracker tracker tag) := by
  refine ⟨rfl,⟨?_,world.globals.rootsBelow⟩,world.liveTrees⟩
  intro row member
  change row ∈ (tracker.global.protectedTags.entries.filter fun entry => entry.1 != tag).push (tag,.StrongProtector) at member
  rcases Array.mem_push.mp member with prior | same
  · exact world.globals.protectedBelow row (Array.mem_filter.mp prior).1
  · subst row
    exact below

/-- Raw-anchor canonical lazy materialization joins the real zero reborrow.
Check/resolve are internal preflight equations, while ensure, constructor,
release certificate and the full physical-memory update follow here from raw
source input and the actual reserved-tag prefix. -/
theorem reborrow (s : WholeCall.Static) (p : WholeCall.Packet) (budget : Nat)
    (metadata : Specification.Metadata s) (input : InputDraft.CurrentInputDraft s p)
    (resources : Specification.ResourceMargins s p)
    (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : ChoiceExecution.S) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses)
    (runtime : machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (tape : ChoiceExecution.tapeAccess.get machine = ChoiceExecution.tapeAccess.get p.before.machine)
    (thread : machine.threads.activeThread = p.before.machine.threads.activeThread)
    (world : TreeRuntimeInput.World machine tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+(resources.budget-1) < 2^64)
    (noRace : machine.dataRace = none) (reserved : BorTag) (fence : RootReservedPost.Fence tracker.global reserved)
    (id : AllocId) (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (ordinary : ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      p.before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩)
    (place : MPlaceTy Provenance) (offset : UInt64) (parent : ProvenanceExtra)
    (parentBinding : parent = .wildcard ∨ ∃ tag, parent = .concrete tag ∧ tracker.global.rootTag? id = some tag)
    (check : s.cfg.retag.checkPtrAccess place.mplace.ptr Size.ZERO (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine))
    (resolve : s.cfg.retag.resolveAllocation place.mplace.ptr (withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (withCurrent frames frame machine))
    (log : s.cfg.retag.logCreation = fun _ _ _ _ _ => pure ())
    (precise : s.cfg.retag.preciseInteriorMut = pure false)
    (freeze : s.cfg.retag.typeIsFreeze place.layout.ty = pure true) :
    ∃ (ensuredMachine : ChoiceExecution.S) (ensuredTracker : MachineHooks.BorrowState)
      (entry : InputDraft.Entry) (tree : BorrowTree),
      TypedRetag.reborrow s.cfg.retag budget place Size.ZERO MachineHooks.protectionPolicy reserved
        (withCurrent frames frame machine) =
        .ok (some (.concrete id reserved))
          (withCurrent frames (registeredFrame frame borrowFrame id reserved)
            {ensuredMachine with memory := replaceTree ensuredMachine.memory id entry tree}) ∧
      ensuredMachine.borrowTracker = some ensuredTracker ∧
      ensuredTracker.global.protectedTags = (registeredTracker tracker reserved).global.protectedTags ∧
      tree.releaseProtector reserved ensuredTracker.global.protectedTags = ⟨tree,.Released⟩ ∧
      replaceTree ensuredMachine.memory id entry tree =
        {machine.memory with live := ((machine.memory.live.filter fun row => row.1 != id).push
          (id,{entry with allocation := entry.allocation.setExtra tree}))} ∧
      ensuredMachine.threads = machine.threads ∧
      RelocationContext.view ensuredMachine.user.payload = RelocationContext.view machine.user.payload ∧
      (∀ oldId tag, tracker.global.rootTag? oldId = some tag → ensuredTracker.global.rootTag? oldId = some tag) ∧
      Preservation.ExistingAddressFacts (withCurrent frames frame machine) (withCurrent frames frame ensuredMachine) := by
  let current := withCurrent frames (registeredFrame frame borrowFrame id reserved)
    (registeredMachine machine tracker reserved)
  let prefixTracker := registeredTracker tracker reserved
  have prefixWorld : TreeRuntimeInput.World current.machine prefixTracker :=
    registered_world machine tracker reserved world fence.1
  obtain ⟨converted,middle,afterTracker,global,root,attributes,ensured,live,installedWorld,distinct,
      finalFence,middleMemory,protectedEq,_trackedEq,rootStable,threadsPost,_runtimePost,contextPost,rootsPost,addressPost⟩ := CanonicalLatentAt.ensure
    s p metadata input resources current memory addresses runtime tape thread prefixTracker prefixWorld tagRoom noRace
    reserved fence id source selected absent noFunction noVaList descriptor ordinary
  let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
  let adjusted := MemoryExtras.putAllocation (CanonicalLatentMemory.extras s)
    {middle with borrowTracker := some {afterTracker with global}} id ⟨none,#[]⟩
  let installed := LatentInstallPost.installed adjusted id .global allocation
  let entry : InputDraft.Entry := ⟨.machine .global,allocation⟩
  have entryTree : entry.allocation.extra = BorrowTree.new root source.byteSize := rfl
  have treeFormed : TreeRuntimeInput.TreeFormed (BorrowTree.new root source.byteSize) global.nextPointerTag := by
    exact Classical.choice (installedWorld.liveTrees (id,entry) (Array.mem_of_find?_eq_some live))
  have shape : parent = .wildcard ∨ parent = .concrete root := by
    rcases parentBinding with wild | ⟨tag,concrete,cached⟩
    · exact Or.inl wild
    · have same : root = tag := rootStable tag cached
      exact Or.inr (concrete.trans (congrArg ProvenanceExtra.concrete same.symm))
  obtain ⟨tree,constructed,released⟩ := LatentRetagPost.new_tree root global.nextPointerTag reserved source.byteSize
    treeFormed distinct parent shape (Size.ofBytes offset) ⟨.ReservedFrz false,false,.None⟩ global.protectedTags
  have information : machine.memory.getAllocInfo id =
      .ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩ := by
    rw [memory]
    unfold MemoryState.hasVaListId at noVaList
    simp [MemoryState.getAllocInfo,absent,noFunction,noVaList,descriptor,pure,Pure.pure,Except.pure]
  have actual := LatentRetagPost.reborrow_after_ensure s.cfg.retag budget place frames frame borrowFrame machine tracker
    enabled frameBorrow id offset parent reserved check resolve log precise freeze _ information rfl installed ensured entry live tree constructed
  refine ⟨installed,{afterTracker with global},entry,tree,actual,rfl,protectedEq,released,?_,threadsPost,contextPost,rootsPost,addressPost⟩
  change middle.memory = machine.memory at middleMemory
  simp [replaceTree,installed,LatentInstallPost.installed,adjusted,MemoryExtras.putAllocation,middleMemory,
    Array.filter_filter]
end EmptyFunction.CanonicalLatentReborrow
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalLatentReborrow.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical latent reborrow axiom {dependency} in {name}"
