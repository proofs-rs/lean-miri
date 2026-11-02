import empty_function.RelocationCallback
import empty_function.AddressPartialByteFold
namespace EmptyFunction.RelocationPartialFold
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
abbrev S := ChoiceExecution.S

def Needed (s : WholeCall.Static) (anchor : WholeCall.State) (source : Allocation CtfeProvenance Unit) : Prop :=
  ∃ row ∈ source.provenanceMap.ptrs, ∃ target : InputDraft.RelocationTarget s anchor row.2.allocId,
    anchor.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == target.resolved) = none ∧
    ∃ info,anchor.machine.memory.getAllocInfo target.resolved = .ok info ∧ info.kind ≠ .typeId

structure Invariant (anchor : WholeCall.State) (initial : S) (original : MachineHooks.BorrowState)
    (needed : Prop) (current : S) where
  tracker : MachineHooks.BorrowState
  world : TreeRuntimeInput.World current tracker
  memory : current.memory = anchor.machine.memory
  threads : current.threads = initial.threads
  runtime : current.user.payload.payload.user.runtime = anchor.machine.user.payload.payload.user.runtime
  context : RelocationContext.view current.user.payload = RelocationContext.view initial.user.payload
  race : current.dataRace = none
  frame : RootFramePost.Frame original.global tracker.global
  bases : ∀ id row,anchor.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
    current.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row
  static : AddressStaticPost.view current.user.addresses = AddressStaticPost.view anchor.machine.user.addresses
  tables : InputDraft.AddressTables {anchor with machine := current}
  generation : needed → ∃ next,InputDraft.GenerationRepresentation {anchor with machine := current} next

private def advance {anchor : WholeCall.State} {initial : S} {original : MachineHooks.BorrowState}
    {needed : Prop} {current final : S} (old : Invariant anchor initial original needed current)
    (post : RelocationCallbackPost.Post {anchor with machine := current} old.tracker needed final) :
    Invariant anchor initial original needed final :=
  ⟨{old.tracker with global := post.global},post.world,post.memory.trans old.memory,
    post.threads.trans old.threads,post.runtime.trans old.runtime,post.context.trans old.context,post.race.trans old.race,
    RootFramePost.trans original.global old.tracker.global post.global old.frame post.frame,
    (by intro id row prior;exact post.bases id row (old.bases id row prior)),
    post.static.trans old.static,post.tables,post.generation⟩

private theorem cached_or_type (s : WholeCall.Static) (anchor : WholeCall.State)
    (source : Allocation CtfeProvenance Unit) (row : Size × CtfeProvenance) (member : row ∈ source.provenanceMap.ptrs)
    (target : InputDraft.RelocationTarget s anchor row.2.allocId) (current : S)
    (memory : current.memory = anchor.machine.memory)
    (bases : ∀ id entry,anchor.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some entry →
      current.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some entry)
    (notNeeded : ¬Needed s anchor source) :
    RelocationRootStep.CachedOrTypeId {anchor with machine := current} target.resolved := by
  classical
  cases cached : anchor.machine.user.addresses.baseAddr.find? (fun old => old.allocId == target.resolved) with
  | some entry =>
    have identity : entry.allocId = target.resolved := by simpa only [beq_iff_eq] using Array.find?_some cached
    have same : entry = ⟨target.resolved,entry.address⟩ := by cases entry;simp_all
    have retained := bases target.resolved entry cached
    rw [same] at retained
    exact .inl ⟨_,retained⟩
  | none =>
    obtain ⟨info,metadata⟩ := RawResources.backing_info anchor target.resolved target.backing
    have typeId : info.kind = .typeId := by
      by_cases same : info.kind = .typeId
      · exact same
      · exact False.elim (notNeeded ⟨row,member,target,cached,info,metadata,same⟩)
    exact .inr ⟨info,by rw [memory];exact metadata,typeId,by rw [memory];exact target.live⟩

structure Post (current : WholeCall.State) (original : MachineHooks.BorrowState) (final : S) where
  tracker : MachineHooks.BorrowState
  world : TreeRuntimeInput.World final tracker
  memory : final.memory = current.machine.memory
  threads : final.threads = current.machine.threads
  runtime : final.user.payload.payload.user.runtime = current.machine.user.payload.payload.user.runtime
  context : RelocationContext.view final.user.payload = RelocationContext.view current.machine.user.payload
  race : final.dataRace = current.machine.dataRace
  frame : RootFramePost.Frame original.global tracker.global
  tables : InputDraft.AddressTables {current with machine := final}
  addresses : Preservation.ExistingAddressFacts current {current with machine := final}

/-- All finite raw relocations and all actual choice outcomes. Byte failures
are excluded by raw compiler windows; callback failures remain genuine typed
non-UB stops. No numeric room, seed, quota, or future-success premise occurs. -/
theorem convert (s : WholeCall.Static) (anchor : WholeCall.State)
    (source : Allocation CtfeProvenance Unit) (raw : InputDraft.RelocationInput s anchor source)
    (tables : InputDraft.AddressTables anchor)
    (current : S) (memory : current.memory = anchor.machine.memory)
    (addresses : current.user.addresses = anchor.machine.user.addresses)
    (runtime : current.user.payload.payload.user.runtime = anchor.machine.user.payload.payload.user.runtime)
    (tracker : MachineHooks.BorrowState) (world : TreeRuntimeInput.World current tracker)
    (noRace : current.dataRace = none) (layout : TargetDataLayout) (hooks : ChoiceExecution.H)
    (width : layout.pointerWidth = .w64) (pointerWidth : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ converted final,
      Allocation.adjustFromTcx source layout (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
        (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks (ForeignResolverPrelude.resolver s hooks)) current = .ok converted final ∧
      RelocationByteFold.Attributes source converted ∧ Nonempty (Post {anchor with machine := current} tracker final)) ∨
    (∃ error failed,
      Allocation.adjustFromTcx source layout (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
        (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks (ForeignResolverPrelude.resolver s hooks)) current =
          .error (.pointerAdjustment error) failed ∧ RunLoop.reportsUB error = false) := by
  classical
  let needed := Needed s anchor source
  let I := fun (_ : Nat) state => Nonempty (Invariant anchor current tracker needed state)
  have initial : I 0 current := by
    refine ⟨⟨tracker,world,memory,rfl,runtime,rfl,noRace,⟨rfl,rfl,by intro id tag prior;exact prior⟩,?_,?_,?_,?_⟩⟩
    · intro id row prior
      rw [addresses]
      exact prior
    · rw [addresses]
    · exact AddressTransport.tables anchor {anchor with machine := current} memory addresses tables
    · intro need
      obtain ⟨generation,rep⟩ := raw.generation need
      exact ⟨generation,AddressTransport.representation anchor {anchor with machine := current} memory addresses generation rep⟩
  have callback : ∀ index (valid : index < source.provenanceMap.ptrs.size) state,I index state →
      (∃ adjusted next,PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks (ForeignResolverPrelude.resolver s hooks)
        (Pointer.new source.provenanceMap.ptrs[index].2
          (Size.ofBytes (RelocationBytePrimitives.word layout (RelocationBytePrimitives.snapshot source) source.provenanceMap.ptrs[index].1.bytes.toNat))) state =
        .ok adjusted next ∧ I (index+1) next) ∨
      (∃ error failed,PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks (ForeignResolverPrelude.resolver s hooks)
        (Pointer.new source.provenanceMap.ptrs[index].2
          (Size.ofBytes (RelocationBytePrimitives.word layout (RelocationBytePrimitives.snapshot source) source.provenanceMap.ptrs[index].1.bytes.toNat))) state =
        .error error failed ∧ RunLoop.reportsUB error = false) := by
    intro index valid state ⟨old⟩
    have member := Array.getElem_mem valid
    obtain ⟨target⟩ := raw.targets source.provenanceMap.ptrs[index] member
    rcases RelocationCallback.step s anchor state hooks old.tracker old.world old.tables needed old.generation old.memory old.runtime old.bases
      source.provenanceMap.ptrs[index].2
      (RelocationBytePrimitives.word layout (RelocationBytePrimitives.snapshot source) source.provenanceMap.ptrs[index].1.bytes.toNat)
      target (fun notNeeded => cached_or_type s anchor source _ member target state old.memory old.bases notNeeded)
      old.race pointerWidth classifier with success | stopped
    · obtain ⟨pointer,final,actual,⟨post⟩⟩ := success
      exact .inl ⟨pointer,final,actual,⟨advance old post⟩⟩
    · exact .inr stopped
  rcases AddressPartialByteFold.convert source layout
    (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks (ForeignResolverPrelude.resolver s hooks)) I current width
      raw.physical.ordered raw.physical.windows raw.physical.fragments initial callback with success | stopped
  · obtain ⟨converted,final,actual,⟨post⟩,attrs,_keys,_fragments⟩ := success
    have finalMemory := post.memory.trans memory.symm
    have finalTables : InputDraft.AddressTables {{anchor with machine := current} with machine := final} := post.tables
    have bases : ∀ id row,current.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
        final.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row := by
      intro id row prior
      apply post.bases id row
      simpa only [addresses] using prior
    have static : AddressStaticPost.view final.user.addresses = AddressStaticPost.view current.user.addresses := by
      rw [post.static,addresses]
    refine .inl ⟨converted,final,actual,attrs,⟨⟨post.tracker,post.world,finalMemory,post.threads,
      post.runtime.trans runtime.symm,post.context,post.race.trans noRace.symm,post.frame,finalTables,?_⟩⟩⟩
    exact AddressStaticPost.facts {anchor with machine := current} {anchor with machine := final}
      (AddressTransport.tables anchor {anchor with machine := current} memory addresses tables) finalTables finalMemory bases static
  · exact .inr stopped
end EmptyFunction.RelocationPartialFold
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if ["EmptyFunction.LiveMetadata.","EmptyFunction.RelocationCallbackPost.","EmptyFunction.RelocationRootStep.",
        "EmptyFunction.RelocationCallback.","EmptyFunction.RelocationPartialFold."].any (fun label =>
          (name.toString.splitOn label).length != 1) then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual partial relocation axiom {dependency} in {name}"
