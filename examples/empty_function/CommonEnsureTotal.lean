import empty_function.CanonicalEnsureRoute
namespace EmptyFunction.CommonEnsureTotal
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.MaterializationPreservation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Internal sequential conversion post, supplied by the actual finite root
callback fold. It is not a caller-validity or metadata field. -/
structure ConversionPost (current : State) (middle : ChoiceExecution.S) where
  tracker : MachineHooks.BorrowState
  world : TreeRuntimeInput.World middle tracker
  memory : middle.memory = current.machine.memory
  threads : middle.threads = current.machine.threads
  runtime : middle.user.payload.payload.user.runtime = current.machine.user.payload.payload.user.runtime
  context : RelocationContext.view middle.user.payload = RelocationContext.view current.machine.user.payload
  race : middle.dataRace = current.machine.dataRace
  tables : InputDraft.AddressTables {current with machine := middle}
  addresses : Preservation.ExistingAddressFacts current {current with machine := middle}

/-- Derived outcomes of the actual canonical source ensure. Resource failures
are allowed; success supplies only the state needed by unit retag/return. -/
def Outcome (s : Static) (p : Packet) (id : AllocId) (current : State) : Prop :=
  (∃ error failed, s.cfg.retag.ensureTreeExtra id current = .error error failed ∧ RunLoop.reportsUB error = false) ∨
  (∃ after tracker entry,
    s.cfg.retag.ensureTreeExtra id current = .ok () {current with machine := after} ∧
    TreeRuntimeInput.World after tracker ∧
    after.memory.live.find? (fun row => row.1 == id) = some (id,entry) ∧
    ProtectionOutcome.Stable current.machine after ∧
    Preservation.OriginalLiveAllocations p.before {current with machine := after} ∧
    FootprintAfter.Geometry p.before {current with machine := after} ∧
    Preservation.ExistingAddressFacts p.before {current with machine := after})

private theorem live_row (machine : ChoiceExecution.S) (id : AllocId)
    (allocation : Allocation Provenance BorrowTree) :
    (GlobalErrorAware.installed machine id .global allocation).memory.live.find? (fun row => row.1 == id) =
      some (id,⟨.machine .global,allocation⟩) := by
  have removed : (machine.memory.live.filter fun row => row.1 != id).find? (fun row => row.1 == id) = none := by
    apply Array.find?_eq_none.mpr
    intro row member same
    have notSame : (row.1 == id) = false := by
      simpa only [bne,Bool.not_eq_true'] using (Array.mem_filter.mp member).2
    rw [same] at notSame
    cases notSame
  simp only [GlobalErrorAware.installed,Array.find?_push,removed,beq_self_eq_true,↓reduceIte,Option.or]

/-- Compose the finite conversion's two actual outcomes with source-tree
initialization and canonical getter insertion. Every premise mentioning an
operation belongs to this internal stage contract and is discharged by the
raw-input conversion theorem in the public ensure wrapper. -/
theorem from_conversion (s : Static) (metadata : Specification.Metadata s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (id : AllocId) (sourceBytes : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedSource s p id sourceBytes)
    (current : State) (memory : current.machine.memory = p.before.machine.memory)
    (addresses : current.machine.user.addresses = p.before.machine.user.addresses)
    (runtime : current.machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (noRace : current.machine.dataRace = none)
    (conversion :
      (∃ converted middle,
        Allocation.adjustFromTcx sourceBytes s.prepared.compiler.runtime.target.base
          (fun _ _ state => .ok (RelocationBytePrimitives.snapshot sourceBytes) state)
          (globalLeaves s).globalRootPointer current.machine = .ok converted middle ∧
        RelocationByteFold.Attributes sourceBytes converted ∧ Nonempty (ConversionPost current middle)) ∨
      (∃ error failed,
        Allocation.adjustFromTcx sourceBytes s.prepared.compiler.runtime.target.base
          (fun _ _ state => .ok (RelocationBytePrimitives.snapshot sourceBytes) state)
          (globalLeaves s).globalRootPointer current.machine = .error (.pointerAdjustment error) failed ∧
        RunLoop.reportsUB error = false)) : Outcome s p id current := by
  have prepare := CanonicalDictionaries.global_bytes_prepare s.prepared.compiler s.prepared.image s.prepared s.options.place.debugAssertions
    id (RelocationBytePrimitives.snapshot sourceBytes) sourceBytes.align
  rcases conversion with ⟨converted,middle,actual,attributes,⟨post⟩⟩ | ⟨error,failed,actual,nonUB⟩
  · have vacancy := (SelectedMaterializationFacts.facts s p input id sourceBytes selected).2
    have middleVacant : ((extras s).get middle.user).allocations.any (fun row => row.1 == id) = false := by
      change middle.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false
      rw [post.runtime,runtime]
      exact vacancy
    rcases GlobalErrorAware.adjust_after_conversion s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
      id sourceBytes converted current.machine middle post.tracker prepare rfl actual attributes post.world
      (post.race.trans noRace) middleVacant with
      ⟨global,root,tagged,adjusted,world⟩ | ⟨error,failed,adjusted,nonUB⟩
    · let allocation := converted.mapExtra (fun _ => BorrowTree.new root sourceBytes.byteSize)
      let registered := MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {post.tracker with global}} id ⟨none,#[]⟩
      let installed := GlobalErrorAware.installed registered id .global allocation
      have tree := RootTreePost.root_operation post.tracker.global global id root sourceBytes.byteSize post.world.globals tagged
      have formed := MaterializationPreservation.installed_world registered {post.tracker with global} id .global allocation world tree
      refine Or.inr ⟨installed,{post.tracker with global},⟨.machine .global,allocation⟩,
        CanonicalEnsureRoute.owned s metadata p id sourceBytes selected current memory allocation registered adjusted,
        formed,live_row registered id allocation,?_,?_,?_,?_⟩
      · exact MaterializationPreservation.stable s current.machine middle post.tracker global id allocation
          post.threads post.race post.context
      · apply MaterializationPreservation.original_live p.before {current with machine := installed} id ⟨.machine .global,allocation⟩
          (SelectedMaterializationFacts.absent s p id sourceBytes selected)
        change (middle.memory.live.filter fun row => row.1 != id).push (id,⟨.machine .global,allocation⟩) = _
        rw [post.memory,memory]
      · exact ⟨{current with machine := middle},post.memory.trans memory,rfl,post.tables⟩
      · have kept : installed.user.addresses = middle.user.addresses :=
          MaterializationPreservation.addresses s middle post.tracker global id allocation
        simpa only [Preservation.ExistingAddressFacts,kept,addresses] using post.addresses
    · exact Or.inl ⟨error,_,CanonicalEnsureRoute.error s metadata p id sourceBytes selected current memory error failed adjusted,nonUB⟩
  · have adjusted := GlobalErrorAware.adjust_conversion_error s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
      id sourceBytes current.machine failed (.pointerAdjustment error) prepare actual
    exact Or.inl ⟨error,_,CanonicalEnsureRoute.error s metadata p id sourceBytes selected current memory error failed adjusted,nonUB⟩
end EmptyFunction.CommonEnsureTotal

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CommonEnsureTotal.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common-ensure axiom {dependency} in {name}"
