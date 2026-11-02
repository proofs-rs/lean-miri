import empty_function.RelocationResources
namespace EmptyFunction.RelocationBinding
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- A current memory descriptor is not a foreign declaration, so its resolved
runtime backing ID is its own runtime AllocId. -/
theorem memory_resolved (s : WholeCall.Static) (before : WholeCall.State) (id : AllocId)
    (target : InputDraft.RelocationTarget s before id) (value : Allocation CtfeProvenance Unit)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,value.byteSize,value.align,value.mutability,some (.memory value)⟩) : target.resolved = id := by
  cases target.mapping with
  | direct same _ _ _ => exact same
  | foreign global definition query payload _ =>
    have same := Option.some.inj (query.symm.trans descriptor)
    cases same
    cases payload

/-- Raw source target metadata supplies both current generator representation
and normalized alignment for the actual queried target layout. -/
theorem generation_alignment (s : WholeCall.Static) (before : WholeCall.State)
    (source : Allocation CtfeProvenance Unit) (input : InputDraft.RelocationInput s before source)
    (row : Size × CtfeProvenance) (member : row ∈ source.provenanceMap.ptrs)
    (value : Allocation CtfeProvenance Unit) (info : AllocationInfo)
    (descriptor : before.machine.memory.findGlobal? row.2.allocId = some
      ⟨row.2.allocId,.memory,value.byteSize,value.align,value.mutability,some (.memory value)⟩)
    (missing : before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = none)
    (metadata : before.machine.memory.getAllocInfo row.2.allocId = .ok info) (notType : info.kind ≠ .typeId) :
    ∃ generation, InputDraft.GenerationRepresentation before generation ∧ InputDraft.AlignmentRepresentation info.align := by
  obtain ⟨target⟩ := input.targets row member
  have identity := memory_resolved s before row.2.allocId target value descriptor
  have uncached : before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == target.resolved) = none := by
    simpa only [identity] using missing
  have alignment := target.uncachedAlignment uncached info (by simpa only [identity] using metadata)
  obtain ⟨generation,representation⟩ := input.generation ⟨row,member,target,uncached,info,by simpa only [identity] using metadata,notType⟩
  exact ⟨generation,representation,alignment⟩

/-- The first actual source relocation has the first actual direct demand;
foreign/shim branches cannot be fabricated for a current memory descriptor. -/
theorem memory_head (s : WholeCall.Static) (before : WholeCall.State)
    (source : Allocation CtfeProvenance Unit) (binding : SourceChoicePlan.Binding s before source)
    (row : Size × CtfeProvenance) (rest : List (Size × CtfeProvenance))
    (rows : source.provenanceMap.ptrs.toList = row::rest)
    (value : Allocation CtfeProvenance Unit)
    (descriptor : before.machine.memory.findGlobal? row.2.allocId = some
      ⟨row.2.allocId,.memory,value.byteSize,value.align,value.mutability,some (.memory value)⟩) :
    ∃ tail, binding.demands = some row.2.allocId :: tail := by
  cases binding with
  | mk demands correspondence =>
    rw [rows] at correspondence
    cases correspondence with
    | cons relation tail =>
      cases relation with
      | direct _ _ => exact ⟨_,rfl⟩
      | foreign global definition backing query payload _ =>
        have same := Option.some.inj (query.symm.trans descriptor)
        cases same
        cases payload

private theorem fits_mpr {m n : Nat} (h : Plan m = Plan n) (dimensions : m = n)
    (plan : Plan n) (tape : ExecutionChoices.Tape) :
    @Fits m (h.mpr plan) tape ↔ @Fits n plan tape := by
  cases dimensions
  rfl

/-- Peel precisely one actual source-derived demand. Future failure/choice
behavior is retained in the arbitrary actual ordered continuation. -/
theorem first_fits (s : WholeCall.Static) (before : WholeCall.State)
    (source : Allocation CtfeProvenance Unit) (binding : SourceChoicePlan.Binding s before source)
    (environment : SourceChoicePlan.Environment binding) (id : AllocId) (tail : List (Option AllocId))
    (demands : binding.demands = some id::tail) (info : AllocationInfo)
    (missing : before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) = none)
    (metadata : before.machine.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive id = true) :
    Fits (AddressChoicePlan.attempt before.machine.user.addresses id
      ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩
      (SourceChoicePlan.ordered before tail)) before.machine.user.payload.payload.user.choices := by
  have fitted := environment.fits
  change Fits (SourceChoicePlan.ordered before binding.demands before.machine.user.addresses)
    before.machine.user.payload.payload.user.choices at fitted
  rw [demands] at fitted
  simp only [SourceChoicePlan.ordered,SourceChoicePlan.info,missing,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
    metadata,Except.map,beq_iff_eq,notDead,notType,live,List.length_cons] at fitted
  have dimensions : 3*(tail.length+1) = 3*tail.length+3 := by omega
  exact (fits_mpr (congrArg Plan dimensions) dimensions _ _).mp fitted
/-- Exact remaining raw-row correspondence from the same source binding. -/
theorem tail_rows (s : WholeCall.Static) (before : WholeCall.State)
    (source : Allocation CtfeProvenance Unit) (binding : SourceChoicePlan.Binding s before source)
    (row : Size × CtfeProvenance) (rest : List (Size × CtfeProvenance))
    (tail : List (Option AllocId)) (rows : source.provenanceMap.ptrs.toList = row::rest)
    (demands : binding.demands = some row.2.allocId :: tail) :
    SourceChoicePlan.Rows (fun row demand => SourceChoicePlan.Demand s before row.2.allocId demand) rest tail := by
  have correspondence := binding.correspondence
  rw [rows,demands] at correspondence
  cases correspondence with
  | cons _ tail => exact tail
end EmptyFunction.RelocationBinding
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationBinding.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation binding axiom {dependency} in {name}"
