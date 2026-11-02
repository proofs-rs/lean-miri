import empty_function.RelocationRoot
namespace EmptyFunction.RawRootAdmission
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
/-- Pure current declaration/supplier metadata for the normal root path.
This covers ordinary memory, internal statics, functions, vtables, type IDs,
va-lists and machine functions; no root/address operation appears here. -/
structure Normal {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) : Prop where
  supplier : (∃ global, memory.findGlobal? id = some global) ∨
    memory.hasExtraFunctionId id = true ∨ memory.hasVaListId id = true
  predicates : ∀ global, memory.findGlobal? id = some global → global.kind = .static →
    ∃ definition isStatic tls foreign, global.payload = some (.static definition isStatic tls foreign)
  format : ∀ global, memory.findGlobal? id = some global → ∀ definition isStatic tls foreign,
    global.payload = some (.static definition isStatic tls foreign) → tls = false ∧ foreign = false

/-- The direct raw CTFE mapping already contains precisely this admission.
A foreign constructor contradicts the direct demand's compiler format. -/
theorem direct (s : WholeCall.Static) (before : WholeCall.State) (declared resolved : AllocId)
    (mapping : ExternMapping.Target s before declared resolved)
    (format : ∀ global, before.machine.memory.findGlobal? declared = some global →
      ∀ definition isStatic tls foreign, global.payload = some (.static definition isStatic tls foreign) →
        tls = false ∧ foreign = false) : Normal before.machine.memory declared := by
  cases mapping with
  | direct _ supplier predicates safe => exact ⟨supplier,predicates,safe⟩
  | foreign global definition query payload _ =>
    have impossible := (format global query definition true false true payload).2
    cases impossible

/-- Only the declaration prelude changes across normal target kinds. The
actual root-tag/address/wrapping operations remain the canonical source ones. -/
theorem root_address {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (offset base : UInt64) (root : BorTag)
    (global : GlobalState) (after : MachineAddress.State K U)
    (admission : Normal before.memory provenance.allocId)
    (enabled : before.borrowTracker = some tracker)
    (tagged : tracker.global.rootPointerTag provenance.allocId = .ok (global,root))
    (address : MachineAddress.addrFromAllocId choices hooks provenance.allocId (some .other)
      {before with borrowTracker := some {tracker with global}} = .ok base after)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    PointerSource.globalRootPointer choices hooks externStatic (Pointer.new provenance (Size.ofBytes offset)) before =
      .ok (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes (base+offset))) after := by
  have wrapping : (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)).wrappingOffset
      (Size.ofBytes offset) ⟨Size.ofBytes 8⟩ =
      .ok (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes (base+offset))) :=
    RelocationRoot.wrapping_offset_u64
      (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)) (Size.ofBytes offset)
  simp only [Pointer.new] at wrapping
  cases query : before.memory.findGlobal? provenance.allocId with
  | none =>
    have supplier : before.memory.hasExtraFunctionId provenance.allocId = true ∨ before.memory.hasVaListId provenance.allocId = true := by
      rcases admission.supplier with ⟨row,found⟩ | machine
      · rw [query] at found; cases found
      · exact machine
    have present : (before.memory.hasExtraFunctionId provenance.allocId || before.memory.hasVaListId provenance.allocId) = true := by
      rcases supplier with left | right <;> simp [*]
    simp only [PointerSource.globalRootPointer,Pointer.new,query,present,↓reduceIte,enabled,tagged,
      get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
      bind,EStateM.bind,pure,EStateM.pure,address,width]
    rw [wrapping]
    rfl
  | some descriptor =>
    cases payload : descriptor.payload with
    | none =>
      have notStatic : descriptor.kind ≠ .static := by
        intro kind
        obtain ⟨definition,isStatic,tls,foreign,shape⟩ := admission.predicates descriptor query kind
        rw [payload] at shape
        cases shape
      simp only [PointerSource.globalRootPointer,Pointer.new,query,payload,beq_iff_eq,notStatic,↓reduceIte,enabled,tagged,
        get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
        bind,EStateM.bind,pure,EStateM.pure,address,width]
      rw [wrapping]
      rfl
    | some value =>
      cases value with
      | static definition isStatic tls foreign =>
        obtain ⟨tlsFalse,foreignFalse⟩ := admission.format descriptor query definition isStatic tls foreign payload
        simp only [PointerSource.globalRootPointer,Pointer.new,query,payload,tlsFalse,foreignFalse,Bool.false_eq_true,↓reduceIte,enabled,tagged,
          get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          bind,EStateM.bind,pure,EStateM.pure,address,width]
        rw [wrapping]
        rfl
      | memory _ | function | vtable | typeId =>
        simp only [PointerSource.globalRootPointer,Pointer.new,query,payload,enabled,tagged,
          get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          bind,EStateM.bind,pure,EStateM.pure,address,width]
        rw [wrapping]
        rfl
end EmptyFunction.RawRootAdmission
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RawRootAdmission.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved raw root admission axiom {dependency} in {name}"
