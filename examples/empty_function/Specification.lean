import empty_function.Program
import empty_function.InputDraft
import empty_function.Preservation
import empty_function.CanonicalDictionaries
import empty_function.ChoiceAdmission
import empty_function.PolicyChoiceAdmission
import empty_function.MetadataQueries

/-! Concrete candidate instantiation of the whole-call goal. These definitions
are reviewable proposals, not a safety theorem or an ordinary-input coverage
certificate. In particular resource sufficiency and arbitrary latent descriptor
conversion adequacy are still open. -/
namespace EmptyFunction.Specification
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open WholeCall
set_option autoImplicit false

/-- Pure compiler facts. The loader binds the selected instance to the actual
exported empty_function body; ABI/layout identities retain that instance's compiler data.
No whole compiler-document equality excludes additional caller metadata. -/
structure Metadata (s : Static) where
  construction : CanonicalDictionaries.Construction s.prepared.compiler
  /-- Source meaning is fixed while compilation-local syntax IDs may differ. -/
  body : Contents.body s.loaded.tables #[] s.loaded.body = .ok Program.contents
  loader : CallResolution.loadedBodyOfInstance s.prepared.compiler.lifecycle.calls.calls
    s.functionInstance = .ok s.loaded
  abi : CompilerInstanceAbi.abiOfInstance s.prepared.compiler.lifecycle.instances
    s.functionInstance #[] = .ok s.abi
  unit : s.prepared.compiler.primitiveLayout "unit" = .ok s.abi.ret.layout
  unitIgnored : s.abi.ret.mode = .Ignore
  noArguments : s.abi.args = #[]
  notVariadic : s.abi.cVariadic = false
  unitSized : s.abi.ret.layout.layout.isSized = true
  unitSize : s.abi.ret.layout.layout.size = Size.ZERO
  unitAlign : s.abi.ret.layout.layout.align.abi = Align.ONE
  unitBackend : s.abi.ret.layout.layout.backendRepr = .Memory (sized := true)
  target : s.prepared.compiler.runtime.target.base.pointerWidth = .w64
  /-- The selected callable is the ordinary item represented by the exported body. -/
  itemKind : s.functionInstance.kind = .Item s.functionInstance.defId
  inlineAttribute : CompilerVirtualFacts.inlineAttribute
    s.prepared.compiler.lifecycle.calls.scopes s.functionInstance = .ok none ∨
    CompilerVirtualFacts.inlineAttribute
      s.prepared.compiler.lifecycle.calls.scopes s.functionInstance = .ok (some false)
  trackCaller : CompilerRuntimeQueries.requiresCallerLocation
    s.prepared.compiler.lifecycle.calls.runtime s.functionInstance = .ok false
  targetFeatures : CompilerTargetFeatures.required
    s.prepared.compiler.intrinsics s.functionInstance = .ok #[]
  notClosure : CompilerCallFacts.isClosureLike
    s.prepared.compiler.intrinsics s.functionInstance = .ok false
  unitLookup : s.prepared.compiler.runtime.lookup s.abi.ret.layout.ty = .ok s.abi.ret.layout
  unitFields : s.abi.ret.layout.layout.fields = .Arbitrary #[] #[]
  unitVariants : s.abi.ret.layout.layout.variants = .Single 0
  unitKind : CompilerFactAdapters.validityKind s.prepared.compiler.lifecycle.calls.symbols.facts
    s.abi.ret.layout.ty = .ok (.aggregate false false false)
  unitInhabited : CompilerFacts.boolean s.prepared.compiler.lifecycle.calls.symbols.facts.context
    s.abi.ret.layout.ty "opsem_inhabited" = .ok true
  unitNode : ∃ node, s.prepared.compiler.lifecycle.calls.symbols.facts.context.runtime.node
    s.abi.ret.layout.ty = .ok node
  sourceReflexive : (s.prepared.compiler.runtime.source.raw == s.prepared.compiler.runtime.source.raw) = true
  unitFreeze : CompilerFacts.boolean s.prepared.compiler.lifecycle.calls.symbols.facts.context
    s.abi.ret.layout.ty "is_freeze" = .ok true
  unitStorageSized : CompilerStorage.veryTriviallySized
    s.prepared.compiler.runtime s.abi.ret.layout.ty = .ok true
  frameInlineAttribute : CompilerVirtualFacts.inlineAttribute
    s.prepared.compiler.lifecycle.frames.calls.scopes s.functionInstance = .ok none ∨
    CompilerVirtualFacts.inlineAttribute
      s.prepared.compiler.lifecycle.frames.calls.scopes s.functionInstance = .ok (some false)
  frameTrackCaller : CompilerRuntimeQueries.requiresCallerLocation
    s.prepared.compiler.lifecycle.frames.calls.runtime s.functionInstance = .ok false
  frameDefinition : ∃ definition,
    s.prepared.compiler.lifecycle.frames.calls.calls.program.compilerTables.definitions[s.functionInstance.defId]? = some definition
  /-- Normalization depends on the current frame's static body/instance key,
  while locals, memory, thread state and caches are unconstrained by this fact. -/
  normalizedLocal : ∀ frame : CompilerFrameContext.ActualFrame,
    frame.bodyIdentity = s.loaded.identity → Meaning.FrameMatches frame s.loaded →
    frame.functionInstance = s.functionInstance →
    CompilerFrameContext.normalizedLocalType s.prepared.compiler frame 0 = .ok s.abi.ret.layout.ty
  loweredBody : LoweredBody
  bodyRow : s.prepared.compiler.program.bundle.bodies[s.loaded.identity.index]? = some loweredBody
  lifecycleBody : s.prepared.compiler.lifecycle.lifecycle.program.bundle.bodies[s.loaded.identity.index]? =
    some loweredBody
  preamble : SpanRef
  lifecycleRow : s.prepared.compiler.lifecycle.lifecycle.entries[s.loaded.identity.index]? =
    some ⟨.ok preamble, .ok s.functionInstance, .ok #[]⟩
  localSpan : SpanRef
  localSourceSpan : ∃ decl, loweredBody.input.locals[0]? = some decl ∧
    s.prepared.compiler.program.bundle.spans.toList.idxOf? decl.sourceInfo.span = some localSpan.id
  /-- The literal is tied to the fixed instruction, not chosen to supply an
  operational result. Its exact structural site selects compiler evidence. -/
  literal : ConstOperand
  literalShape : literal.value = .Val .ZeroSized s.abi.ret.layout.ty
  literalStatement : ((Program.contents.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
    (fun statement => statement.kind) = some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes))
  /-- Missing query evidence is a checked stop. Successful evidence must retain
  the exported unit constant's normalization. -/
  constantNormalization : ∀ evidence,
    CompilerConstantQueries.lookup s.prepared.compiler.constants
      ⟨s.loaded.identity.index,Meaning.unitConstantId s.loaded.tables s.loaded.body
        Program.contents literal body literalStatement⟩ = .ok evidence →
    normalizationFromEvidence #[evidence] s.functionInstance literal.value = .ok literal.value

  /-- The default address-space pointer width agrees with the selected x86_64 target. -/
  pointerSize : s.prepared.compiler.runtime.target.pointerSize = Size.ofBytes 8

  /-- Rust type layouts use the pinned rustc_abi::Align representation (normal
  powers of two through exponent 29), unlike offset-analysis sentinel aligns.
  This is compiler data consistency, not a heap-allocation success condition. -/
  compilerLayoutAlignment : ∀ ty layout,
    s.prepared.compiler.runtime.lookup ty = .ok layout →
    InputDraft.AlignmentRepresentation layout.layout.align.abi

  /-- Canonical compiler span collection covers declarations in every imported
  body, including arbitrary callers whose locals are later materialized. -/
  compilerLocalSourceSpans : ∀ body ∈ s.prepared.compiler.program.bundle.bodies,
    ∀ decl ∈ body.input.locals, ∃ index,
      s.prepared.compiler.program.bundle.spans.toList.idxOf? decl.sourceInfo.span = some index

noncomputable def Metadata.literalId {s : Static} (metadata : Metadata s) : ConstantId :=
  Meaning.unitConstantId s.loaded.tables s.loaded.body Program.contents metadata.literal
    metadata.body metadata.literalStatement

theorem Metadata.literalReference {s : Static} (metadata : Metadata s) :
    Meaning.firstConstantId s.loaded.tables s.loaded.body = .ok metadata.literalId :=
  Meaning.unitConstantId_reference s.loaded.tables s.loaded.body Program.contents metadata.literal
    metadata.body metadata.literalStatement

/-- Availability is required by successful intermediate results, not by the
UB-freedom target. -/
class SuccessfulConstant {s : Static} (metadata : Metadata s) : Prop where
  query : ∃ evidence, CompilerConstantQueries.lookup s.prepared.compiler.constants
    ⟨s.loaded.identity.index,metadata.literalId⟩ = .ok evidence

noncomputable def Metadata.literalEvidence {s : Static} (metadata : Metadata s)
    [successful : SuccessfulConstant metadata] : CompilerConstantEvidence :=
  Classical.choose successful.query

theorem Metadata.literalQuery {s : Static} (metadata : Metadata s)
    [successful : SuccessfulConstant metadata] :
    CompilerConstantQueries.lookup s.prepared.compiler.constants
      ⟨s.loaded.identity.index,metadata.literalId⟩ = .ok metadata.literalEvidence :=
  Classical.choose_spec successful.query

theorem Metadata.literalNormalization {s : Static} (metadata : Metadata s)
    [SuccessfulConstant metadata] :
    normalizationFromEvidence #[metadata.literalEvidence]
      s.functionInstance metadata.literal.value = .ok metadata.literal.value :=
  metadata.constantNormalization metadata.literalEvidence metadata.literalQuery

theorem Metadata.bodyContents {s : Static} (metadata : Metadata s) :
    metadata.loweredBody.bodyId = s.loaded.bodyId ∧ metadata.loweredBody.body = s.loaded.body := by
  let token := LocalsIdentity.ofAllocationToken 0
  let frame : CompilerFrameContext.ActualFrame := Frame.create s.loaded s.functionInstance
    ⟨none,none,0,none⟩ (.stop false) (.frameLocal 0 0 none s.abi.ret.layout token)
    metadata.preamble token
  have known := metadata.normalizedLocal frame rfl (by exact ⟨rfl,rfl,rfl⟩) rfl
  have wire := CompilerFrameContext.normalizedLocalType_body s.prepared.compiler frame 0
    s.abi.ret.layout.ty metadata.loweredBody (by exact metadata.bodyRow) known
  exact wire

noncomputable def Metadata.entry {s : Static} (metadata : Metadata s) : Meaning.Entry :=
  Classical.choose (Meaning.firstConstantId_entry s.loaded.tables s.loaded.body
    metadata.literalId metadata.literalReference)

theorem Metadata.entry_constant {s : Static} (metadata : Metadata s) :
    metadata.entry.constant = metadata.literalId :=
  (Classical.choose_spec (Meaning.firstConstantId_entry s.loaded.tables s.loaded.body
    metadata.literalId metadata.literalReference)).1

theorem Metadata.entry_references {s : Static} (metadata : Metadata s) :
    metadata.entry.References s.loaded.tables s.loaded.body :=
  (Classical.choose_spec (Meaning.firstConstantId_entry s.loaded.tables s.loaded.body
    metadata.literalId metadata.literalReference)).2

theorem Metadata.entry_observations {s : Static} (metadata : Metadata s) :
    Contents.place s.loaded.tables metadata.entry.destination = .ok ⟨0,#[]⟩ ∧
      metadata.entry.retag = .Yes ∧
      Contents.constant s.loaded.tables metadata.entry.constant = .ok metadata.literal :=
  Meaning.entry_observations s.loaded.tables s.loaded.body Program.contents metadata.entry
    metadata.literal metadata.body metadata.entry_references metadata.literalStatement

/-- Header facts follow from the checked source meaning, independently of the
compilation-local numbers used for the referenced syntax nodes. -/
theorem Metadata.body_header (s : Static) (metadata : Metadata s) :
    s.loaded.body.argumentCount = 0 ∧ s.loaded.body.locals = #[0] ∧
      s.loaded.body.basicBlocks.size = 1 := by
  have actual := Meaning.body_metadata s.loaded.tables #[] s.loaded.body Program.contents metadata.body
  have fixed := Meaning.body_metadata Program.root.loaded.tables #[] Program.root.loaded.body
    Program.contents Program.contents_checked
  have blocks := Meaning.array_mapM_size _ _ _
    (Meaning.body_blocks s.loaded.tables #[] s.loaded.body Program.contents metadata.body)
  have fixedBlocks := Meaning.array_mapM_size _ _ _
    (Meaning.body_blocks Program.root.loaded.tables #[] Program.root.loaded.body Program.contents
      Program.contents_checked)
  refine ⟨actual.2.1.trans (fixed.2.1.symm.trans Program.no_arguments), ?_, ?_⟩
  · exact actual.2.2.2.trans (fixed.2.2.2.symm.trans (by rfl))
  · exact blocks.trans (fixedBlocks.symm.trans Program.one_block)


/-- The existing successful loader premise supplies cache validity; the checked
unit body's local range then leaves no implicit local to activate. -/
theorem Metadata.alwaysLive (s : Static) (metadata : Metadata s) :
    s.loaded.body.alwaysLive = #[] := by
  have valid := (CallResolution.loadedBodyOfInstance_tables
    s.prepared.compiler.lifecycle.calls.calls s.functionInstance s.loaded metadata.loader).2.2.2
  rw [Array.all_eq_true'] at valid
  apply Array.eq_empty_iff_forall_not_mem.mpr
  intro id selected
  have bounds := valid id selected
  simp only [(metadata.body_header s).1, (metadata.body_header s).2.1,
    Bool.and_eq_true, decide_eq_true_eq] at bounds
  change 0 < id ∧ id < 1 at bounds
  exact (Nat.not_lt_of_ge bounds.1) bounds.2


structure Profile (s : Static) : Prop where
  debug : s.options.place.debugAssertions = false
  precise : s.options.retag.preciseInteriorMut = false
  implicitWrites : s.options.retag.implicitWrites = false
  shallow : s.options.place.validation = .Shallow

structure RuntimeProfile (s : Static) (p : Packet) : Prop where
  noRace : p.before.machine.dataRace = none
  typesMetadata : p.before.machine.user.payload.payload.user.types.metadata = s.prepared.compiler.runtime
  unitNotConstructedArray : p.before.machine.user.payload.payload.user.types.entries.any
    (fun row => row.value.ty == s.abi.ret.layout.ty) = false
  fixedScheduling : p.before.machine.threads.fixedScheduling = true
  ghost : p.before.machine.user.payload.ghost = false
  shallow : p.before.machine.user.payload.validation = .Shallow
  gc : p.before.machine.user.payload.payload.user.host.control.gcInterval = 0
  unchecked : p.before.machine.user.payload.payload.user.host.control.checkedArithmetic = false

  /-- InitialMachine installs `.none` together with absent race clocks; the
  selected race-off profile preserves this source-owned backend choice. -/
  backend : p.before.machine.user.payload.payload.user.backend = .none

structure AllocationMargins (p : Packet) : Prop where
  available : p.before.machine.memory.idSupplyExhausted = false
  nonzero : p.before.machine.memory.nextAllocId ≠ 0
  room : p.before.machine.memory.nextAllocId.toNat + 1 < 2^64
  sourceAvailable : p.before.machine.memory.sourceAllocIdWorldActive = true →
    p.before.machine.memory.sourceAllocIdExhausted = false
  sourceNonzero : p.before.machine.memory.sourceAllocIdWorldActive = true →
    p.before.machine.memory.sourceAllocIdNext ≠ 0
  sourceRoom : p.before.machine.memory.sourceAllocIdWorldActive = true →
    p.before.machine.memory.sourceAllocIdNext.toNat + 1 < 2^64

/-- A count of current finite storage/graph data, proposed for a conservative
execution reserve. Its sufficiency for every latent/projection case is OPEN. -/
def work (s : Static) (p : Packet) : Nat :=
  64 + s.prepared.compiler.program.input.allocations.size +
    (p.before.machine.memory.live.toList.map fun row => row.2.allocation.len +
      row.2.allocation.extra.nodes.size + row.2.allocation.extra.locations.entries.size).sum +
    (p.before.machine.memory.globals.toList.map fun row => row.size.bytes.toNat).sum +
    (s.prepared.image.initializers.toList.map fun row =>
      row.2.len + row.2.provenanceMap.ptrs.size).sum

/-- Numeric headroom is separate from physical/runtime input validity. No
operation outcome or future-state permission is a resource field. Address
generation bounds are initial data, with their converter adequacy still OPEN. -/
structure ResourceMargins (s : Static) (p : Packet)
    (choiceCondition : Prop := ChoiceAdmission.Environment s p) where
  choices : choiceCondition
  budget : Nat
  reserve : work s p ≤ budget
  capacity : budget ≤ s.capacity
  dispatch : budget ≤ s.limits.callDispatch
  retag : budget ≤ s.limits.retag
  validation : budget ≤ s.limits.validation
  configuredValidation : budget ≤ s.options.limits.validation
  configuredRetag : budget ≤ s.options.limits.retag
  dynamic : budget ≤ s.options.place.dynamicFuel
  tagRoom : ∀ tracker, p.before.machine.borrowTracker = some tracker →
    tracker.global.nextPointerTag.value.toNat + budget < 2^64
  nodeRoom : ∀ row ∈ p.before.machine.memory.live,
    row.2.allocation.extra.nodes.size + budget < 2^32
  maximumSize : Nat
  maximumAlignment : Nat
  liveSizes : ∀ row ∈ p.before.machine.memory.live, row.2.allocation.len ≤ maximumSize
  liveByteSizes : ∀ row ∈ p.before.machine.memory.live,
    row.2.allocation.byteSize.bytes.toNat ≤ maximumSize
  liveStorage : ∀ row ∈ p.before.machine.memory.live,
    row.2.allocation.len = row.2.allocation.byteSize.bytes.toNat
  liveAlignments : ∀ row ∈ p.before.machine.memory.live,
    2^row.2.allocation.align.pow2 ≤ maximumAlignment
  globalSizes : ∀ row ∈ p.before.machine.memory.globals, row.size.bytes.toNat ≤ maximumSize
  globalAlignments : ∀ row ∈ p.before.machine.memory.globals,
    2^row.align.pow2 ≤ maximumAlignment
  initializerSizes : ∀ row ∈ s.prepared.image.initializers,
    row.2.byteSize.bytes.toNat ≤ maximumSize
  initializerStorage : ∀ row ∈ s.prepared.image.initializers,
    row.2.len = row.2.byteSize.bytes.toNat
  initializerAlignments : ∀ row ∈ s.prepared.image.initializers,
    2^row.2.align.pow2 ≤ maximumAlignment
  localSizes : ∀ caller id layout,
    p.before.stack.currentFrame? = some caller →
    Nonempty (InputDraft.LocalMetadata s caller id layout) →
    layout.layout.size.bytes.toNat ≤ maximumSize
  localAlignments : ∀ caller id layout,
    p.before.stack.currentFrame? = some caller →
    Nonempty (InputDraft.LocalMetadata s caller id layout) →
    2^layout.layout.align.abi.pow2 ≤ maximumAlignment
  maximumSizeBudget : maximumSize ≤ budget
  maximumAlignmentBudget : maximumAlignment ≤ budget
  allocation : InputDraft.NeedsEnclosingAllocation p → AllocationMargins p
  addresses : ∀ generation, p.before.machine.user.addresses.generation = some generation →
    InputDraft.GenerationResources generation budget maximumSize maximumAlignment

/-- The same numeric reserves with supplied/diagnostic choice adequacy. -/
abbrev PolicyResourceMargins (s : Static) (p : Packet) :=
  ResourceMargins s p (PolicyChoiceAdmission.Environment s p)

/-- Explicit draft-domain instantiation. The name remains a candidate because
descriptor conversion, generator adequacy and preservation of additional host
and cache state have not yet passed the adoption review. -/
def CandidateTarget (s : Static) : Prop :=
  WholeCall.Target s (Nonempty (Metadata s)) (Profile s)
    (fun p => Nonempty (ResourceMargins s p))
    (fun p => RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p))
    (Preservation.Preserves s)

/-- Named implementation holes. These are theorem obligations, explicitly
separate from CurrentInputDraft and ResourceMargins. No instance is supplied. -/
structure ImplementationObligations (s : Static) : Prop where
  initialization : Nonempty (Metadata s) → Profile s → ∀ p,
    Nonempty (ResourceMargins s p) →
    (RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p)) →
    ∃ installed, install s p = .ok () installed ∧ installed.stack.frames.size = depth p
  bodyReturn : Nonempty (Metadata s) → Profile s → ∀ p,
    Nonempty (ResourceMargins s p) →
    (RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p)) →
    ∀ installed, install s p = .ok () installed →
    ∃ after, Executes s (depth p) installed after ∧ Returned p after ∧
      Preservation.Preserves s p after
  allPrefixes : Nonempty (Metadata s) → Profile s → ∀ p,
    Nonempty (ResourceMargins s p) →
    (RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p)) →
    ∀ installed, install s p = .ok () installed →
    ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) (depth p) installed

/-- Conditional assembly only; the three implementation obligations above
are not proved here, and the candidate domain has not been adopted as complete. -/
theorem conditionalCandidate (s : Static) (holes : ImplementationObligations s) :
    CandidateTarget s :=
  WholeCall.conditionalComposition s (Nonempty (Metadata s)) (Profile s)
    (fun p => Nonempty (ResourceMargins s p))
    (fun p => RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p))
    (Preservation.Preserves s) holes.initialization holes.bodyReturn holes.allPrefixes

end EmptyFunction.Specification
