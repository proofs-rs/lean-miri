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
  body : s.loaded.body = Program.root.loaded.body
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
  itemDefinition : DefId
  itemKind : CompilerInstance.kindOf s.prepared.compiler.loweringContext
    s.prepared.compiler.program.compilerTables s.functionInstance = .ok (.Item itemDefinition)
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
  frameDefinition : ∃ definitionIndex definition,
    CompilerInstance.definitionOf
      (LowerContext.ofDocument s.prepared.compiler.lifecycle.frames.calls.calls.program.input)
      s.prepared.compiler.lifecycle.frames.calls.calls.program.compilerTables s.functionInstance = .ok definitionIndex ∧
    s.prepared.compiler.lifecycle.frames.calls.calls.program.compilerTables.definitions[definitionIndex]? = some definition
  /-- Resolved local types depend on the current frame's body/instance key;
  local values, memory, thread state and caches are unconstrained by this fact. -/
  normalizedLocal : ∀ frame : CompilerFrameContext.ActualFrame,
    frame.bodyIdentity = s.loaded.identity → frame.body = s.loaded.body →
    frame.functionInstance = s.functionInstance →
    CompilerFrameContext.localType s.prepared.compiler frame 0 = .ok s.abi.ret.layout.ty
  loweredBody : LoweredBody
  bodyRow : s.prepared.compiler.program.bundle.bodies[s.loaded.identity.index]? = some loweredBody
  bodyContents : loweredBody.body = s.loaded.body
  lifecycleBody : s.prepared.compiler.lifecycle.lifecycle.program.bundle.bodies[s.loaded.identity.index]? =
    some loweredBody
  preamble : SpanRef
  lifecycleRow : s.prepared.compiler.lifecycle.lifecycle.entries[s.loaded.identity.index]? =
    some ⟨.ok preamble, .ok s.functionInstance⟩
  localSpan : SpanRef
  localSourceSpan : ∃ decl, loweredBody.input.localSources[0]? = some decl ∧
    decl.spanId = localSpan.id
  /-- The literal is tied to the fixed instruction, not chosen to supply an
  operational result. -/
  literal : ConstOperand
  literalShape : literal.value = .Val .ZeroSized s.abi.ret.layout.ty
  literalStatement : ((s.loaded.body.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
    (fun statement => statement.kind) = some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes))
  /-- The default address-space pointer width agrees with the selected x86_64 target. -/
  pointerSize : s.prepared.compiler.runtime.target.pointerSize = Size.ofBytes 8

  /-- Rust type layouts use the pinned rustc_abi::Align representation (normal
  powers of two through exponent 29), unlike offset-analysis sentinel aligns.
  This is compiler data consistency, not a heap-allocation success condition. -/
  compilerLayoutAlignment : ∀ ty layout,
    s.prepared.compiler.runtime.lookup ty = .ok layout →
    InputDraft.AlignmentRepresentation layout.layout.align.abi

  /-- The paired local declaration representation previously made this equality
  structural. The typed MIR and source metadata arrays now record it explicitly;
  it is a compiler-data alignment fact, not an execution-success premise. -/
  compilerLocalSourceAlignment : ∀ body ∈ s.prepared.compiler.program.bundle.bodies,
    body.input.localSources.size = body.input.mir.locals.size

  /-- Canonical compiler span collection covers declarations in every imported
  body, including arbitrary callers whose locals are later materialized. -/
  compilerLocalSourceSpans : ∀ body ∈ s.prepared.compiler.program.bundle.bodies,
    ∀ decl ∈ body.input.localSources,
      decl.spanId < s.prepared.compiler.program.bundle.spans.size

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
