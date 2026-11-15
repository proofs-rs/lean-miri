import Miri.Input.SourceCompilerWorldAbi
import Miri.Frontend.FoundationSourceMaterial
import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Frontend.FoundationRuntimeInstances
import Miri.Frontend.FoundationEntry
import Miri.Frontend.FoundationPrimitiveCatalog
import Miri.Frontend.FoundationPrimitiveFacts
import Miri.Frontend.FoundationNamedTypes
import Miri.Frontend.FoundationForeignDeclarations
import Miri.Frontend.FoundationForeignSymbols
import Miri.Frontend.FoundationSession
import Miri.Frontend.FoundationProducer
import Miri.Frontend.FoundationStartup
import Miri.Frontend.FoundationSpanRegistry
import Miri.Frontend.FoundationGlobalBytes
import Miri.Frontend.FoundationAllocations
import Miri.Frontend.FoundationLinkSections

/-! Normal compiler-entry seed. Only compiler-selected startup header demands
are materialized here. Source instances have identityOnly capability; no MIR
body, promoted table or executable root is invented. The same evaluation World
retains typed source material for later body/type/constraint demand. -/
namespace Miri.Frontend.Foundation
open Lean

private def helperAbi (physical : PhysicalTypeRegistry) (signature : Input.FunctionAbi) :
    Except String Input.FunctionAbi := do
  let document := physical.registry.document
  let compilation ← document.source.getObjVal? "compilation"
  let strategy ← compilation.getObjValAs? String "panic_strategy"
  unless strategy == "abort" || strategy == "unwind" do throw "invalid source panic strategy"
  let binding (id : Nat) : Except String AbiTypeBinding := do
    let some entry := physical.registry.entries[id]? | throw "entry header physical type absent"
    let (node, _) ← physical.lookup id
    return ⟨entry.type,id,node.layoutId⟩
  let unwind : RustUnwindFacts := {
    hasDefinition := false, neverUnwind := false, panicUnwinds := strategy == "unwind"
    foreignItem := false, panicInDropUnwinds := false, dropGlue := false }
  rustFunctionAbiComponentOfDocument document unwind
    (← signature.arguments.mapM fun argument => binding argument.typeId)
    (← binding signature.returnValue.typeId)

/-- Source-derived headers enter the normal fixed preparation path. All maps
below are partial evidence maps: an unrecorded semantic query must fail, never
become a negative compiler answer. Link sections retain unavailable evidence
unless the complete source traversal proves genuine emptiness. -/
def compilerEntrySeed (document : Document) : Except String Input.SourceCompilerWorld.World := do
  let material ← typedSourceMaterial document
  let selection ← entrySelection document.source
  let some entry := selection.compilerEntry | throw "source compiler entry unavailable"
  let some start := selection.startLangItem | throw "source start language item unavailable"
  let mainHeader ← functionHeaderSource document entry.definition
  let startHeader ← functionHeaderSource document start
  let mainSignature ← mainHeader.getObjVal? "signature"
  unless (← signatureBoundVariables document mainSignature).isEmpty &&
      (← mainSignature.getObjValAs? (Array Nat) "inputs").isEmpty do
    throw "source compiler main has generic/bound/input signature unsupported"
  let safetyName ← mainSignature.getObjValAs? String "safety"
  let mainSafety ← match safetyName with
    | "safe" => pure MIR.Safety.Safe
    | "unsafe" => pure .Unsafe
    | _ => throw "source main safety unavailable"
  let (physical, primitives) ← physicalPrimitiveCatalog (PhysicalTypeRegistry.start document)
  let (physical, namedTypes) ← startupNamedTypes physical
  let (physical, mainAbi) ← rustFunctionAbiOfSourceSignatureInRegistry physical entry.definition #[]
  let some result := physical.registry.entries[mainAbi.returnValue.typeId]?
    | throw "source main result type unavailable"
  let (physical, mainPointer) ← physical.intern (.functionPointer #[] result.type safetyName "rust" false)
  let (physical, startAbi) ← rustFunctionAbiOfSourceSignatureInRegistry physical start #[.type result.type]
  let knownFacts := physical.registry.entries.mapIdx (fun index row => (index,row.type)) |>.filterMap fun (id,ty) =>
    if (primitiveFactsDomain ty).isOk then some id else none
  let physical ← physical.withPrimitiveFactsFor knownFacts
  let helper ← helperAbi physical startAbi
  let some sourceTypes := material.physical | throw "typed source definitions unavailable"
  let definitions := sourceTypes.definitions.map (·.raw)
  let initialSpans : SpanRegistry := ⟨#[],#[],#[],#[]⟩
  let (spans, rootSpan) ← appendSessionRootSpan initialSpans document.source
  let some sourceMemory := material.allocations | throw "typed source memory graph unavailable"
  -- Source images remain typed templates until an allocation constant demand.
  let memory : Array Input.AllocationNode := #[]
  let globalBytes ← if sourceMemory.images.isEmpty then do
    pure (← globalBytesWithoutCandidates physical memory).2
  else do
    let candidates := physical.types.filter (·.shapeKind == .str)
    let [str] := candidates.toList | throw "source str primitive absent/ambiguous"
    pure (Input.Catalog.GlobalBytes.unavailable str.id)
  let sections ← sourceLinkSections document.source
  let mainCatalog : Input.Catalog.Main := {
    startLangItem := some start, compilerEntry := some entry.definition
    compilerEntryType := some ⟨entry.definition,"rustc_main",entry.sigpipe.toNat⟩
    entries := #[], linkSections := if sections.isEmpty then some #[] else none }
  let queries : Input.Catalog.Queries := {
    session := ← sessionOfDocument document rootSpan
    runtime := {
      startup := some (← startupOfDocument document), types := #[], virtualQueries := #[], instances := #[]
      foreignSymbols := { (← foreignSymbols document.source) with
        sourceDeclarations := some (← foreignDeclarations document.source) } }
    frameMetadata := ← frameMetadataOfSource document
    instanceAbis := #[], functionFacts := ⟨#[],#[],#[]⟩
    casts := #[], typeNames := #[], panic := #[], nativeSignatures := #[], retag := #[], covariance := #[]
    globalBytes, callerLocations := #[], main := mainCatalog, primitives, vtables := #[]
    namedTypes := some namedTypes, shimAbis := none, namedShimAbis := none
    libcTypeLayouts := none, windowsTypeLayouts := none, namedConstants := none, namedStatics := none }
  let (producer,producerSettings) ← producerOfDocument document
  let initial : Input.ImportDocument := {
    producer, producerSettings, sourceMaterial := some material
    runtimeTargetDataLayout := some (← evidenceOfTarget document.target)
    compilerAbiLayoutSchema := some "physical_ty_and_layout_v1"
    definitions := definitions, typeConstants := physical.typeConstants, predicates := physical.predicates
    layouts := physical.layouts, types := physical.types, files := spans.files, spans := spans.spans
    allocations := memory, compilerAllocIdWorld := none, instances := #[], selectedScope := none
    functionAbis := #[mainAbi,startAbi,helper], bodyRoots := #[], bodies := #[], queries }
  let world ← Input.SourceCompilerWorld.create initial
  let some mainRaw := definitions[entry.definition]? | throw "source main definition absent"
  let some startRaw := definitions[start]? | throw "source start definition absent"
  let (world,mainId) ← Input.SourceCompilerWorld.internItem material.declarations world ⟨mainRaw,#[]⟩
  let (world,startId) ← Input.SourceCompilerWorld.internItem material.declarations world
    ⟨startRaw,#[.Type mainAbi.returnValue.typeId]⟩
  let (world, mainAbiId) ← Input.SourceCompilerWorld.attachInstanceAbi world mainId #[] mainAbi
  let (world, startAbiId) ← Input.SourceCompilerWorld.attachInstanceAbi world startId #[] startAbi
  let mainNode ← Input.SourceCompilerWorld.node world mainId
  let startNode ← Input.SourceCompilerWorld.node world startId
  let mainRuntime ← runtimeInstanceOfHeader document entry.definition #[] mainHeader mainNode
  let startRuntime ← runtimeInstanceOfHeader document start #[.type result.type] startHeader startNode
  let startSignature ← startHeader.getObjVal? "signature"
  let variables ← signatureBoundVariables document startSignature
  let startSafety ← match ← startSignature.getObjValAs? String "safety" with
    | "safe" => pure MIR.Safety.Safe | "unsafe" => pure .Unsafe | _ => throw "source start safety unavailable"
  let sig : Input.FunctionSignature := ⟨startAbi.arguments.map (·.typeId),startAbi.returnValue.typeId,startSafety,.Rust,false⟩
  let displays ← startAbi.arguments.mapM fun argument => do
    let some row := physical.registry.entries[argument.typeId]? | throw "source start input display unavailable"
    concreteRuntimeDisplay row.type
  let some output := physical.registry.entries[startAbi.returnValue.typeId]? | throw "source start output display unavailable"
  let outputDisplay ← concreteRuntimeDisplay output.type
  let display := (if startSafety == .Unsafe then "unsafe " else "") ++ "fn(" ++
    String.intercalate ", " displays.toList ++ ")" ++ (if outputDisplay == "()" then "" else " -> " ++ outputDisplay) ++
    " {" ++ startRuntime.display ++ "}"
  let functionType := world.canonical.types.size
  let functionLayout := world.canonical.layouts.size
  -- Pinned FnDef LayoutData::unit(cx,true): i8 alignment, not tuple aggregate alignment.
  let target ← runtimeTargetOfTarget document.target
  let alignment ← target.i8Align.bytes.mapError toString
  let functionItemLayout : Input.Layout := {
    maxReprAlignBytes := none
    reprC := false
    uninhabited := false
    largestNiche := none
    randomizationSeed := 0
    kind := .layout
    sizeBytes := some 0
    abiAlignBytes := some alignment.toNat
    unadjustedAbiAlignBytes := some alignment.toNat
    fieldOffsetsBytes := .explicit #[]
    fields := some ⟨.arbitrary, 0, none, none, #[], #[]⟩
    variantsLayout := some ⟨.single, some 0, none, none, none, #[]⟩
    backendRepresentation := some ⟨.memory, some true, none, none, none, none, none, none, none⟩
    variantsKind := some .single
    backendReprKind := some .memory
    variants := none
    backendRepr := none
  }

  let type : Input.TypeNode := {
    id := functionType, layoutId := functionLayout
    shape := .functionDefinition start #[.Type mainAbi.returnValue.typeId] sig variables, display }
  let helperFact : Input.Catalog.HelperSignature := {
    signature := ⟨helper.arguments.map (·.typeId),helper.returnValue.typeId,.Safe,.Rust,false⟩
    splatted := false, abiId := 2 }
  let mainEntry : Input.Catalog.MainEntry := {
    definition := entry.definition, genericParameters := #[]
    signature := ⟨true,false,false,mainAbi.returnValue.typeId,mainPointer,some ⟨startId,functionType⟩⟩ }
  let canonical := { world.canonical with
    types := world.canonical.types.push type
    layouts := world.canonical.layouts.push functionItemLayout
    queries := { queries with
      runtime := { queries.runtime with instances := #[mainRuntime,startRuntime] }
      instanceAbis := #[⟨mainId,#[],mainAbiId⟩,⟨startId,#[],startAbiId⟩]
      functionFacts := ⟨#[⟨functionType,some startId,⟨sig.inputs,sig.output,sig.safety,sig.abi,sig.cVariadic⟩⟩],#[],#[helperFact]⟩
      main := { mainCatalog with entries := #[mainEntry] } } }
  return { world with canonical }

end Miri.Frontend.Foundation
