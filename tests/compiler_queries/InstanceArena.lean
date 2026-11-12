import MiriTests.Input.InstanceArenaSupport

/-! Identity/persistence controls for the independent instance prototype. They
make no executable-body, ABI-lowering, trait-selection or guest-safety claim. -/
open Miri.Input Miri.Input.GenericSubstitution Miri.Interpreter
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def source (id : Nat) : InstanceNode := {
  id,kind := .identityOnly,instanceKind := .Item 0,genericArgs := #[.Type 0],
  defPath := none,definitionId := some 0,bodyId := none,promotedBodies := #[] }
private def rawSource (definition : Nat) : CopyTemplateSource := {
  template := {parameters := #[],types := #[],skeleton := {
    phase := .Built,argumentCount := 0,spreadArgument := none,locals := #[],blocks := #[]}},
  sourceRole := .runtime,sourcePromoted := none,definitionId := definition,defPath := "identical display",spanId := 0,preambleDefSpanId := 0,
  injectionPhase := none,localSources := #[],sourceScopes := #[],backtraceSpans := #[] }

def main : IO Unit := do
  let types ← must (TypeArena.World.ofMaterial #[
    {id := 0,display := "same",layoutId := 0,shape := .uint (.known .u32)},
    {id := 1,display := "same",layoutId := 0,shape := .uint (.known .u8)}] #[]
    #[{crateIndex := 0,index := 11},{crateIndex := 0,index := 12}] 8)
  let initialStore ← must (InstanceArena.Store.ofSource types #[source 0])
  let initial : InstanceArena.World := ⟨types,initialStore⟩
  let (material,world) ← must ((InstanceArena.World.internInstance (.Item 0) #[.Type 0]).run initial)
  unless material == 0 && world.instances.constructed.isEmpty do
    throw (IO.userError "material instance identity was not reused exactly")
  let (item,world) ← must ((InstanceArena.World.internInstance (.Item 0) #[.Type 1]).run world)
  let (intrinsic,world) ← must ((InstanceArena.World.internInstance (.Intrinsic 0) #[.Type 1]).run world)
  let (shim,world) ← must ((InstanceArena.World.internInstance (.Shim (.ClosureOnce 0 1 false)) #[.Type 1]).run world)
  let (tracked,world) ← must ((InstanceArena.World.internInstance (.Shim (.ClosureOnce 0 1 true)) #[.Type 1]).run world)
  unless #[item,intrinsic,shim,tracked] == #[1,2,3,4] do
    throw (IO.userError "kind, complete arguments or shim payload was collapsed")
  let (tuple,world) ← must ((InstanceArena.World.typeAction
    (TypeArena.World.internType (.tuple #[0,1]))).run world)
  let (novel,world) ← must ((InstanceArena.World.internInstance (.Item 0) #[.Type tuple]).run world)
  let (again,retained) ← must ((InstanceArena.World.internInstance (.Item 0) #[.Type tuple]).run world)
  unless novel == 5 && again == novel && retained.instances.constructed.size == 5 &&
      retained.types.constructedTypes.size == 1 do
    throw (IO.userError "one compiler world did not retain type/instance interning together")
  let .constructed key ← must (retained.instances.lookup novel)
    | throw (IO.userError "constructed instance lookup lost its namespace")
  unless key.definition == (⟨0,11⟩ : DefinitionIdentity) && key.arguments == #[.Type tuple] do
    throw (IO.userError "physical definition or complete arguments changed")
  if (initial.instances.lookup novel).isOk then throw (IO.userError "initial execution leaked future instance IDs")
  let independent := InstanceArena.World.mk types initialStore
  unless independent.instances.constructed.isEmpty && independent.types.constructedTypes.isEmpty do
    throw (IO.userError "independent execution shared constructor pools")
  if ((InstanceArena.World.internInstance (.Item 0) #[.Type retained.types.typeCount]).run retained).isOk then
    throw (IO.userError "instance accepted an absent type argument")
  if ((InstanceArena.World.internInstance (.Item 0) #[.Const 0]).run retained).isOk then
    throw (IO.userError "instance accepted an absent constant argument")
  if ((InstanceArena.World.internInstance (.Shim (.Clone 0 retained.types.typeCount)) #[]).run retained).isOk then
    throw (IO.userError "instance accepted an absent shim payload type")
  if ((InstanceArena.World.internInstance (.Shim (.ClosureOnce 0 2 false)) #[]).run retained).isOk then
    throw (IO.userError "instance accepted an absent auxiliary shim definition")
  if ((InstanceArena.World.internInstance (.Item 0) #[.Lifetime .Error]).run retained).isOk then
    throw (IO.userError "instance accepted an error-region argument")
  let forged := {key with definition := ⟨0,12⟩}
  if (retained.instances.intern retained.types forged).isOk then
    throw (IO.userError "kind/physical-definition contradiction was accepted")
  let duplicate ← must (InstanceArena.Store.ofSource types #[source 0,source 1])
  let known ← must (InstanceArena.Key.item types ⟨0,11⟩ #[.Type 0])
  match duplicate.intern types known with
  | .error "ambiguous canonical material instance identity" => pure ()
  | _ => throw (IO.userError "duplicate material instance candidates were accepted")
  if (InstanceArena.Store.ofSource types #[source 7]).isOk then
    throw (IO.userError "non-dense material instance table was accepted")
  if (InstanceArena.ordinaryBodySource retained.types #[] key).isOk then
    throw (IO.userError "identity interning fabricated an executable body capability")
  let ordinary : InstanceArena.RawBodySource := ⟨⟨0,11⟩,rawSource 0⟩
  let promoted : InstanceArena.RawBodySource := ⟨⟨0,11⟩,{rawSource 0 with sourcePromoted := some 0}⟩
  let selected ← must (InstanceArena.ordinaryBodySource retained.types #[promoted,ordinary] key)
  unless selected.definitionId == 0 do throw (IO.userError "explicit ordinary source role was lost")
  if (InstanceArena.ordinaryBodySource retained.types #[promoted] key).isOk then
    throw (IO.userError "promoted source was silently used as an ordinary body")
  if (InstanceArena.ordinaryBodySource retained.types #[ordinary,ordinary] key).isOk then
    throw (IO.userError "duplicate ordinary raw sources were accepted")
  if (InstanceArena.ordinaryBodySource retained.types
      #[{ordinary with source := rawSource 1}] key).isOk then
    throw (IO.userError "raw source physical identity contradiction was accepted")
  if (InstanceArena.ordinaryBodySource retained.types #[ordinary] forged).isOk then
    throw (IO.userError "forged body request key was accepted")
  -- The combined StateT uses transactional Except: this failed operation
  -- cannot publish either its newly interned type or instance ID.
  let failed : InstanceArena.WorldM Unit := do
    let child ← InstanceArena.World.typeAction (TypeArena.World.internType (.slice tuple))
    let _ ← InstanceArena.World.internInstance (.Item 0) #[.Type child]
    throw "capability unavailable"
  unless (failed.run retained).toOption.isNone && retained.instances.constructed.size == 5 do
    throw (IO.userError "failed capability transaction leaked instance state")
  let (constant,argumentsWorld) ← must ((InstanceArena.World.typeAction
    (TypeArena.World.internConstant (.Value 0 ⟨#[.Leaf 7 4],0⟩))).run retained)
  let (withConst,argumentsWorld) ← must ((InstanceArena.World.internInstance (.Item 0)
    #[.Type tuple,.Const constant,.Lifetime .Static]).run argumentsWorld)
  let (withRegion,argumentsWorld) ← must ((InstanceArena.World.internInstance (.Item 0)
    #[.Type tuple,.Const constant,.Lifetime .Erased]).run argumentsWorld)
  let (reordered,_) ← must ((InstanceArena.World.internInstance (.Item 0)
    #[.Const constant,.Type tuple,.Lifetime .Static]).run argumentsWorld)
  unless withConst != withRegion && withConst != reordered && withRegion != reordered do
    throw (IO.userError "complete constant/lifetime arguments or argument order was collapsed")
  IO.println "PASS instance prototype exact keys/material reuse/dense IDs, shared type state, ambiguity and execution isolation"
