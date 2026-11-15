import Miri.Input.CompilerProviders
import Miri.Input.CompilerVirtualLeaves
import Miri.Input.SourceCompilerAllocationIdentity
import Miri.Input.SourceCompilerVTables
import Miri.Input.SourceCompilerRuntime

/-! Complete symbolic-vtable dictionary without an overwritten baseline.
Only actual memory offsets are supplied by physical consumers. ABI checks
run at call.rs frame initialization, not at vtable identity resolution.
-/
namespace Miri.Input.CompilerVTableLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported e)

private def source (access : SourceCompilerWorld.Access S)
    (query : SourceCompilerWorld.World → Except String A) : EStateM StepError S A := do
  let some world := access.get (← get) | throw (.unsupported "source vtable World unavailable")
  lift (query world)

def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (access : SourceCompilerWorld.Access (MachineHooks.State K U))
    (engine : VTableMachine.Hooks K U Other)
    (memoryOffset : C → MemPlace Provenance → Size → OffsetMode → MemPlaceMeta Provenance →
      MachineHooks.M K U (MemPlace Provenance)) :
    VTableHooks Provenance (MachineHooks.State K U) C CallInstance (FnAbi MIR.TyId) :=
  let facts := p.lifecycle.calls.symbols.facts
  let engine := CompilerVTableMachine.hooks p.vtables image engine
  let sourceMode := p.runtime.source.sourceMaterial.isSome

  { target := p.runtime.target.base
    isDynamic := fun _ ty => if sourceMode then do
      let runtime ← SourceCompilerRuntime.current p.runtime.target access
      return (← lift (runtime.node ty |>.mapError toString)).shapeKind == .dynamicTraitObject
      else lift (CompilerFacts.boolean facts.context ty "is_dynamic")
    memoryOffset := memoryOffset
    resolvePointer := fun _ pointer => do
      match pointer.intoPointerOrAddr with
      | .error _ => pure (.error .danglingInteger)
      | .ok pointer =>
        match ← engine.functions.ptrGetAlloc pointer with
        | none => pure (.error .danglingInteger)
        | some value => pure (.ok value)
    globalVTable := fun _ id => VTableMachine.globalVTable engine id
    globalFunction := fun _ id => do
      let registry := engine.functions.registry (← get).machine.user
      if registry.extras.any (·.1 == id) then
        throw (.unsupported "FullInstance vtable dictionary cannot represent machine extra function")
      FunctionPointers.globalFunction engine.functions id
    predicates := fun _ token => if sourceMode then
      source access (SourceCompilerVTables.comparisonPredicates · token)
      else lift (CompilerVTableFacts.predicates facts token)
    normalizePredicate := fun _ predicate => if sourceMode then
      source access (SourceCompilerVTables.normalizeComparisonPredicate · predicate)
      else lift (CompilerVTableFacts.normalizePredicate facts predicate)
    layoutOf := fun _ ty => if sourceMode then do
      let runtime ← SourceCompilerRuntime.current p.runtime.target access
      lift (runtime.lookup ty |>.mapError toString)
      else lift (CompilerFacts.layoutOf facts.context ty)
    eraseAndAnonymize := fun _ ty token => if sourceMode then
      source access (SourceCompilerVTables.erasedPair · ty token)
      else lift (CompilerVTableQueries.eraseAndAnonymize p.vtables.queries ty token)
    ensureMonomorphicType := fun _ ty => if sourceMode then
      source access (SourceCompilerCasts.ensureMonomorphic · ty)
      else lift (CompilerVTableQueries.ensureMonomorphicType p.vtables.queries ty)
    ensureMonomorphicDyn := fun _ token => if sourceMode then
      source access (SourceCompilerVTables.ensureMonomorphicPredicates · token)
      else lift (CompilerVTableQueries.ensureMonomorphicDyn p.vtables.queries token)
    globalSalt := fun _ => return (← engine.functions.chooseSalt).val
    reserveVTable := fun _ ty token salt => do
      if bound : salt < 32 then
        if sourceMode then
          let state ← get
          let some world := access.get state | throw (.unsupported "source vtable World unavailable")
          let align := p.runtime.target.defaultAddressSpacePointerSpec.pointerAlign
          let result := SourceCompilerAllocationIdentity.demand world state.machine.memory ty token ⟨salt,bound⟩ align
          let state := access.put state result.world
          set {state with machine := {state.machine with memory := result.memory}}
          let id ← lift result.outcome
          let state ← get
          let registry := engine.registry state.machine.user
          if let some old := registry.entries.find? (fun entry => entry.typeId == ty &&
              entry.dynamicType == token && entry.salt.val == salt) then
            unless old.allocation == id do throw (.invalidProgram "source vtable registry identity conflict")
          else
            unless !(registry.entries.any (·.allocation == id)) do
              throw (.invalidProgram "source vtable identity assigned to another key")
            let registry := {registry with entries := registry.entries.push ⟨ty,token,⟨salt,bound⟩,id⟩}
            modify fun state => {state with machine := {state.machine with
              user := engine.putRegistry state.machine.user registry}}
          return id
        else VTableMachine.reserve engine ty token ⟨salt,bound⟩
      else throw (.invalidProgram "vtable source salt outside 0..32")
    globalRootPointer := fun _ id => do
      if sourceMode then
        unless (engine.registry (← get).machine.user).entries.any (·.allocation == id) do
          throw (.unsupported "source vtable allocation root witness unavailable")
      return (← FunctionPointers.rootPointer engine.functions id).withOptionalProvenance
    entries := fun _ principal ty => if sourceMode then
      throw (.unsupported "source vtable method/contents materialization unavailable")
      else lift (CompilerVTableRuntime.entries p.lifecycle.calls.symbols principal ty)
    assertVirtualInstanceMatches := VirtualCalls.assertConcrete (CompilerVirtualLeaves.make p.lifecycle.calls access) }
end Miri.Input.CompilerVTableLeaves
