import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceAbi
import Miri.Input.DecoderValues
open Lean Miri Miri.Input Miri.Frontend.Foundation

def main (args : List String) : IO Unit := do
  let path :: oraclePaths := args | throw (IO.userError "expected genuine catch MIR-use source")
  unless oraclePaths.length ≤ 1 do throw (IO.userError "expected at most one independent ABI oracle")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let world ← IO.ofExcept (compilerEntrySeed document)
  let some source := world.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some physical := source.physical | throw (IO.userError "physical source absent")
  let some abiSource := source.abi | throw (IO.userError "ABI source absent")
  let callerDisabled := abiSource.optimizationDisabled || abiSource.callerIncremental == some true
  let some uses := source.mirUses | throw (IO.userError "MIR uses absent")
  let [function] := (source.declarations.filter (·.path == "std::panic::catch_unwind")).toList
    | throw (IO.userError "genuine function declaration absent")
  let [use] := (uses.declarations.filter (·.definition == function.definition)).toList
    | throw (IO.userError "genuine MIR-use declaration absent")
  let some body := use.body | throw (IO.userError "genuine optimized body absent")
  let ret ← IO.ofExcept (SourceParamAttrs.parameterUsage body 0)
  let arg ← IO.ofExcept (SourceParamAttrs.parameterUsage body 1)
  unless ret == ⟨false,false,true,true⟩ && arg == ⟨false,false,false,false⟩ do
    throw (IO.userError "actual catch MIR return/argument use differs from pinned visitor")
  -- Dereference-first uses affect the pointee, not indirect parameter storage.
  let indirect := {body with events := body.events.map fun event =>
    {event with kind := match event.kind with
      | .place place context => .place {place with firstProjection := some .deref} context
      | .callMove place => .callMove {place with firstProjection := some .deref}
      | .tailCall => .tailCall}}
  unless (← IO.ofExcept (SourceParamAttrs.parameterUsage indirect 0)) == ⟨false,false,true,false⟩ do
    throw (IO.userError "dereference-first use changed root parameter storage")
  let tail := {body with events := #[⟨0,0,.tailCall⟩]}
  unless (← IO.ofExcept (SourceParamAttrs.parameterUsage tail 1)) == ⟨false,false,true,true⟩ do
    throw (IO.userError "tail-call visitor did not conservatively mark argument")
  let root : SourceMirUses.Place := ⟨1,none⟩
  for (context,projection,expected) in [
      (SourceMirUses.Context.mutating .drop,none,SourceParamAttrs.Usage.mk true false false false),
      (.mutating .drop,some .other,⟨false,false,true,true⟩),
      (.nonMutating .sharedBorrow,none,⟨false,true,false,true⟩),
      (.nonMutating .rawBorrow,none,⟨false,false,true,true⟩),
      (.mutating .store,none,⟨false,false,true,false⟩)] do
    let control := {body with events := #[⟨0,0,.place {root with firstProjection := projection} context⟩]}
    unless (← IO.ofExcept (SourceParamAttrs.parameterUsage control 1)) == expected do
      throw (IO.userError "pinned place-context visitor distinction failed")
  match SourceParamAttrs.parameterUsage {body with phase := .known (.Runtime .PostCleanup)} 0 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "nonoptimized source accepted for deduction")
  let [closure] := (physical.types.zipIdx |>.filterMap fun (type,index) => match type with
    | .closure closure => if physical.definitions[closure.definition]?.map (·.path) == some
        "std::rt::lang_start_internal::{closure#0}" then some index else none
    | _ => none).toList | throw (IO.userError "actual internal closure absent")
  let concrete ← IO.ofExcept (SourceTypes.instantiate physical #[] #[] closure)
  let (world,closure) ← IO.ofExcept (SourcePhysical.intern world concrete)
  let (world,isize) ← IO.ofExcept (SourcePhysical.intern world (.primitive "int" "isize"))
  let (world,callee) ← IO.ofExcept (SourceCompilerWorld.internItem source.declarations world
    ⟨function.definition,#[.Type closure,.Type isize]⟩)
  match SourceAbi.derive world callee #[] with
  | .error message =>
    if callerDisabled then throw (IO.userError s!"caller no-deduction gate failed: {message}")
    unless message.startsWith "typed ABI indirect parameter 1 requires defining" ||
        message == "typed ABI indirect parameter 1 requires caller incremental source" do
      throw (IO.userError s!"return no-adjustment witness failed: {message}")
  | .ok (derived,abi) =>
    let some mir := source.genericMir | throw (IO.userError "selected MIR source absent")
    let [body] := (mir.bodies.filter (fun body => body.definition == function.definition && body.promoted.isNone)).toList
      | throw (IO.userError "selected catch body absent/ambiguous")
    let some returnLocal := body.locals[0]? | throw (IO.userError "selected return local absent")
    let returnType ← IO.ofExcept (SourceTypes.instantiate physical
      #[some concrete,some (.primitive "int" "isize")] #[] returnLocal.type >>= SourceTypes.eraseRegions)
    let (_,returnType) ← IO.ofExcept (SourcePhysical.intern derived returnType)
    unless abi.returnValue.typeId == returnType do
      throw (IO.userError "normalized ABI return and erased MIR local identities differ")
    let disabled := callerDisabled || use.compilation.any (fun c => c.optimization == .no || c.incremental ||
      c.freezeLangItemPresent == some false) || use.alwaysConst == some true
    unless disabled do
      throw (IO.userError "unproven external enabled deduction accepted")
    let expected : AbiPassMode := ⟨.indirect,#[⟨670,16,some 8,.none⟩],none,none,none,some .pointer⟩
    let expectedArg : AbiPassMode := ⟨.indirect,#[⟨670,40,some 8,.none⟩],none,none,none,some .pointer⟩
    unless abi.returnValue.mode == expected && abi.arguments.map (·.mode) == #[expectedArg] do
      throw (IO.userError "actual enabled/disabled indirect modes differ")
    let [oraclePath] := oraclePaths | throw (IO.userError "successful ABI requires independent same-compiler oracle")
    let oracle ← IO.ofExcept (Json.parse (← IO.FS.readFile oraclePath))
    let definitions ← IO.ofExcept (oracle.getObjValAs? (Array Json) "definitions")
    let instances ← IO.ofExcept (oracle.getObjValAs? (Array Json) "instances")
    let queries ← IO.ofExcept (oracle.getObjValAs? (Array Json) "compiler_instance_abis")
    let oracleTypes ← IO.ofExcept (oracle.getObjValAs? (Array Json) "types")
    let abis ← IO.ofExcept (oracle.getObjValAs? (Array Json) "fn_abis")
    let arguments ← IO.ofExcept (oracle.getObjValAs? (Array Json) "abi_arguments")
    let raw := fun (ref : Nat) => do
      let row ← definitions[ref]?
      let crate ← (row.getObjValAs? Nat "crate").toOption
      let index ← (row.getObjValAs? Nat "index").toOption
      pure (DefinitionId.mk crate index)
    let .closure closureDefinition _ := concrete | throw (IO.userError "actual closure identity absent")
    let some closureDefinition := physical.definitions[closureDefinition]?
      | throw (IO.userError "closure raw source identity absent")
    let matching := instances.filter fun row => (show Option Unit from do
      let definition ← (row.getObjValAs? Nat "def_id").toOption
      unless raw definition == some function.definition do none
      let arguments ← (row.getObjValAs? (Array Json) "generic_args").toOption
      let argument : Json ← arguments[0]?
      unless (argument.getObjValAs? String "kind").toOption == some "type" do none
      let argument ← (argument.getObjValAs? Nat "value").toOption
      let argument ← oracleTypes[argument]?
      let shape ← (argument.getObjVal? "shape").toOption
      unless (shape.getObjValAs? String "kind").toOption == some "closure" do none
      let definition ← (shape.getObjValAs? Nat "def_id").toOption
      unless raw definition == some closureDefinition.raw do none
      pure ()) |>.isSome
    let [node] := matching.toList | throw (IO.userError "independent oracle exact function/closure identity absent/ambiguous")
    let id ← IO.ofExcept (node.getObjValAs? Nat "instance_id")
    let [query] := (queries.filter fun row => (row.getObjValAs? Nat "instance_id").toOption == some id &&
        (row.getObjValAs? (Array Nat) "extra_argument_types").toOption == some #[]).toList
      | throw (IO.userError "independent exact ABI key absent/ambiguous")
    let index ← IO.ofExcept (query.getObjValAs? Nat "abi_query")
    let some oracleAbi := abis[index]? | throw (IO.userError "independent ABI absent")
    let parseMode := fun value => IO.ofExcept (JsonReader.run (DecoderValues.parseAbiPassMode "$.mode") value.compress)
    let result ← IO.ofExcept (oracleAbi.getObjValAs? Nat "return")
    let some result := arguments[result]? | throw (IO.userError "independent ABI return absent")
    unless abi.returnValue.mode == (← parseMode (← IO.ofExcept (result.getObjVal? "mode"))) do
      throw (IO.userError "independent compiler return attributes differ")
    let ids ← IO.ofExcept (oracleAbi.getObjValAs? (Array Nat) "arguments")
    unless ids.size == abi.arguments.size do throw (IO.userError "independent ABI argument count differs")
    for (id,argument) in ids.zip abi.arguments do
      let some row := arguments[id]? | throw (IO.userError "independent ABI argument absent")
      unless argument.mode == (← parseMode (← IO.ofExcept (row.getObjVal? "mode"))) do
        throw (IO.userError "independent compiler parameter attributes differ")
    unless abi.fixedCount == (← IO.ofExcept (oracleAbi.getObjValAs? Nat "fixed_count")) &&
        abi.canUnwind == (← IO.ofExcept (oracleAbi.getObjValAs? Bool "can_unwind")) &&
        abi.cVariadic == (← IO.ofExcept (oracleAbi.getObjValAs? Bool "c_variadic")) do
      throw (IO.userError "independent compiler ABI header differs")
  let absentSource := {source with mirUses := none}
  let absent := {world with canonical := {world.canonical with sourceMaterial := some absentSource}}
  match SourceAbi.derive absent callee #[] with
  | .error message =>
    unless !callerDisabled && message.startsWith "typed ABI indirect parameter 0 requires defining-crate MIR deduction evidence" do
      throw (IO.userError "missing material did not reject at return evidence demand")
  | .ok _ => unless callerDisabled do throw (IO.userError "missing MIR-use capability accepted")
  let absentDeclaration := {source with mirUses := some {uses with declarations := uses.declarations.filter (·.definition != function.definition)}}
  let absent := {world with canonical := {world.canonical with sourceMaterial := some absentDeclaration}}
  match SourceAbi.derive absent callee #[] with
  | .error "typed ABI indirect MIR-use declaration absent/ambiguous" => unless !callerDisabled do throw (IO.userError "caller gate demanded MIR")
  | .ok _ => unless callerDisabled do throw (IO.userError "omitted MIR-use declaration confused with observed no-MIR")
  | _ => throw (IO.userError "omitted MIR-use declaration confused with observed no-MIR")
  let noExternalBody := {uses with declarations := uses.declarations.map fun row =>
    if row.definition == function.definition then {row with body := none,compilation := none} else row}
  let noExternalBody := {source with mirUses := some noExternalBody}
  let noExternalBody := {world with canonical := {world.canonical with sourceMaterial := some noExternalBody}}
  match SourceAbi.derive noExternalBody callee #[] with
  | .error "typed ABI indirect parameter 0 requires defining MIR availability evidence" => unless !callerDisabled do throw (IO.userError "caller gate demanded MIR")
  | .ok _ => unless callerDisabled do throw (IO.userError "unencoded external MIR confused with defining no-MIR")
  | _ => throw (IO.userError "unencoded external MIR confused with defining no-MIR")
  IO.println "actual optimized MIR-use visitor and gate-independent return witness passed"
