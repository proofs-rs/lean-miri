import Miri.Input.CompilerSourceVTableMaterializer
import Miri.Interpreter.VTableMachine

/-! Explicit interpreter binding for the bounded source vtable factory. The
caller must provide actual User fields. This module does not silently install a
native Allocation-to-live-memory converter or a compiler query cache profile. -/
namespace Miri.Input.CompilerSourceVTableMachine
open Miri.Memory Miri.Interpreter
open CompilerInitialAllocation CompilerSourceVTableMaterializer

structure Hooks (K User : Type) where
  getStore : User → Store
  putStore : User → Store → User
  getCompiler : User → RuntimeArrayTypes.World
  putCompiler : User → RuntimeArrayTypes.World → User
  getMemo : User → Memo
  putMemo : User → Memo → User

private def binding (h : Hooks K User) :
    Binding (MachineHooks.State K User) Provenance Miri.TreeBorrows.BorrowTree K where
  getMemory := fun state => state.machine.memory
  getStore := fun state => h.getStore state.machine.user
  getCompiler := fun state => h.getCompiler state.machine.user
  getMemo := fun state => h.getMemo state.machine.user
  commit := fun state memory store compiler memo =>
    let user := h.putMemo (h.putCompiler (h.putStore state.machine.user store) compiler) memo
    {state with machine := {state.machine with memory := memory, user := user}}

private def liftAction (h : Hooks K User)
    (action : CtfeQueryBridge.Action
      (CompilerSourceVTableMaterializer.State Provenance Miri.TreeBorrows.BorrowTree K) String A) :
    MachineHooks.M K User A := fun state =>
  let (result,next) := CompilerSourceVTableMaterializer.asAction (binding h) action state
  match result with
  | .ok value => .ok value next
  | .error (.unsupported reason) => .error (.unsupported reason) next
  | .error (.internal reason) => .error (.invalidProgram reason) next
  | .error (.reported reason _) => .error (.callback reason) next
  | .error (.tooGeneric _) => .error (.unsupported "source vtable input too generic") next

/-- Establish query-memo ownership while the actual source counter is empty.
Call this before the first symbolic reservation; nonempty unknown prefixes fail. -/
def initializeMemo (h : Hooks K User) (run : Nat) : MachineHooks.M K User Unit :=
  liftAction h fun state =>
    let (result,next) := CompilerSourceVTableMaterializer.initializeFreshMemo run state
    (result.mapError CtfeQueryBridge.Failure.unsupported,next)

/-- The query result is compiler-owned CTFE memory. Its AllocId is distinct
from a symbolic runtime vtable pointer; dereferencing symbolic metadata remains
forbidden. Runtime native conversion is an independent required capability. -/
def allocation (h : Hooks K User) (run work fuel : Nat) (noTraitVptr : Bool)
    (concrete : TypeId) (principal : Option TraitSelection.TraitRef) : MachineHooks.M K User AllocId :=
  liftAction h (CompilerSourceVTableMaterializer.query run work fuel noTraitVptr concrete principal)

/-- Source runtime reservation uses raw predicate IDs to retrieve complete
physical source predicates, not normalized display keys or vtable rows. -/
def reserve (h : Hooks K User) (machine : VTableMachine.Hooks K User Other)
    (concrete : Miri.MIR.TyId) (dynamic : PredicateList) (salt : Fin 32) : MachineHooks.M K User AllocId := do
  let state ← get
  let some run := state.machine.memory.activeInitialCompilerRun
    | throw (.unsupported "source vtable hook requires active initial compiler run")
  let compiler := h.getCompiler state.machine.user
  let rawPredicates : Except String (Array Miri.Input.VtablePredicate) := dynamic.mapM (fun id => do
      let some predicate := compiler.metadata.source.predicates[id]?
        | throw "source vtable raw predicate ID absent"
      pure {predicate with definitionPath := none})
  let predicates ← match rawPredicates with
    | .ok predicates => pure predicates
    | .error reason => throw (.unsupported reason)
  let id ← liftAction h (CompilerSourceVTableMaterializer.reserveSymbolic run concrete predicates salt.val.toUInt64)
  let state ← get
  let registry := machine.registry state.machine.user
  if let some old := registry.entries.find? (fun entry => entry.typeId == concrete &&
      entry.dynamicType == dynamic && entry.salt == salt) then
    unless old.allocation == id do throw (.invalidProgram "source vtable runtime registry identity conflict")
  else
    unless !(registry.entries.any (·.allocation == id)) do
      throw (.unsupported "source vtable raw predicate registry alias requires canonical key adapter")
    let user := machine.putRegistry state.machine.user
      {registry with entries := registry.entries.push ⟨concrete,dynamic,salt,id⟩}
    set {state with machine := {state.machine with user := user}}
  return id

/-- Actual reserveVTable runtime callback override; all pointer/tag operations
continue through the real VTableMachine hooks. The caller explicitly selects
this wrapper. No source failure falls back to the old registry/query catalog. -/
def hooks (h : Hooks K User) (machine : VTableMachine.Hooks K User Other)
    (base : VTableHooks Provenance (MachineHooks.State K User) C CallInstance ABI) :
    VTableHooks Provenance (MachineHooks.State K User) C CallInstance ABI :=
  let original := VTableMachine.hooks machine base
  {original with reserveVTable := fun context concrete dynamic salt => do
    if (← get).machine.memory.activeInitialCompilerRun.isSome then
      if bound : salt < 32 then reserve h machine concrete dynamic ⟨salt,bound⟩
      else throw (.invalidProgram "source vtable runtime salt outside0..32")
    else original.reserveVTable context concrete dynamic salt}
end Miri.Input.CompilerSourceVTableMachine
