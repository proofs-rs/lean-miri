import Miri.Interpreter.PointerMachine
import Lean

/-! One actual integer-to-pointer cast, then ordinary copies of its result.
Pinned alloc_addresses/mod.rs:361-390 deliberately does not resolve an
allocation during this cast. Exposure/origin availability are separate facts. -/
namespace DuplicatePrefix.S05ZeroCellWildcardCast
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false

open Lean Elab Tactic in
elab "unfold_cast_addresses" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".PointerMachine.addresses" then some (mkIdent name) else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected the source PointerMachine.addresses helper"

/-- The source permissive cast returns wildcard provenance without changing
state. No allocation-resolution or cast-success premise is supplied. -/
theorem pointer_from_address {K U : Type} (h : PointerMachine.Hooks K U)
    (state : PointerMachine.State K U) (address : UInt64)
    (mode : state.machine.user.addresses.provenanceMode = .permissive) :
    PointerMachine.pointerFromExposedAddress h address state =
      .ok (Pointer.new (some .wildcard) (Size.ofBytes address)) state := by
  unfold PointerMachine.pointerFromExposedAddress
  unfold_cast_addresses
  simp [mode,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]

/-- Preserve the exact pointer returned by the source cast, merely eliminating
its optional-provenance representation. The impossible none branch is an
interpreter error, never a successful replacement operation. -/
def cast {K U : Type} (h : PointerMachine.Hooks K U) (address : UInt64) :
    PointerMachine.M K U (Pointer Provenance) := do
  let pointer ← PointerMachine.pointerFromExposedAddress h address
  let some provenance := pointer.provenance
    | throw (.invalidProgram "integer cast returned no provenance")
  return ⟨pointer.offset,provenance⟩

theorem cast_from_fields {K U : Type} (h : PointerMachine.Hooks K U)
    (state : PointerMachine.State K U) (address : UInt64)
    (mode : state.machine.user.addresses.provenanceMode = .permissive) :
    cast h address state = .ok (Pointer.new .wildcard (Size.ofBytes address)) state := by
  unfold cast
  simp only [bind,EStateM.bind,pointer_from_address h state address mode]
  rfl

/-- Both consumers receive the SAME once-created pointer value. The statement
is value identity; it does not assert positive-length dereference authority. -/
def copies {K U : Type} (h : PointerMachine.Hooks K U) (address : UInt64) :
    PointerMachine.M K U (Pointer Provenance × Pointer Provenance) := do
  let pointer ← cast h address
  return (pointer,pointer)

theorem one_cast_two_copies {K U : Type} (h : PointerMachine.Hooks K U)
    (state : PointerMachine.State K U) (address : UInt64)
    (mode : state.machine.user.addresses.provenanceMode = .permissive) :
    copies h address state =
      .ok (Pointer.new .wildcard (Size.ofBytes address),Pointer.new .wildcard (Size.ofBytes address)) state := by
  unfold copies
  simp only [bind,EStateM.bind,cast_from_fields h state address mode]
  rfl

end DuplicatePrefix.S05ZeroCellWildcardCast

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellWildcardCast." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved wildcard-cast dependency {dependency}"
