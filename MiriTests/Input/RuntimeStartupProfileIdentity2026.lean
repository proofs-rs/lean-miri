import Miri.Input.EvalBootstrap
import Miri.Input.CompilerGlobalBytes
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerVTableMachine
import Miri.Input.CompilerIntrinsicSymbols

open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter

theorem bootstrapReadyProfileIdentity (profile : Lean.Options) (state : α) :
    Lean.profileit "startup.bootstrap_ready" profile (fun _ => state) = state := by
  rfl

/-! Profiling may record startup stages, but every profile option set yields
the same value or state transition as the unprofiled implementation. -/

theorem functionSeedProfileIdentity (profile : Lean.Options)
    (p : CompilerFunctionPointers.Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : FunctionPointers.Registry Other) :
    CompilerFunctionPointers.seedImportedProfiled profile p image memory initial =
      CompilerFunctionPointers.seedImported p image memory initial := by
  rfl

theorem functionAttachProfileIdentity (profile : Lean.Options)
    (p : CompilerFunctionPointers.Prepared) (image : AllocationImage.Imported)
    (hooks : FunctionPointers.Hooks K User Other) :
    CompilerFunctionPointers.attachProfiled profile p image hooks =
      CompilerFunctionPointers.attach p image hooks := by
  rfl

theorem vtableSeedProfileIdentity (profile : Lean.Options)
    (p : CompilerVTableMachine.Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : VTableMachine.Registry) :
    CompilerVTableMachine.seedImportedProfiled profile p image memory initial =
      CompilerVTableMachine.seedImported p image memory initial := by
  rfl

theorem vtableAttachProfileIdentity (profile : Lean.Options)
    (p : CompilerVTableMachine.Prepared) (image : AllocationImage.Imported)
    (hooks : VTableMachine.Hooks K User Other) :
    CompilerVTableMachine.attachProfiled profile p image hooks =
      CompilerVTableMachine.attach p image hooks := by
  rfl

theorem globalBytesAttachProfileIdentity (K U : Type) (profile : Lean.Options)
    (program : LoweredProgram) (runtime : RuntimeMetadata)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw)) :
    CompilerGlobalBytes.attachProfiled (K := K) (U := U) profile program runtime sourceEquality =
      CompilerGlobalBytes.attach (K := K) (U := U) program runtime sourceEquality := by
  rfl

theorem typeIdAttachProfileIdentity (K : Type) (profile : Lean.Options)
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (registry : IntrinsicSymbolsMachine.Access U) :
    CompilerIntrinsicSymbols.attachProfiled (K := K) profile p image registry =
      CompilerIntrinsicSymbols.attach (K := K) p image registry := by
  rfl

theorem bootstrapProfileIdentity [DecidableEq Os] (profile : Lean.Options)
    (hooks : EvalBootstrap.Hooks U C O X F A Aff P AP Os)
    (config : EvalBootstrap.Configuration Os) (choice : C) :
    EvalBootstrap.createContextWithBytesProfiled profile hooks config choice =
      EvalBootstrap.createContextWithBytes hooks config choice := by
  rfl

#print axioms bootstrapReadyProfileIdentity
#print axioms functionSeedProfileIdentity
#print axioms functionAttachProfileIdentity
#print axioms vtableSeedProfileIdentity
#print axioms vtableAttachProfileIdentity
#print axioms globalBytesAttachProfileIdentity
#print axioms typeIdAttachProfileIdentity
#print axioms bootstrapProfileIdentity
