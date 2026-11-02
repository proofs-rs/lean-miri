import empty_function.OrdinaryReturnNoUB
import empty_function.LocalIndirectReturn

/-! Actual ordinary unit-copy atoms. Capacity and validation facts are supplied
by the successful body branch, not by initial resource admission. -/
namespace EmptyFunction.OrdinaryCopyNoUB
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false

/-- Memory-unit Return copy always succeeds under the ordinary unit metadata.
The physical pointer, heap, tags, address generator, and choice tape are free. -/
theorem memory (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (validation : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (machine : OrdinaryReturnNoUB.Machine) (place : MPlaceTy Provenance)
    (returnPlace : frame.returnPlace = .memory place)
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ frame.returnPlace
      (LocalUnit.current older caller machine) = (LocalUnit.current older caller machine,.ok ()) := by
  rw [returnPlace]
  exact ReturnStep.copy s metadata profile remaining capacity validation
    (LocalUnit.current older caller machine) place layout noMeta aligned noGhost shallow

theorem memory_outcome (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (validation : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (machine : OrdinaryReturnNoUB.Machine) (place : MPlaceTy Provenance)
    (returnPlace : frame.returnPlace = .memory place)
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    OrdinaryReturnNoUB.CopyOutcome s older caller frame machine :=
  Or.inr ⟨caller,machine,memory s metadata profile remaining capacity validation older caller frame machine
    place returnPlace layout noMeta aligned noGhost shallow⟩

/-- A whole indirect local already denotes unit storage; this path allocates
nothing and performs the actual zero write and nested validator unchanged. -/
theorem old_indirect (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (validation : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (machine : OrdinaryReturnNoUB.Machine) (id : LocalId)
    (slot : LocalState Provenance LocalLayout) (place : MemPlace Provenance)
    (atSlot : caller.locals[id]? = some slot) (live : slot.value = .live (.indirect place))
    (cache : slot.layout = some s.abi.ret.layout)
    (noMeta : place.metadata = .none) (aligned : place.misaligned = none)
    (noClocks : caller.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (returnPlace : frame.returnPlace =
      .frameLocal older.size id none s.abi.ret.layout caller.localsIdentity) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ frame.returnPlace
      (LocalUnit.current older caller machine) = (LocalUnit.current older caller machine,.ok ()) := by
  rw [returnPlace]
  exact LocalIndirectReturn.copy s metadata profile remaining capacity validation older caller machine id slot
    place atSlot live cache noMeta aligned noClocks noGhost shallow

theorem old_indirect_outcome (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (validation : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (machine : OrdinaryReturnNoUB.Machine) (id : LocalId)
    (slot : LocalState Provenance LocalLayout) (place : MemPlace Provenance)
    (atSlot : caller.locals[id]? = some slot) (live : slot.value = .live (.indirect place))
    (cache : slot.layout = some s.abi.ret.layout)
    (noMeta : place.metadata = .none) (aligned : place.misaligned = none)
    (noClocks : caller.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (returnPlace : frame.returnPlace =
      .frameLocal older.size id none s.abi.ret.layout caller.localsIdentity) :
    OrdinaryReturnNoUB.CopyOutcome s older caller frame machine :=
  Or.inr ⟨caller,machine,old_indirect s metadata profile remaining capacity validation older caller frame machine
    id slot place atSlot live cache noMeta aligned noClocks noGhost shallow returnPlace⟩

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.OrdinaryCopyNoUB.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary copy axiom {dependency} in {name}"
end EmptyFunction.OrdinaryCopyNoUB
