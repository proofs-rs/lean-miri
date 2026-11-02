import empty_function.ProjectedIndirectValidation
import empty_function.ProjectedInbounds
import empty_function.ProjectionWrapping
namespace EmptyFunction.ProjectedValidate
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem concrete (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (localId : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (base : LocalLayout)
    (place : MemPlace Provenance) (id : AllocId) (tag : BorTag) (amount : Size)
    (atSlot : frame.locals[localId]? = some slot) (live : slot.value = .live (.indirect place))
    (cache : slot.layout = some base) (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (concrete : place.ptr.provenance = some (.concrete id tag))
    (footprint : IndirectFootprint (LocalUnit.current frames frame machine) place.ptr base.layout.size)
    (within : amount.bytes.toNat ≤ base.layout.size.bytes.toNat) (signed : base.layout.size.bytes.toNat < 2^63) :
    s.cfg.projection.place.validate () ⟨.local frames.size localId (some amount) frame.localsIdentity,s.abi.ret.layout⟩
      (LocalUnit.current frames frame machine) = .ok () (LocalUnit.current frames frame machine) := by
  let state := LocalUnit.current frames frame machine
  have activeFoot := ProjectedFootprint.atState state (BodyValidation.active state) place.ptr base.layout.size footprint rfl rfl
  have inbounds := ProjectedInbounds.source s metadata (BodyValidation.active state) place id tag concrete
    base.layout.size amount activeFoot within signed
  have wrapping := ProjectionWrapping.source s metadata (BodyValidation.active state) place amount
  exact ProjectedIndirectValidation.validate_projected s metadata profile remaining capacity positive frames frame machine
    localId slot base place _ amount atSlot live cache noClocks noGhost shallow inbounds wrapping
end EmptyFunction.ProjectedValidate
