import empty_function.CanonicalLatentConcrete
import empty_function.CanonicalLatentWildcard
import empty_function.IntegerEndpoint
namespace EmptyFunction.CanonicalLatentMemoryResult
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false

/-- Whole fixed-interpreter call for the ordinary latent memory family. The
classification is stated solely over original candidate geometry and original
source/target descriptors. Other source and target kinds remain separate
families of the full current-caller goal. -/
theorem result (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p) (destination : InputDraft.MemoryDestination s p input.tracker)
    (ordinary : CanonicalLatentPreflight.Ordinary s p) :
    WholeCall.Result s (Preservation.Preserves s) p := by
  cases encoding : destination.place.mplace.ptr.provenance with
  | none => exact IntegerEndpoint.result s metadata profile p runtime input resources destination encoding
  | some provenance =>
    cases provenance with
    | wildcard => exact CanonicalLatentWildcard.result s metadata profile p runtime input resources destination encoding ordinary
    | concrete id tag =>
      have selected : ChoiceAdmission.SelectedId p id :=
        .concrete destination.place.mplace.ptr tag (by simp [InputDraft.effectivePointer,destination.encoding]) encoding
      obtain ⟨source,absent,noFunction,noVaList,descriptor,targets⟩ := ordinary id selected
      exact CanonicalLatentConcrete.result s metadata profile p runtime input resources destination id tag encoding
        source absent noFunction noVaList descriptor targets
end EmptyFunction.CanonicalLatentMemoryResult
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.CanonicalLatentMemoryResult." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent memory axiom {dependency} in {name}"
