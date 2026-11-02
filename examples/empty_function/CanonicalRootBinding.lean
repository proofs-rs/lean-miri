import empty_function.CanonicalEnsureRoute
import empty_function.ForeignResolverPrelude
namespace EmptyFunction.CanonicalRootBinding
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.MaterializationPreservation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem root (s : Static) :
    (globalLeaves s).globalRootPointer = PointerSource.globalRootPointer ChoiceExecution.tapeAccess
      (source s).address (ForeignResolverPrelude.resolver s (source s).address) := by
  with_unfolding_all rfl

theorem classifier (s : Static) : (source s).address.classifyAddressError = PointerSource.addressError := by
  rfl

theorem width (s : Static) (metadata : Specification.Metadata s) :
    (source s).address.arithmetic = ⟨Size.ofBytes 8⟩ := by
  change (⟨s.prepared.compiler.runtime.target.pointerSize⟩ : PointerArithmetic) = _
  rw [metadata.pointerSize]
end EmptyFunction.CanonicalRootBinding
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalRootBinding.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical-root-binding axiom {dependency} in {name}"
