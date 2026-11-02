import duplicate_prefix.RootReferenceRvalue
import duplicate_prefix.PointerAddFacts
namespace DuplicatePrefix.RootReferenceFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootReferenceInfo RootReferenceRvalue
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def destination (shared : Bool) : MIR.LocalId := if shared then 12 else 16
def location (shared : Bool) : Location := if shared then ⟨2,11⟩ else ⟨6,7⟩

theorem statement (shared : Bool) :
    CopyPreconditions.Bodies.statementKindAt RootBody.reflected.body.body (location shared).block (location shared).statementIndex =
      some (.Assign ⟨destination shared,#[]⟩ (.Ref .Erased (borrowKind shared) ⟨1,#[.Deref]⟩)) := by
  cases shared <;> decide +kernel

theorem normalized_destination (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (shared : Bool) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame (destination shared) =
      .ok (layout shared).ty := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  cases shared <;> with_unfolding_all rfl

theorem compute_destination
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (shared : Bool) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler (destination shared)
      (Storage.withCurrent frames frame machine) = .ok (layout shared) (Storage.withCurrent frames frame machine) := by
  apply PointerAddFacts.compute_local frames frame machine (destination shared) (layout shared).ty (layout shared)
    (normalized_destination frame sourceBody identity callee shared)
  cases shared with
  | false =>
    rw [layout,if_neg (by decide),ActualReferenceMetadata.reference_ty]
    exact RootCompilerFacts.slice_layout_eq
  | true =>
    rw [layout,if_pos rfl,SharedReferenceMetadata.shared_layout_type]
    exact SharedReferenceMetadata.shared_layout_eq

#print axioms compute_destination
open Lean Elab Command in
run_cmd do
  for declaration in [``statement, ``normalized_destination, ``compute_destination] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end DuplicatePrefix.RootReferenceFacts
