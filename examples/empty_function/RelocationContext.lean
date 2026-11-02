import empty_function.ChoiceExecution
namespace EmptyFunction.RelocationContext
set_option autoImplicit false
/-- The caller-visible non-choice user fields read by RuntimeContext. Root
address allocation changes the supplied tape, not types, validation or I/O. -/
def view (payload : ChoiceExecution.Payload) :=
  (payload.payload.user.types,payload.ghost,payload.validation,
    payload.payload.user.host.ioSources,payload.payload.user.host.control)

theorem put (state : ChoiceExecution.S) (tape : Miri.Interpreter.ExecutionChoices.Tape) :
    view (ChoiceExecution.tapeAccess.put state tape).user.payload = view state.user.payload := rfl
end EmptyFunction.RelocationContext
