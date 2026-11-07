import Miri.Input.RuntimeProgram

theorem compiler_runtime_same_source (owner : Miri.Input.RuntimeProgram) :
    owner.runtime.source = owner.program.input := rfl

#print axioms compiler_runtime_same_source
