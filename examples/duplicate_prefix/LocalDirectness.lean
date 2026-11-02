import duplicate_prefix.CopyHelperCleanup
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.LocalDirectness
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 8192

theorem live (frame : CompilerFrameContext.ActualFrame) (loc : Location) (id : Miri.MIR.LocalId)
    (valid : id < frame.locals.size) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate (SourceSteps.liveFrame frame loc id valid) :=
  CopyHelperCleanup.all_immediate_set frame id _ valid all (by intro memory;simp)

theorem dead (frame : CompilerFrameContext.ActualFrame) (loc : Location) (id : Miri.MIR.LocalId)
    (valid : id < frame.locals.size) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate (SourceSteps.deadFrame frame loc id valid) :=
  CopyHelperCleanup.all_immediate_set frame id _ valid all (by intro memory;simp)

theorem written_at (frame : CompilerFrameContext.ActualFrame) (id : Miri.MIR.LocalId)
    (layout : LocalLayout) (value : Immediate Provenance) (valid : id < frame.locals.size)
    (loc : Location) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate {(ActualLocalCopy.written frame id layout valid value) with location := .mir loc} :=
  CopyHelperCleanup.all_immediate_written frame id layout value valid all

#print axioms live
#print axioms dead
#print axioms written_at
end DuplicatePrefix.LocalDirectness
