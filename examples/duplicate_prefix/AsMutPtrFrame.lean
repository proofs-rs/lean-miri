import duplicate_prefix.AsMutPtrStorage
import duplicate_prefix.AsMutPtrRawAssign
namespace DuplicatePrefix.AsMutPtrFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def entered (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 5) :=
  {frame with
   locals := #[frame.locals[0]'(by omega),frame.locals[1]'(by omega),
    ⟨.live (.immediate .uninit),none⟩,⟨.live (.immediate .uninit),none⟩,⟨.live (.immediate .uninit),none⟩]
   location := .mir ⟨0,3⟩}

theorem after_storage (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 5)
    (cache2 : (frame.locals[2]'(by omega)).layout = none)
    (cache3 : (frame.locals[3]'(by omega)).layout = none)
    (cache4 : (frame.locals[4]'(by omega)).layout = none) :
    AsMutPtrStorage.afterStorageFrame frame size = entered frame size := by
  unfold AsMutPtrStorage.afterStorageFrame SourceSteps.liveFrame entered
  simp only
  congr 1
  apply Array.ext
  · simp [size]
  · intro i left right
    have cases5 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by
      have bound : i < 5 := by simpa using right
      omega
    rcases cases5 with rfl | rfl | rfl | rfl | rfl <;>
      simp [Array.getElem_set,cache2,cache3,cache4]

#print axioms after_storage
end DuplicatePrefix.AsMutPtrFrame
