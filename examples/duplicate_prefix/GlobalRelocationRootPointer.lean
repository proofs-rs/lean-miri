import duplicate_prefix.GlobalDataOnlyConversion
import duplicate_prefix.PointerArithmetic
import Miri.Interpreter.PointerSource

/-! A relocation to known compiler memory uses the actual root-pointer and
cached-address source. Compiler provenance flags do not replace the canonical
allocation ID or borrow root. -/
namespace DuplicatePrefix.GlobalRelocationRootPointer
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem cached {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (offset base : UInt64) (root : BorTag)
    (source : Allocation CtfeProvenance Unit)
    (descriptor : before.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? provenance.allocId = some root)
    (addressCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) =
      some ⟨provenance.allocId,base⟩)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    PointerSource.globalRootPointer choices hooks externStatic (Pointer.new provenance (Size.ofBytes offset)) before =
      .ok (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes (base+offset))) before := by
  have rootEq := GlobalState.rootPointerTag_existing tracker.global provenance.allocId root rootCached
  have unchanged : {before with borrowTracker := some tracker} = before := by rw [←enabled]
  simp only [PointerSource.globalRootPointer,Pointer.new,descriptor,enabled,rootEq,
    MachineAddress.addrFromAllocId,get,getThe,MonadStateOf.get,EStateM.get,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,unchanged,addressCached,
    width]
  have wrapping := DuplicatePrefix.PointerArithmetic.wrapping_offset_u64
    (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)) (Size.ofBytes offset)
  change (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)).wrappingOffset
    (Size.ofBytes offset) ⟨Size.ofBytes 8⟩ = _ at wrapping
  simp only [Pointer.new] at wrapping
  rw [wrapping]
  rfl
end DuplicatePrefix.GlobalRelocationRootPointer

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GlobalRelocationRootPointer.cached) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved global relocation root pointer dependency {dependency}"
