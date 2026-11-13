import Miri.Input.CompilerInitialAllocationWorld
import Miri.Input.CompilerInitialCtfeRootSource
import Miri.Input.CompilerProviders
import Miri.Input.AllocationImage

/-! Engine result interface contains no execution configuration or EvalWorld.
The production wrapper supplies the fixed-Step engine explicitly. -/
namespace Miri.Input.CompilerInitialCtfeRootResult
open Miri.Memory Miri.MIR Miri.Interpreter
structure Result where
  value : UInt32
  root : AllocId
  type : TyId
  pcs : Array (Nat × Nat)
structure Attempt where
  outcome : Except String Result
  allocations : CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
  types : RuntimeArrayTypes.World
  blocked : Bool
abbrev Engine := CompilerProviders.Prepared → AllocationImage.Imported → RuntimeArrayTypes.World →
  CompilerInitialCtfeRootSource.Registered →
  CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind → Attempt
end Miri.Input.CompilerInitialCtfeRootResult
