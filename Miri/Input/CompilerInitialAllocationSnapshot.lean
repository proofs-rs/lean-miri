import Miri.Memory.MemoryState
import Miri.Input.InstanceArena

namespace Miri.Input.CompilerInitialAllocation
open Lean Miri.Memory Miri.ABI GenericSubstitution
set_option autoImplicit false
variable {P E K : Type}
structure Relocation where
  slot : UInt64
  target : UInt64
  offset : Nat
  immutable : Bool
  shared : Bool
  deriving DecidableEq, BEq, Repr

structure MemoryKey where
  bytes : Array UInt8
  initMask : InitMask
  alignment : UInt64
  mutable : Bool
  pointerBytes : UInt64
  littleEndian : Bool
  provenance : ProvenanceMap CtfeProvenance
  deriving DecidableEq, Repr

instance : BEq MemoryKey := ⟨fun a b => decide (a = b)⟩

instance : BEq InstanceArena.Key := ⟨fun a b => decide (a = b)⟩

/-- Symbolic keys use the actual execution-owned type/instance identities.
No serializer graph allocation ID appears in this key type. -/
inductive GlobalKey where
  | memory (value : MemoryKey)
  | function (value : InstanceArena.Key)
  | static (definition : DefinitionIdentity)
  | typeId (type : TypeId)
  | vtable (type : TypeId) (predicates : Array VtablePredicate)
  deriving BEq

/-- These must be supplied by the strict source/type decoder for this same
World. Missing symbolic constructors are errors, never anonymous opaque keys. -/
structure Symbols where
  pointerBytes : UInt64
  littleEndian : Bool
  function : Json → Except String InstanceArena.Key
  type : Json → Except String TypeId
  predicates : Json → Except String (Array VtablePredicate)

/-- Source-only static declaration, not a compiler layout answer. -/
structure StaticSource where
  type : Option TypeId
  explicitAlignBytes : Option UInt64
  mutability : MemoryMutability
  isStatic : Bool
  foreignItem : Bool
  nested : Bool
  threadLocal : Bool

structure Binding where
  source : UInt64
  key : GlobalKey
  staticSource : Option StaticSource := none

structure DedupBinding where
  key : GlobalKey
  salt : UInt64
  source : UInt64

structure Effects where
  unchanged : Bool
  beforeNext : UInt64
  afterNext : UInt64
  added : Array UInt64
  removed : Array UInt64
  changed : Array UInt64
  beforeDedup : Nat
  afterDedup : Nat
  dedupChanged : Bool

structure Snapshot where
  next : UInt64
  globals : Array Binding
  dedup : Array DedupBinding
  captureEffects : Effects
  serializationEffects : Effects


end Miri.Input.CompilerInitialAllocation
