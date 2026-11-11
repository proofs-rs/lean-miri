import Miri.Input.TableCore

namespace Miri.Input.DecoderValues
open JsonReader

def hexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def validHex (value : String) : Bool := value.toList.all hexDigit && value.length % 2 == 0

def allocationKind (kind : String) : Except String AllocationKind :=
  match kind with
  | "memory" => pure (.memory)
  | "function" => pure (.function)
  | "static" => pure (.static)
  | "vtable" => pure (.vtable)
  | "type_id" => pure (.typeId)
  | "" => throw "allocation kind is missing"
  | other => throw s!"unrecognized allocationKind tag `{other}`"

def vtablePredicateKind (tag : String) : Except String VtablePredicateKind :=
  match tag with
  | "trait" => pure (.trait)
  | "auto_trait" => pure (.autoTrait)
  | "projection" => pure (.projection)
  | other => throw s!"unrecognized vtablePredicateKind tag `{other}`"

def vtableEntryKind (tag : String) : Except String VtableEntryKind :=
  match tag with
  | "drop_in_place_null" => pure (.dropInPlaceNull)
  | "drop_in_place" => pure (.dropInPlace)
  | "size_bytes" => pure (.sizeBytes)
  | "align_bytes" => pure (.alignBytes)
  | "vacant" => pure (.vacant)
  | "method" => pure (.method)
  | "supertrait_vtable_pointer" => pure (.supertraitVtablePointer)
  | other => throw s!"unrecognized vtableEntryKind tag `{other}`"

def parseSourceAllocIdKind (value path : String) : Except String SourceAllocIdKind := do
  match value with
  | "dangling" => pure .dangling
  | "memory" => pure .memory
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | _ => throw s!"{path}: unknown source AllocId kind `{value}`"

def canonicalLowerHex (value : String) : Bool :=
  validHex value && value.toList.all (fun char =>
    (char >= '0' && char <= '9') || (char >= 'a' && char <= 'f'))

def allocationNodeMatchesSourceKind (sourceKind : SourceAllocIdKind)
    (nodeKind : AllocationKind) : Bool :=
  match sourceKind, nodeKind with
  | .memory, .memory | .function, .function | .vtable, .vtable
  | .static, .static | .typeId, .typeId => true
  | _, _ => false

def parseSourceAllocIdDedupKind (value path : String) : Except String SourceAllocIdDedupKind := do
  match value with
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | "memory" | "memory_const_allocation" => pure .memory
  | "bytes" | "byte_memory" => pure .bytes
  | _ => throw s!"{path}: unknown source AllocId dedup key kind `{value}`"

def passModeKind (tag : String) : Except String PassModeKind :=
  match tag with
  | "Ignore" => pure (.ignore)
  | "Direct" => pure (.direct)
  | "Pair" => pure (.pair)
  | "Cast" => pure (.cast)
  | "Indirect" => pure (.indirect)
  | "IndirectUnsized" => pure (.indirectUnsized)
  | other => throw s!"unrecognized passModeKind tag `{other}`"

def abiRegisterKind (tag : String) : Except String AbiRegisterKind :=
  match tag with
  | "integer" => pure (.integer)
  | "float" => pure (.float)
  | "ppc_f128" => pure (.ppcF128)
  | "vector" => pure (.vector)
  | other => throw s!"unrecognized abiRegisterKind tag `{other}`"

def canonicalAbiKind (tag : String) : Except String CanonicalAbiKind :=
  match tag with
  | "c" => pure (.c)
  | "rust" => pure (.rust)
  | "rust_cold" => pure (.rustCold)
  | "rust_preserve_none" => pure (.rustPreserveNone)
  | "rust_tail" => pure (.rustTail)
  | "custom" => pure (.custom)
  | "swift" => pure (.swift)
  | "arm" => pure (.arm)
  | "gpu_kernel" => pure (.gpuKernel)
  | "interrupt" => pure (.interrupt)
  | "x86" => pure (.x86)
  | other => throw s!"unrecognized canonicalAbiKind tag `{other}`"

def armCallKind (tag : String) : Except String ArmCallKind :=
  match tag with
  | "aapcs" => pure (.aapcs)
  | "cmse_nonsecure_call" => pure (.cmseNonSecureCall)
  | "cmse_nonsecure_entry" => pure (.cmseNonSecureEntry)
  | other => throw s!"unrecognized armCallKind tag `{other}`"

def interruptCallKind (tag : String) : Except String InterruptCallKind :=
  match tag with
  | "avr" => pure (.avr)
  | "avr_non_blocking" => pure (.avrNonBlocking)
  | "msp430" => pure (.msp430)
  | "riscv_machine" => pure (.riscvMachine)
  | "riscv_supervisor" => pure (.riscvSupervisor)
  | "x86" => pure (.x86)
  | other => throw s!"unrecognized interruptCallKind tag `{other}`"

def x86CallKind (tag : String) : Except String X86CallKind :=
  match tag with
  | "fastcall" => pure (.fastcall)
  | "stdcall" => pure (.stdcall)
  | "sysv64" => pure (.sysv64)
  | "thiscall" => pure (.thiscall)
  | "vectorcall" => pure (.vectorcall)
  | "win64" => pure (.win64)
  | other => throw s!"unrecognized x86CallKind tag `{other}`"

private structure ParseInitRangeFields where
  state : Option (String) := none
  start_bytes : Option (Nat) := none
  end_bytes_exclusive : Option (Nat) := none

def parseInitRange (path : String) : Parser (InitRange) := do
  let s ← object (ParseInitRangeFields.mk none none none) fun s key => do
    match key with
    | "state" => return { s with state := some (← string) }
    | "start_bytes" => return { s with start_bytes := some (← natural) }
    | "end_bytes_exclusive" => return { s with end_bytes_exclusive := some (← natural) }
    | _ => skipValue; pure s
  let state ← required s.state (path ++ ".state")
  let start_bytes ← required s.start_bytes (path ++ ".start_bytes")
  let end_bytes_exclusive ← required s.end_bytes_exclusive (path ++ ".end_bytes_exclusive")
  let initialized ← match state with
    | "initialized" => pure true
    | "uninitialized" => pure false
    | _ => fail s!"{path}.state: unrecognized initialization state `{state}`"
  unless start_bytes ≤ end_bytes_exclusive do fail s!"{path}: reversed initialization range"
  return ⟨initialized, start_bytes, end_bytes_exclusive⟩

private structure ParseRelocationFields where
  storage_offset_bytes : Option (Nat) := none
  target : Option (Nat) := none
  target_offset_encoded_bytes : Option (String) := none
  immutable : Option (Bool) := none
  shared_ref : Option (Bool) := none

def parseRelocation (path : String) : Parser (Relocation) := do
  let s ← object (ParseRelocationFields.mk none none none none none) fun s key => do
    match key with
    | "storage_offset_bytes" => return { s with storage_offset_bytes := some (← natural) }
    | "target" => return { s with target := some (← natural) }
    | "target_offset_encoded_bytes" => return { s with target_offset_encoded_bytes := some (← string) }
    | "immutable" => return { s with immutable := some (← boolean) }
    | "shared_ref" => return { s with shared_ref := some (← boolean) }
    | _ => skipValue; pure s
  let storage_offset_bytes ← required s.storage_offset_bytes (path ++ ".storage_offset_bytes")
  let target ← required s.target (path ++ ".target")
  let target_offset_encoded_bytes ← required s.target_offset_encoded_bytes (path ++ ".target_offset_encoded_bytes")
  let immutable ← required s.immutable (path ++ ".immutable")
  let shared_ref ← required s.shared_ref (path ++ ".shared_ref")
  let some leanAllocId := Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat (target + 1)) | fail s!"{path}: invalid CTFE allocation identity"
  let provenance ← liftExcept ((Miri.Memory.CtfeProvenance.fromParts (leanAllocId, immutable, shared_ref)).mapError (fun _ => s!"{path}: invalid CTFE provenance flags or allocation-ID width"))
  unless validHex target_offset_encoded_bytes do fail s!"{path}: malformed hexadecimal bytes"
  return ⟨storage_offset_bytes, target, target_offset_encoded_bytes, immutable, shared_ref, provenance⟩

private def memoryMutability : Parser MemoryMutability := do
  match ← string with
  | "mutable" => pure .mutable
  | "immutable" => pure .immutable
  | value => fail s!"unknown memory mutability `{value}`"

private def checkedMemory (path : String) (size align : Nat) (mutability : MemoryMutability)
    (bytes : String) (ranges : Array InitRange) (relocations : Array Relocation) : Parser AllocationMemory := do
  unless validHex bytes do fail s!"{path}.bytes_hex: malformed hexadecimal bytes"
  unless bytes.length / 2 == size do fail s!"{path}.bytes_hex: byte buffer length does not equal size_bytes"
  let mut cursor := 0
  for chunk in ranges do
    unless chunk.startBytes == cursor do fail s!"{path}.initialization_ranges: ranges overlap or leave a gap"
    unless chunk.endBytesExclusive ≤ size do fail s!"{path}.initialization_ranges: range exceeds allocation size"
    cursor := chunk.endBytesExclusive
  unless cursor == size do fail s!"{path}.initialization_ranges: ranges do not cover the allocation"
  for relocation in relocations do
    unless relocation.storageOffsetBytes + relocation.targetOffsetEncodedBytes.length / 2 ≤ size do
      fail s!"{path}.relocations: relocation's encoded pointer bytes exceed allocation size"
  unless align > 0 do fail s!"{path}.align_bytes: allocation alignment must be nonzero"
  return ⟨size, align, mutability, bytes, ranges, relocations⟩

private structure ParseAllocationMemoryFields where
  size_bytes : Option (Nat) := none
  align_bytes : Option (Nat) := none
  mutability : Option (MemoryMutability) := none
  bytes_hex : Option (String) := none
  initialization_ranges : Option (Array InitRange) := none
  relocations : Option (Array Relocation) := none

def parseAllocationMemory (path : String) : Parser (AllocationMemory) := do
  let s ← object (ParseAllocationMemoryFields.mk none none none none none none) fun s key => do
    match key with
    | "size_bytes" => return { s with size_bytes := some (← natural) }
    | "align_bytes" => return { s with align_bytes := some (← natural) }
    | "mutability" => return { s with mutability := some (← memoryMutability) }
    | "bytes_hex" => return { s with bytes_hex := some (← string) }
    | "initialization_ranges" => return { s with initialization_ranges := some (← array (parseInitRange (path ++ ".initialization_ranges"))) }
    | "relocations" => return { s with relocations := some (← array (parseRelocation (path ++ ".relocations"))) }
    | _ => skipValue; pure s
  let size_bytes ← required s.size_bytes (path ++ ".size_bytes")
  let align_bytes ← required s.align_bytes (path ++ ".align_bytes")
  let mutability ← required s.mutability (path ++ ".mutability")
  let bytes_hex ← required s.bytes_hex (path ++ ".bytes_hex")
  let initialization_ranges ← required s.initialization_ranges (path ++ ".initialization_ranges")
  let relocations ← required s.relocations (path ++ ".relocations")
  checkedMemory path size_bytes align_bytes mutability bytes_hex initialization_ranges relocations

private structure ParseDefinitionIdFields where
  crate : Option (Nat) := none
  index : Option (Nat) := none

def parseDefinitionId (path : String) : Parser (DefinitionId) := do
  let s ← object (ParseDefinitionIdFields.mk none none) fun s key => do
    match key with
    | "crate" => return { s with crate := some (← natural) }
    | "index" => return { s with index := some (← natural) }
    | _ => skipValue; pure s
  let crate ← required s.crate (path ++ ".crate")
  let index ← required s.index (path ++ ".index")
  return ⟨crate, index⟩

def parseDefinitionRef (_path : String) : Parser DefinitionRef := natural

private structure ParseScopeRootFields where
  def_path : Option (String) := none
  def_id : Option (Nat) := none

private def parseScopeRoot (path : String) : Parser (ScopeRoot) := do
  let s ← object (ParseScopeRootFields.mk none none) fun s key => do
    match key with
    | "def_path" => return { s with def_path := some (← string) }
    | "def_id" => return { s with def_id := some (← natural) }
    | _ => skipValue; pure s
  let def_path ← required s.def_path (path ++ ".def_path")
  let def_id ← required s.def_id (path ++ ".def_id")
  if def_path.isEmpty then fail s!"{path}.def_path: selected root path cannot be empty"
  return ⟨def_path, def_id⟩

private structure ParseSelectedScopeFields where
  kind : Option (String) := none
  semantics : Option (String) := none
  roots : Option (Array ScopeRoot) := none

def parseSelectedScope (path : String) : Parser (SelectedScope) := do
  let s ← object (ParseSelectedScopeFields.mk none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "semantics" => return { s with semantics := some (← string) }
    | "roots" => return { s with roots := some (← array (parseScopeRoot (path ++ ".roots"))) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let semantics ← required s.semantics (path ++ ".semantics")
  let roots ← required s.roots (path ++ ".roots")
  unless roots.toList.eraseDups.length == roots.size do fail s!"{path}.roots: duplicate selected roots"
  return ⟨kind, semantics, roots⟩

private structure ParseProjectionTermFields where
  kind : Option (String) := none
  value : Option (Nat) := none

private def parseProjectionTerm (path : String) : Parser (Nat) := do
  let s ← object (ParseProjectionTermFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "value" => return { s with value := some (← natural) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let value ← required s.value (path ++ ".value")
  unless kind == "type" do fail s!"{path}: unsupported predicate projection term"
  pure value

private structure ParseVtablePredicateFields where
  kind : Option (String) := none
  def_id : Option (Nat) := none
  def_path : Option (Option String) := none
  generic_args : Option (Array Miri.MIR.GenericArg) := none
  bound_variables : Option (Array Miri.MIR.BoundVariableKind) := none
  term : Option (Option Nat) := none

def parseVtablePredicate (path : String) : Parser (VtablePredicate) := do
  let s ← object (ParseVtablePredicateFields.mk none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "def_id" => return { s with def_id := some (← natural) }
    | "def_path" => return { s with def_path := some (← nullable string) }
    | "generic_args" => return { s with generic_args := some (← GenericArgsCodec.decode) }
    | "bound_variables" => return { s with bound_variables := some (← array GenericArgsCodec.boundVariable) }
    | "term" => return { s with term := some (← nullable (parseProjectionTerm (path ++ ".term"))) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let def_id ← required s.def_id (path ++ ".def_id")
  let def_path ← pure (s.def_path.getD none)
  let generic_args ← pure (s.generic_args.getD  #[])
  let bound_variables ← required s.bound_variables (path ++ ".bound_variables")
  let term ← pure (s.term.getD none)
  let kind ← liftExcept (vtablePredicateKind kind)
  let allowed : List String := match kind with
    | .autoTrait => []
    | .trait => ["generic_args"]
    | .projection => ["generic_args", "term"]
  if s.generic_args.isSome && !(allowed.contains "generic_args") then fail s!"{path}: field `generic_args` is incompatible with the selected variant"
  if s.term.isSome && !(allowed.contains "term") then fail s!"{path}: field `term` is incompatible with the selected variant"
  if kind != .autoTrait && s.generic_args.isNone then fail s!"{path}: predicate is missing generic_args"
  if kind == .projection && term.isNone then fail s!"{path}: projection predicate has no term"
  return ⟨kind, def_id, def_path, generic_args, bound_variables, term⟩

private structure ParseVtableEntryFields where
  kind : Option (String) := none
  instance_id : Option (Option Nat) := none
  allocation : Option (Option Nat) := none
  trait_def_id : Option (Option Nat) := none
  trait_def_path : Option (Option String) := none

def parseVtableEntry (path : String) : Parser (VtableEntry) := do
  let s ← object (ParseVtableEntryFields.mk none none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "instance_id" => return { s with instance_id := some (← nullable natural) }
    | "allocation" => return { s with allocation := some (← nullable natural) }
    | "trait_def_id" => return { s with trait_def_id := some (← nullable natural) }
    | "trait_def_path" => return { s with trait_def_path := some (← nullable string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let instance_id ← pure (s.instance_id.getD none)
  let allocation ← pure (s.allocation.getD none)
  let trait_def_id ← pure (s.trait_def_id.getD none)
  let trait_def_path ← pure (s.trait_def_path.getD none)
  let kind ← liftExcept (vtableEntryKind kind)
  let allowed : List String := match kind with
    | .dropInPlace | .method => ["instance_id"]
    | .supertraitVtablePointer => ["allocation", "trait_def_id", "trait_def_path"]
    | _ => []
  if s.instance_id.isSome && !(allowed.contains "instance_id") then fail s!"{path}: field `instance_id` is incompatible with the selected variant"
  if s.allocation.isSome && !(allowed.contains "allocation") then fail s!"{path}: field `allocation` is incompatible with the selected variant"
  if s.trait_def_id.isSome && !(allowed.contains "trait_def_id") then fail s!"{path}: field `trait_def_id` is incompatible with the selected variant"
  if s.trait_def_path.isSome && !(allowed.contains "trait_def_path") then fail s!"{path}: field `trait_def_path` is incompatible with the selected variant"
  match kind with
  | .dropInPlace | .method => unless instance_id.isSome do fail s!"{path}: vtable entry is missing instance_id"
  | .supertraitVtablePointer => unless allocation.isSome && trait_def_id.isSome do fail s!"{path}: supertrait entry is incomplete"
  | _ => pure ()
  return ⟨kind, instance_id, allocation, trait_def_id, trait_def_path⟩

def decodeVtableEntry (path : String := "$compiler_vtable_entry") : Parser VtableEntry := parseVtableEntry path

private structure DecodeStaticGlobalInfoFields where
  nested : Option (Bool) := none
  size_bytes : Option (Nat) := none
  align_bytes : Option (Nat) := none
  mutability : Option (MemoryMutability) := none
  is_static : Option (Bool) := none
  is_foreign_item : Option (Bool) := none
  thread_local : Option (Bool) := none

def decodeStaticGlobalInfo (path : String := "$static_global_info") : Parser (StaticGlobalInfo) := do
  let s ← object (DecodeStaticGlobalInfoFields.mk none none none none none none none) fun s key => do
    match key with
    | "nested" => return { s with nested := some (← boolean) }
    | "size_bytes" => return { s with size_bytes := some (← natural) }
    | "align_bytes" => return { s with align_bytes := some (← natural) }
    | "mutability" => return { s with mutability := some (← memoryMutability) }
    | "is_static" => return { s with is_static := some (← boolean) }
    | "is_foreign_item" => return { s with is_foreign_item := some (← boolean) }
    | "thread_local" => return { s with thread_local := some (← boolean) }
    | _ => skipValue; pure s
  let nested ← required s.nested (path ++ ".nested")
  let size_bytes ← required s.size_bytes (path ++ ".size_bytes")
  let align_bytes ← required s.align_bytes (path ++ ".align_bytes")
  let mutability ← required s.mutability (path ++ ".mutability")
  let is_static ← required s.is_static (path ++ ".is_static")
  let is_foreign_item ← required s.is_foreign_item (path ++ ".is_foreign_item")
  let thread_local ← required s.thread_local (path ++ ".thread_local")
  return ⟨nested, size_bytes, align_bytes, mutability, is_static, is_foreign_item, thread_local⟩

private structure ParseTlsInitializerFields where
  allocation : Option (Option AllocationMemory) := none

private def parseTlsInitializer (path : String) : Parser (Option AllocationMemory) := do
  let s ← object (ParseTlsInitializerFields.mk none) fun s key => do
    match key with
    | "allocation" => return { s with allocation := some (← nullable (parseAllocationMemory (path ++ ".allocation"))) }
    | _ => skipValue; pure s
  let allocation ← pure (s.allocation.getD none)
  pure allocation

private structure ParseThreadLocalFields where
  def_id : Option (Nat) := none
  global_info : Option (StaticGlobalInfo) := none
  initializer : Option (Option AllocationMemory) := none

def parseThreadLocal (path : String := "$thread_local") : Parser (Catalog.ThreadLocal) := do
  let s ← object (ParseThreadLocalFields.mk none none none) fun s key => do
    match key with
    | "def_id" => return { s with def_id := some (← natural) }
    | "global_info" => return { s with global_info := some (← decodeStaticGlobalInfo (path ++ ".global_info")) }
    | "initializer" => return { s with initializer := some (← parseTlsInitializer (path ++ ".initializer")) }
    | _ => skipValue; pure s
  let def_id ← required s.def_id (path ++ ".def_id")
  let global_info ← required s.global_info (path ++ ".global_info")
  let initializer ← required s.initializer (path ++ ".initializer")
  unless global_info.isStatic && global_info.threadLocal do fail "TLS declaration compiler query evidence is unresolved or inconsistent"
  unless global_info.foreignItem || initializer.isSome do fail "TLS declaration initializer is missing"
  return ⟨def_id, global_info, if global_info.foreignItem then none else initializer⟩

private structure ParseAllocationFields where
  allocation_id : Option (Nat) := none
  source_alloc_id : Option (Option Nat) := none
  kind : Option (String) := none
  size_bytes : Option (Option (Nat)) := none
  align_bytes : Option (Option (Nat)) := none
  mutability : Option (Option (MemoryMutability)) := none
  bytes_hex : Option (Option (String)) := none
  initialization_ranges : Option (Option (Array InitRange)) := none
  relocations : Option (Option (Array Relocation)) := none
  instance_id : Option (Option Nat) := none
  global_info : Option (Option StaticGlobalInfo) := none
  initializer : Option (Option AllocationMemory) := none
  def_id : Option (Option Nat) := none
  def_path : Option (Option String) := none
  thread_local : Option (Option Bool) := none
  predicates : Option (Option (Array Nat)) := none
  entries : Option (Option (Array VtableEntry)) := none
  type : Option (Option Nat) := none
  principal_predicate : Option (Option Nat) := none

def parseAllocation (path : String) : Parser (AllocationNode) := do
  let s ← object (ParseAllocationFields.mk none none none none none none none none none none none none none none none none none none none) fun s key => do
    match key with
    | "allocation_id" => return { s with allocation_id := some (← natural) }
    | "source_alloc_id" => return { s with source_alloc_id := some (← nullable natural) }
    | "kind" => return { s with kind := some (← string) }
    | "size_bytes" => return { s with size_bytes := some (← nullable (natural)) }
    | "align_bytes" => return { s with align_bytes := some (← nullable (natural)) }
    | "mutability" => return { s with mutability := some (← nullable (memoryMutability)) }
    | "bytes_hex" => return { s with bytes_hex := some (← nullable (string)) }
    | "initialization_ranges" => return { s with initialization_ranges := some (← nullable (array (parseInitRange (path ++ ".initialization_ranges")))) }
    | "relocations" => return { s with relocations := some (← nullable (array (parseRelocation (path ++ ".relocations")))) }
    | "instance_id" => return { s with instance_id := some (← nullable natural) }
    | "global_info" => return { s with global_info := some (← nullable (decodeStaticGlobalInfo (path ++ ".global_info"))) }
    | "initializer" => return { s with initializer := some (← nullable (parseAllocationMemory (path ++ ".initializer"))) }
    | "def_id" => return { s with def_id := some (← nullable natural) }
    | "def_path" => return { s with def_path := some (← nullable string) }
    | "thread_local" => return { s with thread_local := some (← nullable boolean) }
    | "predicates" => return { s with predicates := some (← nullable (array natural)) }
    | "entries" => return { s with entries := some (← nullable (array (parseVtableEntry (path ++ ".entries")))) }
    | "type" => return { s with type := some (← nullable natural) }
    | "principal_predicate" => return { s with principal_predicate := some (← nullable natural) }
    | _ => skipValue; pure s
  let allocation_id ← required s.allocation_id (path ++ ".allocation_id")
  let source_alloc_id ← pure (s.source_alloc_id.getD none)
  let kind ← required s.kind (path ++ ".kind")
  let size_bytes ← pure (s.size_bytes.getD none)
  let align_bytes ← pure (s.align_bytes.getD none)
  let mutability ← pure (s.mutability.getD none)
  let bytes_hex ← pure (s.bytes_hex.getD none)
  let initialization_ranges ← pure (s.initialization_ranges.getD none)
  let relocations ← pure (s.relocations.getD none)
  let instance_id ← pure (s.instance_id.getD none)
  let global_info ← pure (s.global_info.getD none)
  let initializer ← pure (s.initializer.getD none)
  let def_id ← pure (s.def_id.getD none)
  let def_path ← pure (s.def_path.getD none)
  let thread_local ← pure (s.thread_local.getD none)
  let predicates ← pure (s.predicates.getD none)
  let entries ← pure (s.entries.getD none)
  let type ← pure (s.type.getD none)
  let principal_predicate ← pure (s.principal_predicate.getD none)
  let kind ← liftExcept (allocationKind kind)
  let allowed : List String := match kind with
    | .memory => ["size_bytes", "align_bytes", "mutability", "bytes_hex", "initialization_ranges", "relocations"]
    | .function => ["instance_id"]
    | .static => ["global_info", "initializer", "def_id", "def_path", "thread_local"]
    | .vtable => ["type", "size_bytes", "align_bytes", "predicates", "principal_predicate", "entries"]
    | .typeId => ["type"]
  if s.size_bytes.isSome && !(allowed.contains "size_bytes") then fail s!"{path}: field `size_bytes` is incompatible with the selected variant"
  if s.align_bytes.isSome && !(allowed.contains "align_bytes") then fail s!"{path}: field `align_bytes` is incompatible with the selected variant"
  if s.mutability.isSome && !(allowed.contains "mutability") then fail s!"{path}: field `mutability` is incompatible with the selected variant"
  if s.bytes_hex.isSome && !(allowed.contains "bytes_hex") then fail s!"{path}: field `bytes_hex` is incompatible with the selected variant"
  if s.initialization_ranges.isSome && !(allowed.contains "initialization_ranges") then fail s!"{path}: field `initialization_ranges` is incompatible with the selected variant"
  if s.relocations.isSome && !(allowed.contains "relocations") then fail s!"{path}: field `relocations` is incompatible with the selected variant"
  if s.instance_id.isSome && !(allowed.contains "instance_id") then fail s!"{path}: field `instance_id` is incompatible with the selected variant"
  if s.global_info.isSome && !(allowed.contains "global_info") then fail s!"{path}: field `global_info` is incompatible with the selected variant"
  if s.initializer.isSome && !(allowed.contains "initializer") then fail s!"{path}: field `initializer` is incompatible with the selected variant"
  if s.def_id.isSome && !(allowed.contains "def_id") then fail s!"{path}: field `def_id` is incompatible with the selected variant"
  if s.def_path.isSome && !(allowed.contains "def_path") then fail s!"{path}: field `def_path` is incompatible with the selected variant"
  if s.thread_local.isSome && !(allowed.contains "thread_local") then fail s!"{path}: field `thread_local` is incompatible with the selected variant"
  if s.predicates.isSome && !(allowed.contains "predicates") then fail s!"{path}: field `predicates` is incompatible with the selected variant"
  if s.entries.isSome && !(allowed.contains "entries") then fail s!"{path}: field `entries` is incompatible with the selected variant"
  if s.type.isSome && !(allowed.contains "type") then fail s!"{path}: field `type` is incompatible with the selected variant"
  if s.principal_predicate.isSome && !(allowed.contains "principal_predicate") then fail s!"{path}: field `principal_predicate` is incompatible with the selected variant"
  if kind == .vtable && s.principal_predicate.isNone then fail s!"{path}: missing principal_predicate"
  let sourceAllocId ← source_alloc_id.mapM fun value => do
    unless value > 0 && value < 2^64 do fail s!"{path}.source_alloc_id: expected nonzero u64"
    pure (UInt64.ofNat value)
  let (memory, data) ← match kind with
    | .memory => do
      let value ← checkedMemory path (← required size_bytes "size_bytes") (← required align_bytes "align_bytes")
        (← required mutability "mutability") (← required bytes_hex "bytes_hex")
        (← required initialization_ranges "initialization_ranges") (← required relocations "relocations")
      pure (some value, some (AllocationData.memory value))
    | .function => pure (none, some (.function ⟨← required instance_id "instance_id"⟩))
    | .static => do
      let definitionPath ← required def_path "def_path"
      if definitionPath.isEmpty then fail s!"{path}.def_path: static allocation is missing its definition path"
      unless (global_info.map (·.foreignItem)).getD false || initializer.isSome do
        fail s!"{path}.initializer: non-foreign static is missing its initializer image"
      pure (none, some (.static ⟨global_info, ← required def_id "def_id", definitionPath, ← required thread_local "thread_local", initializer⟩))
    | .vtable => pure (none, some (.vtable ⟨principal_predicate, ← required type "type", size_bytes, align_bytes,
        ← required predicates "predicates", ← required entries "entries"⟩))
    | .typeId => pure (none, some (.typeId (← required type "type")))
  return ⟨allocation_id, sourceAllocId, kind, memory, data⟩

private structure ParseSourceAllocIdPoolRowFields where
  source_alloc_id : Option (Nat) := none
  kind : Option (String) := none
  status : Option (String) := none
  allocation_id : Option (Option Nat) := none
  memory_mutability : Option (Option MemoryMutability) := none
  memory_align_bytes : Option (Option Nat) := none
  memory_all_bytes_initialized : Option (Option Bool) := none
  memory_has_provenance : Option (Option Bool) := none
  byte_image_hex : Option (Option String) := none
  opaque_allocation_id : Option (Option Nat) := none

def parseSourceAllocIdPoolRow (path : String) : Parser (SourceAllocIdPoolRow) := do
  let s ← object (ParseSourceAllocIdPoolRowFields.mk none none none none none none none none none none) fun s key => do
    match key with
    | "source_alloc_id" => return { s with source_alloc_id := some (← natural) }
    | "kind" => return { s with kind := some (← string) }
    | "status" => return { s with status := some (← string) }
    | "allocation_id" => return { s with allocation_id := some (← nullable natural) }
    | "memory_mutability" => return { s with memory_mutability := some (← nullable memoryMutability) }
    | "memory_align_bytes" => return { s with memory_align_bytes := some (← nullable natural) }
    | "memory_all_bytes_initialized" => return { s with memory_all_bytes_initialized := some (← nullable boolean) }
    | "memory_has_provenance" => return { s with memory_has_provenance := some (← nullable boolean) }
    | "byte_image_hex" => return { s with byte_image_hex := some (← nullable string) }
    | "opaque_allocation_id" => return { s with opaque_allocation_id := some (← nullable natural) }
    | _ => skipValue; pure s
  let source_alloc_id ← required s.source_alloc_id (path ++ ".source_alloc_id")
  let kind ← required s.kind (path ++ ".kind")
  let status ← required s.status (path ++ ".status")
  let allocation_id ← required s.allocation_id (path ++ ".allocation_id")
  let memory_mutability ← pure (s.memory_mutability.getD none)
  let memory_align_bytes ← pure (s.memory_align_bytes.getD none)
  let memory_all_bytes_initialized ← pure (s.memory_all_bytes_initialized.getD none)
  let memory_has_provenance ← pure (s.memory_has_provenance.getD none)
  let byte_image_hex ← pure (s.byte_image_hex.getD none)
  let opaque_allocation_id ← pure (s.opaque_allocation_id.getD none)
  let raw := source_alloc_id
  unless raw > 0 && raw < 2^64 do fail s!"{path}.source_alloc_id: expected nonzero u64"
  let kind ← liftExcept (parseSourceAllocIdKind kind (path ++ ".kind"))
  if kind != .memory && (s.memory_mutability.isSome || s.memory_align_bytes.isSome || s.memory_all_bytes_initialized.isSome || s.memory_has_provenance.isSome || s.byte_image_hex.isSome) then fail s!"{path}: memory payload belongs only to memory source allocation rows"
  let status ← match status with
    | "dangling" => pure SourceAllocIdStatus.dangling
    | "serialized" => pure .serialized
    | "opaque" => pure .opaque
    | value => fail s!"{path}.status: unknown source AllocId pool status `{value}`"
  if s.opaque_allocation_id.isSome then fail s!"{path}: opaque_allocation_id is not a semantic allocation witness"
  let allocationId := allocation_id
  let (memoryMutability, memoryAlignBytes, memoryAllBytesInitialized, memoryHasProvenance) ← match kind with
    | .memory => pure (some (← required memory_mutability "memory_mutability"), some (← required memory_align_bytes "memory_align_bytes"), some (← required memory_all_bytes_initialized "memory_all_bytes_initialized"), some (← required memory_has_provenance "memory_has_provenance"))
    | _ => pure (none, none, none, none)
  let byteImageHex := byte_image_hex
  if let some image := byteImageHex then
    unless canonicalLowerHex image do fail s!"{joinPath path "byte_image_hex"}: expected canonical lowercase hexadecimal"
  let shapeIsValid := match kind, status, allocationId with
    | .dangling, .dangling, none => true
    | .memory, .serialized, some _ => true
    | .function, .serialized, some _ => true
    | .vtable, .serialized, some _ => true
    | .static, .serialized, some _ => true
    | .typeId, .serialized, some _ => true
    | .memory, .opaque, none => true
    | .function, .opaque, none => true
    | .vtable, .opaque, none => true
    | .static, .opaque, none => true
    | .typeId, .opaque, none => true
    | _, _, _ => false
  unless shapeIsValid do fail s!"{path}: inconsistent kind/status/allocation_id in source AllocId pool row"
  let byteEligible := kind == .memory && memoryMutability == some .immutable && memoryAlignBytes == some 1 &&
    memoryAllBytesInitialized == some true && memoryHasProvenance == some false
  match kind, byteEligible, byteImageHex with
  | .memory, true, some _ =>
    unless status == .serialized && allocationId.isSome do
      fail s!"{path}: eligible byte-memory key requires a serialized allocation node"
  | .memory, false, none => pure ()
  | .memory, _, _ => fail s!"{path}: inconsistent byte-memory eligibility and image"
  | _, _, none => pure ()
  | _, _, some _ => fail s!"{path}: byte-memory image is only valid for memory globals"
  pure ⟨UInt64.ofNat raw, kind, status, allocationId, memoryMutability, memoryAlignBytes,
    memoryAllBytesInitialized, memoryHasProvenance, byteImageHex⟩


private structure ParseSourceAllocIdSaltResultFields where
  source_alloc_id : Option (Nat) := none
  salt : Option (Nat) := none
  allocation_id : Option (Nat) := none

def parseSourceAllocIdSaltResult (path : String) : Parser (SourceAllocIdSaltResult) := do
  let s ← object (ParseSourceAllocIdSaltResultFields.mk none none none) fun s key => do
    match key with
    | "source_alloc_id" => return { s with source_alloc_id := some (← natural) }
    | "salt" => return { s with salt := some (← natural) }
    | "allocation_id" => return { s with allocation_id := some (← natural) }
    | _ => skipValue; pure s
  let source_alloc_id ← required s.source_alloc_id (path ++ ".source_alloc_id")
  let salt ← required s.salt (path ++ ".salt")
  let allocation_id ← required s.allocation_id (path ++ ".allocation_id")
  unless source_alloc_id > 0 && source_alloc_id < 2^64 do fail s!"{path}.source_alloc_id: expected nonzero u64"
  return ⟨salt, allocation_id, UInt64.ofNat source_alloc_id⟩

private structure ParseSourceAllocIdDedupRowFields where
  key_kind : Option (String) := none
  salts : Option (Array SourceAllocIdSaltResult) := none
  bytes_hex : Option (Option String) := none
  key_allocation_id : Option (Nat) := none

def parseSourceAllocIdDedupRow (path : String) : Parser (SourceAllocIdDedupRow) := do
  let s ← object (ParseSourceAllocIdDedupRowFields.mk none none none none) fun s key => do
    match key with
    | "key_kind" => return { s with key_kind := some (← string) }
    | "salts" => return { s with salts := some (← array (parseSourceAllocIdSaltResult (path ++ ".salts"))) }
    | "bytes_hex" => return { s with bytes_hex := some (← nullable string) }
    | "key_allocation_id" => return { s with key_allocation_id := some (← natural) }
    | _ => skipValue; pure s
  let key_kind ← required s.key_kind (path ++ ".key_kind")
  let salts ← required s.salts (path ++ ".salts")
  let bytes_hex ← pure (s.bytes_hex.getD none)
  let key_allocation_id ← required s.key_allocation_id (path ++ ".key_allocation_id")
  let keyKind ← liftExcept (parseSourceAllocIdDedupKind key_kind (path ++ ".key_kind"))
  if let some image := bytes_hex then
    unless canonicalLowerHex image do fail s!"{path}.bytes_hex: expected canonical lowercase hexadecimal"
  match keyKind, bytes_hex with
  | .bytes, some _ => pure ()
  | .bytes, none => fail s!"{path}.bytes_hex: required for byte-image dedup key"
  | _, some _ => fail s!"{path}.bytes_hex: only valid for byte-image dedup key"
  | _, none => pure ()
  return ⟨keyKind, key_allocation_id, bytes_hex, salts⟩

private structure ParseAllocFrontierFields where
  last_reserved_source_alloc_id : Option (Nat) := none
  next_source_alloc_id : Option (Nat) := none
  final_sentinel_source_alloc_id : Option (Nat) := none

private def parseAllocFrontier (path : String) : Parser (Nat × Nat × Nat) := do
  let s ← object (ParseAllocFrontierFields.mk none none none) fun s key => do
    match key with
    | "last_reserved_source_alloc_id" => return { s with last_reserved_source_alloc_id := some (← natural) }
    | "next_source_alloc_id" => return { s with next_source_alloc_id := some (← natural) }
    | "final_sentinel_source_alloc_id" => return { s with final_sentinel_source_alloc_id := some (← natural) }
    | _ => skipValue; pure s
  let last_reserved_source_alloc_id ← required s.last_reserved_source_alloc_id (path ++ ".last_reserved_source_alloc_id")
  let next_source_alloc_id ← required s.next_source_alloc_id (path ++ ".next_source_alloc_id")
  let final_sentinel_source_alloc_id ← required s.final_sentinel_source_alloc_id (path ++ ".final_sentinel_source_alloc_id")
  for value in [last_reserved_source_alloc_id, next_source_alloc_id, final_sentinel_source_alloc_id] do
    unless value > 0 && value < 2^64 do fail s!"{path}: expected nonzero u64"
  return (last_reserved_source_alloc_id, next_source_alloc_id, final_sentinel_source_alloc_id)

private def completeKeyFamily : Parser SourceAllocIdDedupKind := do
  unless (← string) == "byte_memory" do fail "only byte_memory complete key family is supported"
  pure .bytes
private def nonExhaustiveKeyFamily : Parser SourceAllocIdDedupKind := do
  liftExcept (parseSourceAllocIdDedupKind (← string) "$compiler_alloc_id_world.non_exhaustive_key_families")

private structure ParseCompilerAllocIdWorldFields where
  schema : Option (String) := none
  profile : Option (String) := none
  frontier : Option (Nat × Nat × Nat) := none
  global_pool_complete_through : Option (Nat) := none
  raw_pool : Option (Array SourceAllocIdPoolRow) := none
  dedup_catalog : Option (Array SourceAllocIdDedupRow) := none
  complete_key_families : Option (Array SourceAllocIdDedupKind) := none
  non_exhaustive_key_families : Option (Array SourceAllocIdDedupKind) := none

def parseCompilerAllocIdWorld (path : String := "$.compiler_alloc_id_world") : Parser (CompilerAllocIdWorld) := do
  let s ← object (ParseCompilerAllocIdWorldFields.mk none none none none none none none none) fun s key => do
    match key with
    | "schema" => return { s with schema := some (← string) }
    | "profile" => return { s with profile := some (← string) }
    | "frontier" => return { s with frontier := some (← parseAllocFrontier (path ++ ".frontier")) }
    | "global_pool_complete_through" => return { s with global_pool_complete_through := some (← natural) }
    | "raw_pool" => return { s with raw_pool := some (← array (parseSourceAllocIdPoolRow (path ++ ".raw_pool"))) }
    | "dedup_catalog" => return { s with dedup_catalog := some (← array (parseSourceAllocIdDedupRow (path ++ ".dedup_catalog"))) }
    | "complete_key_families" => return { s with complete_key_families := some (← array completeKeyFamily) }
    | "non_exhaustive_key_families" => return { s with non_exhaustive_key_families := some (← array nonExhaustiveKeyFamily) }
    | _ => skipValue; pure s
  let schema ← required s.schema (path ++ ".schema")
  let profile ← required s.profile (path ++ ".profile")
  let frontier ← required s.frontier (path ++ ".frontier")
  let global_pool_complete_through ← required s.global_pool_complete_through (path ++ ".global_pool_complete_through")
  let raw_pool ← required s.raw_pool (path ++ ".raw_pool")
  let dedup_catalog ← required s.dedup_catalog (path ++ ".dedup_catalog")
  let complete_key_families ← required s.complete_key_families (path ++ ".complete_key_families")
  let non_exhaustive_key_families ← required s.non_exhaustive_key_families (path ++ ".non_exhaustive_key_families")
  unless schema == "rustc_alloc_id_world_v1" do fail s!"{path}.schema: unsupported source AllocId world schema"
  unless profile == "prepared_post_export" do fail s!"{path}.profile: unsupported source AllocId world profile"
  unless global_pool_complete_through == frontier.1 do fail s!"{path}.global_pool_complete_through: does not equal frontier"
  return ⟨UInt64.ofNat frontier.1, UInt64.ofNat frontier.2.1, UInt64.ofNat frontier.2.2,
    raw_pool, dedup_catalog, complete_key_families, non_exhaustive_key_families⟩

private structure ParsePromotedBodyFields where
  promoted_index : Option (Option Nat) := none
  body : Option (Option Nat) := none

private def parsePromotedBody (path : String) (index : Nat) : Parser (PromotedBody) := do
  let s ← object (ParsePromotedBodyFields.mk none none) fun s key => do
    match key with
    | "promoted_index" => return { s with promoted_index := some (← nullable natural) }
    | "body" => return { s with body := some (← nullable natural) }
    | _ => skipValue; pure s
  let promoted_index ← pure (s.promoted_index.getD none)
  let body ← pure (s.body.getD none)
  return ⟨promoted_index.getD index, body⟩

def parsePromotedBodies (path : String) : Parser (Array PromotedBody) := arrayIndexed (parsePromotedBody path)

private structure ParseBodyRootFields where
  body : Option (Nat) := none
  entry_instance : Option (Nat) := none
  def_id : Option (Nat) := none
  def_path : Option (String) := none
  is_static : Option (Bool) := none
  thread_local_static : Option (Bool) := none
  promoted_bodies : Option (Array PromotedBody) := none

def parseBodyRoot (path : String) : Parser (BodyRoot) := do
  let s ← object (ParseBodyRootFields.mk none none none none none none none) fun s key => do
    match key with
    | "body" => return { s with body := some (← natural) }
    | "entry_instance" => return { s with entry_instance := some (← natural) }
    | "def_id" => return { s with def_id := some (← natural) }
    | "def_path" => return { s with def_path := some (← string) }
    | "is_static" => return { s with is_static := some (← boolean) }
    | "thread_local_static" => return { s with thread_local_static := some (← boolean) }
    | "promoted_bodies" => return { s with promoted_bodies := some (← parsePromotedBodies (path ++ ".promoted_bodies")) }
    | _ => skipValue; pure s
  let body ← required s.body (path ++ ".body")
  let entry_instance ← required s.entry_instance (path ++ ".entry_instance")
  let def_id ← required s.def_id (path ++ ".def_id")
  let def_path ← required s.def_path (path ++ ".def_path")
  let is_static ← required s.is_static (path ++ ".is_static")
  let thread_local_static ← required s.thread_local_static (path ++ ".thread_local_static")
  let promoted_bodies ← pure (s.promoted_bodies.getD  #[])
  return ⟨body, entry_instance, def_id, def_path, is_static, thread_local_static, promoted_bodies⟩

private structure ParseVirtualIdentityFields where
  function_type : Option (Nat) := none
  fn_abi : Option (Nat) := none

private def parseVirtualIdentity (path : String) : Parser (Nat × Nat) := do
  let s ← object (ParseVirtualIdentityFields.mk none none) fun s key => do
    match key with
    | "function_type" => return { s with function_type := some (← natural) }
    | "fn_abi" => return { s with fn_abi := some (← natural) }
    | _ => skipValue; pure s
  let function_type ← required s.function_type (path ++ ".function_type")
  let fn_abi ← required s.fn_abi (path ++ ".fn_abi")
  return (function_type, fn_abi)

private structure ParseInstanceFields where
  kind : Option (String) := none
  instance_id : Option (Nat) := none
  instance_kind : Option (Miri.Interpreter.CallInstanceKind) := none
  generic_args : Option (Array Miri.MIR.GenericArg) := none
  def_path : Option (Option String) := none
  def_id : Option (Option Nat) := none
  body : Option (Option Nat) := none
  dispatch_slot : Option (Option Nat) := none
  body_status : Option (Option String) := none
  virtual_identity : Option (Option (Nat × Nat)) := none
  foreign_item : Option (Option Bool) := none
  symbol_name : Option (Option String) := none
  fallback_instance : Option (Option Nat) := none
  promoted_bodies : Option (Array PromotedBody) := none

def parseInstance (path : String) : Parser (InstanceNode) := do
  let s ← object ({} : ParseInstanceFields) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "instance_id" => return { s with instance_id := some (← natural) }
    | "instance_kind" => return { s with instance_kind := some (← InstanceKindCodec.decode) }
    | "generic_args" => return { s with generic_args := some (← GenericArgsCodec.decode) }
    | "def_path" => return { s with def_path := some (← nullable (string)) }
    | "def_id" => return { s with def_id := some (← nullable (natural)) }
    | "body" => return { s with body := some (← nullable (natural)) }
    | "dispatch_slot" => return { s with dispatch_slot := some (← nullable (natural)) }
    | "body_status" => return { s with body_status := some (← nullable (string)) }
    | "virtual_identity" => return { s with virtual_identity := some (← nullable (parseVirtualIdentity (path ++ ".virtual_identity"))) }
    | "foreign_item" => return { s with foreign_item := some (← nullable (boolean)) }
    | "symbol_name" => return { s with symbol_name := some (← nullable (string)) }
    | "fallback_instance" => return { s with fallback_instance := some (← nullable (natural)) }
    | "promoted_bodies" => return { s with promoted_bodies := some (← parsePromotedBodies (path ++ ".promoted_bodies")) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let instance_id ← required s.instance_id (path ++ ".instance_id")
  let instance_kind ← required s.instance_kind (path ++ ".instance_kind")
  let generic_args ← required s.generic_args (path ++ ".generic_args")
  let def_path ← pure (s.def_path.getD none)
  let def_id ← pure (s.def_id.getD none)
  let body ← pure (s.body.getD none)
  let dispatch_slot ← pure (s.dispatch_slot.getD none)
  let body_status ← pure (s.body_status.getD none)
  let virtual_identity ← pure (s.virtual_identity.getD none)
  let foreign_item ← pure (s.foreign_item.getD none)
  let symbol_name ← pure (s.symbol_name.getD none)
  let fallback_instance ← pure (s.fallback_instance.getD none)
  let promoted_bodies ← pure (s.promoted_bodies.getD  #[])
  let kind ← match kind with
    | "instance_mir" => pure InstanceKind.instanceMir
    | "intrinsic_dispatch" => pure .intrinsicDispatch
    | "foreign_item_no_mir" => pure .foreignItemNoMir
    | "virtual_dispatch_target" => pure .virtualDispatchTarget
    | "identity_only" => pure .identityOnly
    | other => fail s!"{path}.kind: unrecognized instance kind `{other}`"
  let node : InstanceNode := {
    instanceKind := instance_kind, genericArgs := generic_args, id := instance_id, kind := kind,
    defPath := def_path, definitionId := def_id,
    bodyId := body, promotedBodies := promoted_bodies, dispatchSlot := dispatch_slot,
    bodyStatus := body_status, virtualIdentity := virtual_identity, foreignItem := foreign_item,
    symbolName := symbol_name, fallbackInstance := fallback_instance}
  liftExcept (LocalValidation.validateInstance node)
  pure node

private structure ParseArgumentExtensionFields where
  kind : Option (String) := none

def parseArgumentExtension (path : String) : Parser (ArgumentExtensionKind) := do
  let s ← object (ParseArgumentExtensionFields.mk none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  match kind with
  | "none" => pure .none
  | "zero_extend" => pure .zeroExtend
  | "sign_extend" => pure .signExtend
  | _ => fail s!"{path}: unknown ArgumentExtensionKind"

private structure ParseArgumentCaptureFields where
  kind : Option (String) := none

def parseArgumentCapture (path : String) : Parser (ArgumentCaptureKind) := do
  let s ← object (ParseArgumentCaptureFields.mk none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  match kind with
  | "none" => pure .none
  | "address" => pure .address
  | "read_only" => pure .readOnly
  | "unrestricted" => pure .unrestricted
  | _ => fail s!"{path}: unknown ArgumentCaptureKind"

private structure ParseIndirectModeFields where
  kind : Option (String) := none

def parseIndirectMode (path : String) : Parser (IndirectModeKind) := do
  let s ← object (ParseIndirectModeFields.mk none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  match kind with
  | "pointer" => pure .pointer
  | "on_stack" => pure .onStack
  | "amdgpu_kernel_argument" => pure .amdgpuKernelArgument
  | _ => fail s!"{path}: unknown IndirectModeKind"

private structure ParseAbiAttributesFields where
  no_alias : Option (Bool) := none
  no_free : Option (Bool) := none
  no_undef : Option (Bool) := none
  non_null : Option (Bool) := none
  read_only : Option (Bool) := none
  writable : Option (Bool) := none
  in_register : Option (Bool) := none
  regular_bits : Option (Nat) := none
  pointee_size_bytes : Option (Nat) := none
  pointee_align_bytes : Option (Option Nat) := none
  arg_extension : Option (ArgumentExtensionKind) := none
  captures : Option (ArgumentCaptureKind) := none

def parseAbiAttributes (path : String) : Parser (AbiAttributes) := do
  let s ← object (ParseAbiAttributesFields.mk none none none none none none none none none none none none) fun s key => do
    match key with
    | "no_alias" => return { s with no_alias := some (← boolean) }
    | "no_free" => return { s with no_free := some (← boolean) }
    | "no_undef" => return { s with no_undef := some (← boolean) }
    | "non_null" => return { s with non_null := some (← boolean) }
    | "read_only" => return { s with read_only := some (← boolean) }
    | "writable" => return { s with writable := some (← boolean) }
    | "in_register" => return { s with in_register := some (← boolean) }
    | "regular_bits" => return { s with regular_bits := some (← natural) }
    | "pointee_size_bytes" => return { s with pointee_size_bytes := some (← natural) }
    | "pointee_align_bytes" => return { s with pointee_align_bytes := some (← nullable natural) }
    | "arg_extension" => return { s with arg_extension := some (← parseArgumentExtension (path ++ ".arg_extension")) }
    | "captures" => return { s with captures := some (← parseArgumentCapture (path ++ ".captures")) }
    | _ => skipValue; pure s
  let no_alias ← required s.no_alias (path ++ ".no_alias")
  let no_free ← required s.no_free (path ++ ".no_free")
  let no_undef ← required s.no_undef (path ++ ".no_undef")
  let non_null ← required s.non_null (path ++ ".non_null")
  let read_only ← required s.read_only (path ++ ".read_only")
  let writable ← required s.writable (path ++ ".writable")
  let in_register ← required s.in_register (path ++ ".in_register")
  let regular_bits ← required s.regular_bits (path ++ ".regular_bits")
  let pointee_size_bytes ← required s.pointee_size_bytes (path ++ ".pointee_size_bytes")
  let pointee_align_bytes ← pure (s.pointee_align_bytes.getD none)
  let arg_extension ← required s.arg_extension (path ++ ".arg_extension")
  let captures ← required s.captures (path ++ ".captures")
  return ⟨no_alias, no_free, no_undef, non_null, read_only, writable, in_register, regular_bits, pointee_size_bytes, pointee_align_bytes, arg_extension, captures⟩

private structure ParseCanonicalAbiFields where
  kind : Option (String) := none
  arm_call : Option (Option String) := none
  interrupt_kind : Option (Option String) := none
  x86_call : Option (Option String) := none

def parseCanonicalAbi (path : String) : Parser (CanonicalAbi) := do
  let s ← object (ParseCanonicalAbiFields.mk none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "arm_call" => return { s with arm_call := some (← nullable string) }
    | "interrupt_kind" => return { s with interrupt_kind := some (← nullable string) }
    | "x86_call" => return { s with x86_call := some (← nullable string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let arm_call ← pure (s.arm_call.getD none)
  let interrupt_kind ← pure (s.interrupt_kind.getD none)
  let x86_call ← pure (s.x86_call.getD none)
  let allowed : List String := match kind with
    | "arm" => ["arm_call"]
    | "interrupt" => ["interrupt_kind"]
    | "x86" => ["x86_call"]
    | _ => []
  if s.arm_call.isSome && !(allowed.contains "arm_call") then fail s!"{path}: field `arm_call` is incompatible with the selected variant"
  if s.interrupt_kind.isSome && !(allowed.contains "interrupt_kind") then fail s!"{path}: field `interrupt_kind` is incompatible with the selected variant"
  if s.x86_call.isSome && !(allowed.contains "x86_call") then fail s!"{path}: field `x86_call` is incompatible with the selected variant"
  if kind == "arm" then let _ ← required arm_call "arm_call"; pure ()
  if kind == "interrupt" then let _ ← required interrupt_kind "interrupt_kind"; pure ()
  if kind == "x86" then let _ ← required x86_call "x86_call"; pure ()
  return ⟨← liftExcept (canonicalAbiKind kind), ← liftExcept (arm_call.mapM armCallKind),
    ← liftExcept (interrupt_kind.mapM interruptCallKind), ← liftExcept (x86_call.mapM x86CallKind)⟩

private structure ParseAbiRegisterHintFields where
  kind : Option (String) := none
  integer_kind : Option (Option String) := none
  signed : Option (Option Bool) := none
  float_kind : Option (Option String) := none
  address_space : Option (Option Nat) := none

def parseAbiRegisterHint (path : String) : Parser (AbiRegisterHint) := do
  let s ← object (ParseAbiRegisterHintFields.mk none none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "integer_kind" => return { s with integer_kind := some (← nullable string) }
    | "signed" => return { s with signed := some (← nullable boolean) }
    | "float_kind" => return { s with float_kind := some (← nullable string) }
    | "address_space" => return { s with address_space := some (← nullable natural) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let integer_kind ← pure (s.integer_kind.getD none)
  let signed ← pure (s.signed.getD none)
  let float_kind ← pure (s.float_kind.getD none)
  let address_space ← pure (s.address_space.getD none)
  let allowed : List String := match kind with
    | "integer" => ["integer_kind", "signed"]
    | "float" => ["float_kind"]
    | "pointer" => ["address_space"]
    | _ => []
  if s.integer_kind.isSome && !(allowed.contains "integer_kind") then fail s!"{path}: field `integer_kind` is incompatible with the selected variant"
  if s.signed.isSome && !(allowed.contains "signed") then fail s!"{path}: field `signed` is incompatible with the selected variant"
  if s.float_kind.isSome && !(allowed.contains "float_kind") then fail s!"{path}: field `float_kind` is incompatible with the selected variant"
  if s.address_space.isSome && !(allowed.contains "address_space") then fail s!"{path}: field `address_space` is incompatible with the selected variant"
  match kind with
  | "integer" => return .integer (← liftExcept (integerTypeTag (← required integer_kind "integer_kind"))) (← required signed "signed")
  | "float" => return .float (← liftExcept (floatTypeTag (← required float_kind "float_kind")))
  | "pointer" => return .pointer (← required address_space "address_space")
  | _ => fail s!"{path}: unrecognized register primitive hint"

private structure ParseAbiRegisterKindFields where
  kind : Option (String) := none
  hint_element : Option (Option AbiRegisterHint) := none

private def parseAbiRegisterKind (path : String) : Parser (AbiRegisterKind × Option AbiRegisterHint) := do
  let s ← object (ParseAbiRegisterKindFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "hint_element" => return { s with hint_element := some (← nullable (parseAbiRegisterHint (path ++ ".hint_element"))) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let hint_element ← pure (s.hint_element.getD none)
  if kind == "vector" then
    let _ ← required hint_element "hint_element"
    pure ()
  else if s.hint_element.isSome then
    fail s!"{path}: hint_element belongs only to vector registers"
  return (← liftExcept (abiRegisterKind kind), hint_element)

private structure ParseAbiRegisterFields where
  kind : Option (AbiRegisterKind × Option AbiRegisterHint) := none
  size_bits : Option (Nat) := none

def parseAbiRegister (path : String) : Parser (AbiRegister) := do
  let s ← object (ParseAbiRegisterFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← parseAbiRegisterKind (path ++ ".kind")) }
    | "size_bits" => return { s with size_bits := some (← natural) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let size_bits ← required s.size_bits (path ++ ".size_bits")
  return ⟨kind.1, size_bits, kind.2⟩

private structure ParseAbiCastTargetFields where
  prefix_registers : Option (Array AbiRegister) := none
  rest_offset_bytes : Option (Option Nat) := none
  rest_register : Option (AbiRegister) := none
  rest_total_bytes : Option (Nat) := none
  rest_is_consecutive : Option (Bool) := none
  attributes : Option (AbiAttributes) := none

def parseAbiCastTarget (path : String) : Parser (AbiCastTarget) := do
  let s ← object (ParseAbiCastTargetFields.mk none none none none none none) fun s key => do
    match key with
    | "prefix_registers" => return { s with prefix_registers := some (← array (parseAbiRegister (path ++ ".prefix_registers"))) }
    | "rest_offset_bytes" => return { s with rest_offset_bytes := some (← nullable natural) }
    | "rest_register" => return { s with rest_register := some (← parseAbiRegister (path ++ ".rest_register")) }
    | "rest_total_bytes" => return { s with rest_total_bytes := some (← natural) }
    | "rest_is_consecutive" => return { s with rest_is_consecutive := some (← boolean) }
    | "attributes" => return { s with attributes := some (← parseAbiAttributes (path ++ ".attributes")) }
    | _ => skipValue; pure s
  let prefix_registers ← required s.prefix_registers (path ++ ".prefix_registers")
  let rest_offset_bytes ← pure (s.rest_offset_bytes.getD none)
  let rest_register ← required s.rest_register (path ++ ".rest_register")
  let rest_total_bytes ← required s.rest_total_bytes (path ++ ".rest_total_bytes")
  let rest_is_consecutive ← required s.rest_is_consecutive (path ++ ".rest_is_consecutive")
  let attributes ← required s.attributes (path ++ ".attributes")
  return ⟨prefix_registers, rest_offset_bytes, rest_register, rest_total_bytes, rest_is_consecutive, attributes⟩

private structure ParseAbiPassModeFields where
  kind : Option (String) := none
  attributes : Option (Option AbiAttributes) := none
  first : Option (Option AbiAttributes) := none
  second : Option (Option AbiAttributes) := none
  metadata_attributes : Option (Option AbiAttributes) := none
  target : Option (Option AbiCastTarget) := none
  mode : Option (Option IndirectModeKind) := none
  pad_i32_count : Option (Option Nat) := none
  address_space : Option (Option Nat) := none

def parseAbiPassMode (path : String) : Parser (AbiPassMode) := do
  let s ← object (ParseAbiPassModeFields.mk none none none none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "attributes" => return { s with attributes := some (← nullable (parseAbiAttributes (path ++ ".attributes"))) }
    | "first" => return { s with first := some (← nullable (parseAbiAttributes (path ++ ".first"))) }
    | "second" => return { s with second := some (← nullable (parseAbiAttributes (path ++ ".second"))) }
    | "metadata_attributes" => return { s with metadata_attributes := some (← nullable (parseAbiAttributes (path ++ ".metadata_attributes"))) }
    | "target" => return { s with target := some (← nullable (parseAbiCastTarget (path ++ ".target"))) }
    | "mode" => return { s with mode := some (← nullable (parseIndirectMode (path ++ ".mode"))) }
    | "pad_i32_count" => return { s with pad_i32_count := some (← nullable natural) }
    | "address_space" => return { s with address_space := some (← nullable natural) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let attributes ← pure (s.attributes.getD none)
  let first ← pure (s.first.getD none)
  let second ← pure (s.second.getD none)
  let metadata_attributes ← pure (s.metadata_attributes.getD none)
  let target ← pure (s.target.getD none)
  let mode ← pure (s.mode.getD none)
  let pad_i32_count ← pure (s.pad_i32_count.getD none)
  let address_space ← pure (s.address_space.getD none)
  let kind ← liftExcept (passModeKind kind)
  let allowed : List String := match kind with
    | .ignore => []
    | .direct => ["attributes"]
    | .pair => ["first", "second"]
    | .cast => ["target", "pad_i32_count"]
    | .indirect => ["attributes", "address_space", "mode"]
    | .indirectUnsized => ["attributes", "metadata_attributes"]
  if s.attributes.isSome && !(allowed.contains "attributes") then fail s!"{path}: field `attributes` is incompatible with the selected variant"
  if s.first.isSome && !(allowed.contains "first") then fail s!"{path}: field `first` is incompatible with the selected variant"
  if s.second.isSome && !(allowed.contains "second") then fail s!"{path}: field `second` is incompatible with the selected variant"
  if s.metadata_attributes.isSome && !(allowed.contains "metadata_attributes") then fail s!"{path}: field `metadata_attributes` is incompatible with the selected variant"
  if s.target.isSome && !(allowed.contains "target") then fail s!"{path}: field `target` is incompatible with the selected variant"
  if s.mode.isSome && !(allowed.contains "mode") then fail s!"{path}: field `mode` is incompatible with the selected variant"
  if s.pad_i32_count.isSome && !(allowed.contains "pad_i32_count") then fail s!"{path}: field `pad_i32_count` is incompatible with the selected variant"
  if s.address_space.isSome && !(allowed.contains "address_space") then fail s!"{path}: field `address_space` is incompatible with the selected variant"
  match kind with
  | .direct | .indirect => let _ ← required attributes "attributes"; pure ()
  | .pair => let _ ← required first "first"; let _ ← required second "second"; pure ()
  | .indirectUnsized => let _ ← required attributes "attributes"; let _ ← required metadata_attributes "metadata_attributes"; pure ()
  | _ => pure ()
  match kind with
  | .cast => unless target.isSome && pad_i32_count.isSome do fail s!"{path}: Cast pass mode is missing target/padding data"
  | .indirect => unless mode.isSome do fail s!"{path}: Indirect pass mode is missing its mode tag"
  | _ => pure ()
  return ⟨kind, #[attributes, first, second, metadata_attributes].filterMap id, target, pad_i32_count, address_space, mode⟩

private structure ParseAbiArgumentFields where
  type : Option (Nat) := none
  layout : Option (Nat) := none
  mode : Option (AbiPassMode) := none

def parseAbiArgument (path : String) : Parser (AbiArgument) := do
  let s ← object (ParseAbiArgumentFields.mk none none none) fun s key => do
    match key with
    | "type" => return { s with type := some (← natural) }
    | "layout" => return { s with layout := some (← natural) }
    | "mode" => return { s with mode := some (← parseAbiPassMode (path ++ ".mode")) }
    | _ => skipValue; pure s
  let type ← required s.type (path ++ ".type")
  let layout ← required s.layout (path ++ ".layout")
  let mode ← required s.mode (path ++ ".mode")
  return ⟨type, layout, mode⟩

private structure ParseFunctionAbiFields where
  arguments : Option (Array AbiArgument) := none
  returnValue : Option (AbiArgument) := none
  calling_convention : Option (CanonicalAbi) := none
  can_unwind : Option (Bool) := none
  c_variadic : Option (Bool) := none
  fixed_count : Option (Nat) := none

def parseFunctionAbi (path : String) : Parser (FunctionAbi) := do
  let s ← object (ParseFunctionAbiFields.mk none none none none none none) fun s key => do
    match key with
    | "arguments" => return { s with arguments := some (← array (parseAbiArgument (path ++ ".arguments"))) }
    | "return" => return { s with returnValue := some (← parseAbiArgument (path ++ ".return")) }
    | "calling_convention" => return { s with calling_convention := some (← parseCanonicalAbi (path ++ ".calling_convention")) }
    | "can_unwind" => return { s with can_unwind := some (← boolean) }
    | "c_variadic" => return { s with c_variadic := some (← boolean) }
    | "fixed_count" => return { s with fixed_count := some (← natural) }
    | _ => skipValue; pure s
  let arguments ← required s.arguments (path ++ ".arguments")
  let returnValue ← required s.returnValue (path ++ ".returnValue")
  let calling_convention ← required s.calling_convention (path ++ ".calling_convention")
  let can_unwind ← required s.can_unwind (path ++ ".can_unwind")
  let c_variadic ← required s.c_variadic (path ++ ".c_variadic")
  let fixed_count ← required s.fixed_count (path ++ ".fixed_count")
  return ⟨arguments, returnValue, calling_convention, can_unwind, c_variadic, fixed_count⟩

def decodeCompilerLayout : Parser Layout := parseLayout "$.compiler_projection_layout"
def decodeCompilerFunctionAbi : Parser FunctionAbi := parseFunctionAbi "$.compiler_fn_abi"
end Miri.Input.DecoderValues
