import Miri.Input.CompilerInitialAllocationSnapshot

namespace Miri.Input.CompilerInitialAllocation
open Lean Miri.Memory Miri.ABI GenericSubstitution
set_option autoImplicit false
variable {P E K : Type}
private def fields (j : Json) (expected : List String) : Except String Unit := do
  let object ← j.getObj?
  unless object.toArray.size == expected.length do throw "snapshot field count differs"
  for (key, _) in object.toArray do
    unless expected.contains key do throw s!"unknown initial snapshot field {key}"
  for key in expected do let _ ← j.getObjVal? key; pure ()
private def field := Json.getObjVal?
private def nat (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def text (j : Json) (key : String) : Except String String := do (← field j key).getStr?
private def flag (j : Json) (key : String) : Except String Bool := do (← field j key).getBool?
private def array (j : Json) (key : String) : Except String (Array Json) := do (← field j key).getArr?
private def u64 (j : Json) : Except String UInt64 := do
  let n ← j.getNat?
  unless n < 18446744073709551616 do throw "snapshot integer exceeds u64"
  pure (UInt64.ofNat n)
private def word (j : Json) (key : String) : Except String UInt64 := do u64 (← field j key)

private def definition (j : Json) : Except String DefinitionIdentity := do
  fields j ["crate", "index"]
  pure ⟨(← word j "crate").toNat, (← word j "index").toNat⟩

private def sourceProvenance (frontier : UInt64) (j : Json) : Except String CtfeProvenance := do
  let raw ← word j "target_source_alloc_id"
  unless raw != 0 && raw < frontier && raw.toNat < 4611686018427387904 do
    throw "snapshot provenance target is outside reserved identity domain"
  let immutable ← flag j "immutable"
  let shared ← flag j "shared_reference"
  if immutable && !shared then throw "immutable CTFE provenance lacks shared bit"
  let some id := AllocId.ofUInt64 raw | throw "zero source allocation identity"
  (CtfeProvenance.fromParts (id,immutable,shared)).mapError (fun e => reprStr e)

private def mask (size : Nat) (j : Json) : Except String InitMask := do
  let len ← word j "len"
  unless len.toNat == size do throw "source InitMask logical length differs from backing allocation"
  match ← text j "kind" with
  | "lazy" =>
    fields j ["kind","len","state"]
    pure {blocks := .Lazy (← flag j "state"),len := Size.ofBytes len}
  | "materialized" =>
    fields j ["kind","len","blocks"]
    let blocks ← (← array j "blocks").mapM u64
    unless len.toNat ≤ blocks.size*64 do throw "source InitMask block capacity below logical length"
    -- Retain all words, including logical trailing bits and excess blocks.
    pure {blocks := .Materialized ⟨blocks⟩,len := Size.ofBytes len}
  | other => throw s!"unsupported source InitMask representation {other}"

private def memory (symbols : Symbols) (frontier : UInt64) (j : Json) : Except String MemoryKey := do
  fields j ["kind","size","alignment","mutable","bytes","initialized","pointer_bytes","little_endian","relocations","init_mask","provenance_fragments"]
  let size ← nat j "size"
  unless size < 18446744073709551616 do throw "snapshot backing length exceeds source Size"
  let alignment ← word j "alignment"
  unless alignment != 0 do throw "zero source allocation alignment"
  let _ ← (Align.fromBytes alignment).mapError toString
  let pointerBytes ← word j "pointer_bytes"
  unless [1,2,4,8].contains pointerBytes.toNat do throw "unsupported source pointer width"
  let readByte (byte : Json) : Except String UInt8 := do
    let n ← byte.getNat?
    unless n < 256 do throw "snapshot byte exceeds u8"
    pure (UInt8.ofNat n)
  let bytes ← (← array j "bytes").mapM readByte
  let initialized ← (← array j "initialized").mapM Json.getBool?
  unless size == bytes.size && size == initialized.size do throw "snapshot byte/init sizes differ"
  let initMask ← mask size (← field j "init_mask")
  for i in [:size] do
    let observed ← (initMask.get (Size.ofBytes (UInt64.ofNat i))).mapError toString
    unless observed == initialized[i]?.getD false do throw "source mask representation contradicts bit audit"
  let littleEndian ← flag j "little_endian"
  unless pointerBytes == symbols.pointerBytes && littleEndian == symbols.littleEndian do
    throw "allocation pointer layout contradicts the actual run target"
  let mut pointers := #[]
  let mut previousEnd := 0
  for row in ← array j "relocations" do
    fields row ["slot","target_source_alloc_id","target_offset","immutable","shared_reference"]
    let slot ← word row "slot"
    let provenance ← sourceProvenance frontier row
    let start := slot.toNat
    let finish := start + pointerBytes.toNat
    unless previousEnd ≤ start && finish ≤ size do throw "snapshot pointer overlap/out of bounds"
    for i in [start:finish] do
      unless initialized[i]?.getD false do throw "partial/uninitialized whole pointer"
    let digits ← text row "target_offset"
    let some offset := digits.toNat? | throw "invalid snapshot pointer offset"
    let mut stored := 0
    for i in [:pointerBytes.toNat] do
      let some byte := bytes[start+i]? | throw "snapshot pointer byte absent"
      if littleEndian then stored := stored + byte.toNat * 256^i
      else stored := stored*256 + byte.toNat
    unless stored == offset do throw "pointer offset contradicts stored bytes"
    pointers := pointers.push (Size.ofBytes slot,provenance)
    previousEnd := finish
  let rawFragments ← field j "provenance_fragments"
  let fragments : Option (Array (Size × PointerFrag CtfeProvenance)) ← if rawFragments == .null then pure none else do
    let mut fragments := #[]
    let mut previous : Option UInt64 := none
    for row in ← rawFragments.getArr? do
      fields row ["slot","index","target_source_alloc_id","immutable","shared_reference","bytes"]
      let slot ← word row "slot"
      unless slot.toNat < size && (previous.map (fun value => decide (value < slot))).getD true do
        throw "fragment offset invalid or noncanonical"
      let index ← nat row "index"
      unless index < 8 do throw "fragment index exceeds source eight-byte representation"
      let provenance ← sourceProvenance frontier row
      let stored ← (← array row "bytes").mapM readByte
      if h : stored.size = 8 then
        let fragment : PointerFrag CtfeProvenance := {idx := UInt8.ofNat index, prov := provenance, bytes := ⟨stored,h⟩}
        fragments := fragments.push (Size.ofBytes slot,fragment)
      else throw "fragment must preserve all eight stored bytes"
      previous := some slot
    -- Some(empty) is Eq-distinct from None and is not discarded.
    pure (some fragments)
  let provenance ← (ProvenanceMap.fromParts pointers fragments).mapError (fun e => reprStr e)
  let mutable ← flag j "mutable"
  let align ← (Align.fromBytes alignment).mapError toString
  let _ ← (Allocation.fromCompilerSnapshot bytes align (if mutable then .Mut else .Not)
    initMask provenance (Size.ofBytes pointerBytes)).mapError toString
  pure ⟨bytes,initMask,alignment,mutable,pointerBytes,littleEndian,provenance⟩

private def key (symbols : Symbols) (frontier : UInt64) (j : Json) : Except String GlobalKey := do
  match ← text j "kind" with
  | "memory" => pure (.memory (← memory symbols frontier j))
  | "static" => fields j ["kind","definition"]; pure (.static (← definition (← field j "definition")))
  | "function" => fields j ["kind","instance"]; pure (.function (← symbols.function (← field j "instance")))
  | "type_id" => fields j ["kind","type"]; pure (.typeId (← symbols.type (← field j "type")))
  | "vtable" =>
    fields j ["kind","type","predicates"]
    pure (.vtable (← symbols.type (← field j "type")) (← symbols.predicates (← field j "predicates")))
  | other => throw s!"unsupported initial global constructor {other}"

private def effects (j : Json) : Except String Effects := do
  fields j ["unchanged","before_next_source_alloc_id","after_next_source_alloc_id","added_global_source_ids","removed_global_source_ids","changed_global_source_ids","before_dedup_count","after_dedup_count","dedup_changed"]
  let beforeNext ← word j "before_next_source_alloc_id"
  let afterNext ← word j "after_next_source_alloc_id"
  unless beforeNext != 0 && beforeNext ≤ afterNext do throw "snapshot effect frontier reversed"
  let readIds (name : String) : Except String (Array UInt64) := do
    let ids ← (← array j name).mapM u64
    let mut seen : Array UInt64 := #[]
    for id in ids do
      unless id != 0 && id < afterNext && !seen.contains id do throw "invalid/duplicate effect identity"
      seen := seen.push id
    pure ids
  let added ← readIds "added_global_source_ids"
  let removed ← readIds "removed_global_source_ids"
  let changed ← readIds "changed_global_source_ids"
  let beforeDedup ← nat j "before_dedup_count"
  let afterDedup ← nat j "after_dedup_count"
  let dedupChanged ← flag j "dedup_changed"
  let unchanged ← flag j "unchanged"
  let actualChange := beforeNext != afterNext || beforeDedup != afterDedup || dedupChanged ||
    !added.isEmpty || !removed.isEmpty || !changed.isEmpty
  if unchanged == actualChange then throw "snapshot nonmutation flag contradicts effects"
  pure ⟨unchanged,beforeNext,afterNext,added,removed,changed,beforeDedup,afterDedup,dedupChanged⟩

private def staticSource (symbols : Symbols) (j : Json) : Except String StaticSource := do
  fields j ["source_type","declared_mutability","is_static","is_foreign_item","nested","thread_local","explicit_align_bytes"]
  let rawType ← field j "source_type"
  let type ← if rawType == .null then pure none else some <$> symbols.type rawType
  let nested ← flag j "nested"
  unless nested || type.isSome do throw "non-nested static source type absent"
  let rawAlign ← field j "explicit_align_bytes"
  let explicitAlignBytes ← if rawAlign == .null then pure none else do
    let align ← u64 rawAlign
    unless align != 0 do throw "zero explicit source alignment"
    let _ ← (Align.fromBytes align).mapError toString
    pure (some align)
  let mutable ← text j "declared_mutability"
  let mutability ← match mutable with
    | "mutable" => pure MemoryMutability.mutable
    | "immutable" => pure MemoryMutability.immutable
    | _ => throw "invalid static mutability"
  let isStatic ← flag j "is_static"
  let foreignItem ← flag j "is_foreign_item"
  let threadLocal ← flag j "thread_local"
  pure {type,explicitAlignBytes,mutability,nested,isStatic,foreignItem,threadLocal}
private def global (symbols : Symbols) (frontier : UInt64) (source : UInt64) (value : Json) : Except String Binding := do
  if (← text value "kind") == "static" then
    fields value ["kind","definition","static_info"]
    pure {source, key := .static (← definition (← field value "definition")), staticSource := some (← staticSource symbols (← field value "static_info"))}
  else pure {source, key := ← key symbols frontier value}

def decode (symbols : Symbols) (j : Json) : Except String Snapshot := do
  fields j ["schema","phase","next_source_alloc_id","global_count","dedup_count","globals","dedup","capture_to_serialization_effects","serialization_effects"]
  unless (← text j "schema") == "rustc_initial_global_snapshot_v1" &&
      (← text j "phase") == "before_export_queries" do throw "initial snapshot schema/phase mismatch"
  let next ← word j "next_source_alloc_id"
  unless next != 0 do throw "initial snapshot frontier is zero"
  let mut globals : Array Binding := #[]
  let mut previous : UInt64 := 0
  for row in ← array j "globals" do
    fields row ["source_alloc_id","value"]
    let source ← word row "source_alloc_id"
    unless previous < source && source < next do throw "duplicate/noncanonical/out-of-frontier initial global"
    globals := globals.push (← global symbols next source (← field row "value"))
    previous := source
  let mut dedup : Array DedupBinding := #[]
  for row in ← array j "dedup" do
    fields row ["key","salt","source_alloc_id"]
    let value ← key symbols next (← field row "key")
    let salt ← word row "salt"
    let source ← word row "source_alloc_id"
    if dedup.any (fun old => old.key == value && old.salt == salt) then throw "duplicate typed dedup key/salt"
    let some target := globals.find? (·.source == source) | throw "dedup target global absent"
    unless target.key == value do throw "dedup key differs from its actual global binding"
    dedup := dedup.push ⟨value,salt,source⟩
  unless globals.size == (← nat j "global_count") && dedup.size == (← nat j "dedup_count") do
    throw "snapshot global/dedup count mismatch"
  let captureEffects ← effects (← field j "capture_to_serialization_effects")
  let serializationEffects ← effects (← field j "serialization_effects")
  unless captureEffects.beforeNext == next && captureEffects.afterNext == serializationEffects.beforeNext do
    throw "snapshot serialization phase frontiers do not join"
  pure ⟨next,globals,dedup,captureEffects,serializationEffects⟩


def readSourceEffects (j : Json) : Except String Effects := effects j

def readSourceMemory (symbols : Symbols) (frontier : UInt64) (j : Json) : Except String MemoryKey := memory symbols frontier j

end Miri.Input.CompilerInitialAllocation
