import Miri.Input.LowerMIR

/-! Exact interner-index regressions: duplicate keys select the first stored
ID, coarse-key collisions still require full equality, and append-only updates
remain addressable by their original table index. -/
open Miri Miri.Input

theorem sourceSpanArrayIdxOfEqList (spans : Array SourceSpanData) (span : SourceSpanData) :
    spans.idxOf? span = spans.toList.idxOf? span := by
  simpa using (List.idxOf?_toArray span spans.toList)

#print axioms sourceSpanArrayIdxOfEqList

theorem definitionArrayIdxOfEqList (definitions : Array DefinitionId) (id : DefinitionId) :
    definitions.idxOf? id = definitions.toList.idxOf? id := by
  simpa using (List.idxOf?_toArray id definitions.toList)

#print axioms definitionArrayIdxOfEqList

private def spanA : SourceSpanData := {
  originalPayload := "a", lo := 3, hi := 8,
  start := ⟨1, 2⟩, «end» := ⟨1, 7⟩, context := "ctx-a", file := "src.rs" }

private def spanAOther : SourceSpanData := {
  originalPayload := "a", lo := 3, hi := 8,
  start := ⟨1, 2⟩, «end» := ⟨1, 7⟩, context := "ctx-b", file := "src.rs" }

private def spanB : SourceSpanData := {
  originalPayload := "b", lo := 9, hi := 11,
  start := ⟨2, 0⟩, «end» := ⟨2, 2⟩, context := "ctx-c", file := "src.rs" }

private def scanSequence (tables : CompilerTables) (values : Array TypedValue) :
    Except String (Array Nat × CompilerTables) := do
  let mut tables := tables
  let mut ids := #[]
  for value in values do
    let (span,next) ← lowerCompilerSpan tables value
    tables := next
    ids := ids.push span.id
  return (ids,tables)

private def indexedSequence (interner : CompilerSpanInterner) (values : Array TypedValue) :
    Except String (Array Nat × CompilerTables) := do
  let mut interner := interner
  let mut ids := #[]
  for value in values do
    let (span,next) ← lowerCompilerSpanWithInterner interner value
    interner := next
    ids := ids.push span.id
  return (ids,interner.getTables)

private def internCases : Bool := Id.run do
  let tables : CompilerTables := ⟨#[spanA, spanA], #[], #[]⟩
  let interner := CompilerSpanInterner.ofTables tables
  let .ok (first, interner) := lowerCompilerSpanWithInterner interner (.sourceSpan spanA)
    | return false
  let .ok (collision, interner) := lowerCompilerSpanWithInterner interner (.sourceSpan spanAOther)
    | return false
  if first.id != 0 || collision.id != 2 then return false
  let .ok (duplicate, interner) := lowerCompilerSpanWithInterner interner (.sourceSpan spanA)
    | return false
  if duplicate.id != first.id then return false
  let .ok (afterAppend, _) := lowerCompilerSpanWithInterner interner (.sourceSpan spanB)
    | return false
  if afterAppend.id != 3 then return false

  let sequence := #[TypedValue.sourceSpan spanAOther, .sourceSpan spanA,
    .sourceSpan spanB, .sourceSpan spanAOther]
  let scanned := scanSequence tables sequence
  let indexed := indexedSequence (CompilerSpanInterner.ofTables tables) sequence
  if scanned.toOption.map Prod.fst != indexed.toOption.map Prod.fst then return false
  match scanned, indexed with
  | .ok (_, scannedTables), .ok (_, indexedTables) =>
    if scannedTables.spans != indexedTables.spans then return false
    if scannedTables.definitions != indexedTables.definitions then return false
    if scannedTables.typeConstants != indexedTables.typeConstants then return false
  | _, _ => return false

  let invalid : TypedValue := .scalar .null
  let scanError := lowerCompilerSpan tables invalid
  let indexedError := lowerCompilerSpanWithInterner (CompilerSpanInterner.ofTables tables) invalid
  match scanError, indexedError with
  | .error scanMessage, .error indexedMessage =>
    if scanMessage != indexedMessage then return false
  | _, _ => return false

  -- Equal-sized replacements and reorderings must discard the old index.
  let indexedTables : CompilerTables := ⟨#[spanA, spanB], #[], #[]⟩
  let indexed := CompilerSpanInterner.ofTables indexedTables
  let reorderedTables : CompilerTables := ⟨#[spanB, spanA], #[], #[]⟩
  let reordered := indexed.rebind reorderedTables
  let .ok (reorderedA, reordered) := lowerCompilerSpanWithInterner reordered (.sourceSpan spanA)
    | return false
  if reorderedA.id != 1 || reordered.getTables.spans != reorderedTables.spans then return false
  let replacementTables : CompilerTables := ⟨#[spanAOther, spanB], #[], #[]⟩
  let replacement := indexed.rebind replacementTables
  let .ok (replacementA, replacement) := lowerCompilerSpanWithInterner replacement (.sourceSpan spanA)
    | return false
  if replacementA.id != 2 || replacement.getTables.spans.size != 3 then return false
  return tables.spans == #[spanA, spanA] && tables.spans.size == 2

def main : IO Unit := do
  unless internCases do throw (IO.userError "compiler span interner sequence mismatch")
  IO.println "compiler span interner sequence and error cases passed"
