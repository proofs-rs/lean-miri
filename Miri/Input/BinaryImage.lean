import Lean

namespace Miri.Input.BinaryImage

structure Cursor where
  bytes : ByteArray
  position : Nat := 0

abbrev Reader := EStateM String Cursor

def magic : ByteArray := ⟨#[76,77,73,82,73,77,71,1]⟩

def readByte : Reader UInt8 := do
  let cursor ← get
  if h : cursor.position < cursor.bytes.size then
    let byte := cursor.bytes[cursor.position]
    set { cursor with position := cursor.position + 1 }
    return byte
  else throw "binary image: truncated byte"

/-- Canonical unsigned LEB128, bounded to u64, without per-byte parser states. -/
def readNat : Reader Nat := fun cursor => Id.run do
  let mut position := cursor.position
  let mut value := 0
  let mut factor := 1
  for index in [:10] do
    if h : position < cursor.bytes.size then
      let byte := cursor.bytes[position]
      let chunk := byte.toNat % 128
      if index == 9 && byte > 1 then return .error "binary image: integer overflows u64" cursor
      value := value + chunk * factor
      position := position + 1
      if byte < 128 then
        if index != 0 && chunk == 0 then return .error "binary image: noncanonical integer" cursor
        return .ok value { cursor with position }
      factor := factor * 128
    else return .error "binary image: truncated integer" cursor
  return .error "binary image: integer overflows u64" cursor

def readText : Reader String := do
  let count ← readNat
  let cursor ← get
  unless count ≤ cursor.bytes.size - cursor.position do throw "binary image: truncated string"
  let bytes := cursor.bytes.extract cursor.position (cursor.position + count)
  let some text := String.fromUTF8? bytes | throw "binary image: invalid UTF-8"
  set { cursor with position := cursor.position + count }
  return text

/-- Every row/field/edge needs at least one remaining byte. Do not allocate from
an unbounded declared count before checking it against the actual input. -/
def readCount : Reader Nat := do
  let count ← readNat
  let cursor ← get
  unless count ≤ cursor.bytes.size - cursor.position do throw "binary image: impossible item count"
  return count

def hasMagic (bytes : ByteArray) : Bool :=
  bytes.size ≥ magic.size && bytes.extract 0 magic.size == magic

end Miri.Input.BinaryImage
