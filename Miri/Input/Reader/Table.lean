import Miri.Input.Reader.Catalog
import Miri.MIR.Table

namespace Miri.Input.Reader
open Lean Miri.MIR

-- Reserving catalog slots avoids a separate ID remapping table.
def Catalog.readEntry (catalog : Catalog) (table : SharedTable α)
    (decode : Json → Except String α) (input : Json) (path : String) :
    Except String (Nat × SharedTable α) := do
  unless catalog.nodes.size <= table.size do throw s!"{path}: shared table is not initialized"
  match ← catalog.sharedId? input path with
  | none => return (table.size, table.push (some (← decode input)))
  | some id =>
    unless id < catalog.nodes.size do throw s!"{path}: invalid shared ID {id}"
    if bound : id < table.size then
      match table[id] with
      | some _ => return (id, table)
      | none =>
        let value ← decode (← catalog.inspect input path)
        return (id, table.set id (some value) bound)
    else throw s!"{path}: shared table size mismatch at ID {id}"

def Catalog.readCached (catalog : Catalog) (getTable : σ → SharedTable α)
    (putTable : σ → SharedTable α → σ) (decode : Json → String → StateT σ (Except String) α)
    (input : Json) (path : String) : StateT σ (Except String) Nat := do
  match ← catalog.sharedId? input path with
  | none =>
    let value ← decode input path
    let state ← get
    let table := getTable state
    set (putTable state (table.push (some value)))
    return table.size
  | some id =>
    unless id < catalog.nodes.size do throw s!"{path}: invalid shared ID {id}"
    let state ← get
    let some entry := (getTable state)[id]? | throw s!"{path}: table not initialized"
    if entry.isSome then return id
    let value ← decode (← catalog.inspect input path) path
    let state ← get
    let table := getTable state
    if bound : id < table.size then
      set (putTable state (table.set id (some value) bound))
      return id
    else throw s!"{path}: table not initialized"


end Miri.Input.Reader
