import Lean.Data.Json.Printer
import Lean.Data.Json.Parser

/-! Test-only JSON rewriting helpers. Production decoding never imports this module. -/
namespace Miri.Input.JsonFixtures

structure Value where
  json : Lean.Json

def parse (text : String) : Except String Value := Value.mk <$> Lean.Json.parse text

def Value.text (value : Value) : String := value.json.compress

def Value.array (value : Value) : Except String (Array Value) :=
  (value.json.getArr?).map (·.map Value.mk)

def Value.object (value : Value) : Except String (Array (String × Value)) := do
  let fields ← value.json.getObj?
  return fields.toArray.map fun (key, item) => (key, ⟨item⟩)

def Value.field (value : Value) (key : String) : Except String Value :=
  Value.mk <$> value.json.getObjVal? key

def Value.natural (value : Value) : Except String Nat := value.json.getNat?

def Value.string (value : Value) : Except String String := value.json.getStr?

end Miri.Input.JsonFixtures
