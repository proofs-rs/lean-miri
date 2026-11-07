import Miri.Input.Reader.Catalog

/-! Reader-local field access. A catalog read observes just the requested node;
it does not construct a recursively resolved JSON document. The raw instance is
for standalone syntax observations, outside an imported transport catalog. -/
namespace Miri.Input.Reader
open Lean

class JsonFields where
  inspect : Json → Json

def rawJsonFields : JsonFields := ⟨id⟩

instance (priority := low) : JsonFields := rawJsonFields

def Catalog.jsonFields (catalog : Catalog) : JsonFields :=
  ⟨fun value => (catalog.inspect value "reader").toOption.getD value⟩

def inspectJson [JsonFields] (value : Json) : Json := JsonFields.inspect value

def jsonField? [JsonFields] (value : Json) (key : String) : Except String Json :=
  ((inspectJson value).getObjVal? key).map inspectJson

def jsonFieldAs? [JsonFields] (α : Type) [FromJson α] (value : Json) (key : String) : Except String α := do
  fromJson? (← jsonField? value key)

end Miri.Input.Reader
