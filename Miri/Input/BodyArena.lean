import Miri.Input.InstanceArena

/-! Raw body identity interning. A constructed entry identifies source syntax
and a complete instance; it never contains substituted MIR or an ABI result. -/
namespace Miri.Input.BodyArena

structure Key where
  templateId : Nat
  instanceId : InstanceId
  instanceKey : InstanceArena.Key
  promoted : Option Nat
  deriving Repr, DecidableEq

private def lookupInstanceKey (instances : InstanceArena.Store) (id : InstanceId) : Except String InstanceArena.Key := do
  match ← instances.lookup id with
  | .material key | .constructed key => pure key

def Key.create (types : TypeArena.World) (instances : InstanceArena.Store)
    (templates : Array CopyTemplateSource) (templateId instanceId : Nat)
    (promoted : Option Nat) : Except String Key := do
  let key ← lookupInstanceKey instances instanceId
  let .Item _ := key.kind | throw "raw template body requires an Item instance"
  let some source := templates[templateId]? | throw "raw body source template is absent"
  unless source.sourcePromoted == promoted do throw "raw body source promoted role mismatch"
  unless (← types.identity source.definitionId) == key.definition do
    throw "raw body source physical definition does not match its instance"
  unless source.template.parameters.size == key.arguments.size do
    throw "raw body source generic argument count mismatch"
  for (parameter,argument) in source.template.parameters.zip key.arguments do
    let sort := match argument with
      | .Type _ => GenericSubstitution.ArgSort.type
      | .Const _ => .constant | .Lifetime _ => .region
    unless parameter == sort do throw "raw body source generic argument sort mismatch"
  pure ⟨templateId,instanceId,key,promoted⟩

structure Store where
  private mk ::
  /-- Source namespace extent; raw body seeds remain in the immutable World metadata. -/
  materialCount : Nat
  constructed : Array Key := #[]
  deriving Repr, DecidableEq

inductive View where
  | material (index : Nat)
  | constructed (key : Key)

def Store.ofSource (bodies : Array BodySeed) : Store := ⟨bodies.size,#[]⟩
def Store.count (store : Store) : Nat := store.materialCount + store.constructed.size

def Store.lookup (store : Store) (id : BodyId) : Except String View :=
  if id < store.materialCount then .ok (.material id)
  else match store.constructed[id - store.materialCount]? with
    | some key => .ok (.constructed key) | none => .error "constructed body identity is absent"

private def Store.append (store : Store) (key : Key) : BodyId × Store :=
  (store.count,{store with constructed := store.constructed.push key})

def Store.intern (types : TypeArena.World) (instances : InstanceArena.Store)
    (templates : Array CopyTemplateSource) (sourceBodies : Array BodySeed) (store : Store) (key : Key) :
    Except String (BodyId × Store) := do
  let verified ← Key.create types instances templates key.templateId key.instanceId key.promoted
  unless verified == key do throw "raw body key contradicts the current instance universe"
  unless store.materialCount <= sourceBodies.size do throw "material body namespace exceeds source prefix"
  let mut found := none
  for index in [:store.materialCount] do
    let some seed := sourceBodies[index]? | throw "material body source is absent"
    let .copyTemplate reference := seed | continue
    let some source := templates[reference.templateId]? | throw "material body source template is absent"
    let candidate ← Key.create types instances templates reference.templateId reference.instanceId source.sourcePromoted
    unless reference.genericArgs == candidate.instanceKey.arguments do
      throw "material body source arguments contradict its complete instance"
    if candidate == key then
      unless found.isNone do throw "ambiguous canonical material body identity"
      found := some index
  for (candidate,index) in store.constructed.zipIdx do
    if candidate == key then
      unless found.isNone do throw "duplicate canonical constructed body identity"
      found := some (store.materialCount + index)
  if let some id := found then pure (id,store) else pure (store.append key)

theorem Store.append_dense (store : Store) (key : Key) :
    (store.append key).1 = store.materialCount + store.constructed.size := rfl

theorem Store.append_material_preserved (store : Store) (key : Key) :
    (store.append key).2.materialCount = store.materialCount := rfl

theorem Store.append_lookup (store : Store) (key : Key) :
    (store.append key).2.lookup (store.append key).1 = .ok (.constructed key) := by
  simp [Store.append, Store.lookup, Store.count,
    Nat.not_lt.mpr (Nat.le_add_right store.materialCount store.constructed.size)]

end Miri.Input.BodyArena
