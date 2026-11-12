import Miri.Input.TypeArenaWorld

/-! Independent prototype for execution-owned instance syntax interning.
It is not connected to SourceCall: canonical identity alone does not establish
body, ABI, transfer or intrinsic capabilities. The composite below owns exactly
one type universe and one instance store; neither stores compiler query answers.
-/
namespace Miri.Input.InstanceArena
open Miri.Interpreter GenericSubstitution

structure Key where
  kind : CallInstanceKind
  definition : DefinitionIdentity
  arguments : Array MIR.GenericArg
  deriving Repr, DecidableEq

private def validateArguments (types : TypeArena.World) (arguments : Array MIR.GenericArg) : Except String Unit := do
  for argument in arguments do
    match argument with
    | .Type id => let _ ← types.lookupType id; pure ()
    | .Const id => let _ ← types.lookupConstant id; pure ()
    | .Lifetime region =>
      match region with
      | .Bound _ _ (.Named id) | .Placeholder _ _ (.Named id) => let _ ← types.identity id; pure ()
      | .LateParameter scope kind =>
        let _ ← types.identity scope
        if let .Named id := kind then let _ ← types.identity id; pure ()
      | .Error => throw "instance syntax contains an error region"
      | _ => pure ()

private def validateKind (types : TypeArena.World) (kind : CallInstanceKind) : Except String Unit := do
  let _ ← types.identity kind.defId
  let mut children : Array TypeId := #[]
  if let .Shim shim := kind then
    match shim with
    | .ClosureOnce _ closure _ => let _ ← types.identity closure; pure ()
    | .FnPtr _ ty | .Clone _ ty | .FnPtrAsPtr _ ty | .FnPtrFromPtr _ ty
    | .AsyncDropGlueCtor _ ty | .AsyncDropGlue _ ty => children := #[ty]
    | .FutureDropPoll _ proxy impl => children := #[proxy,impl]
    | .DropGlue _ ty => children := ty.toArray
    | _ => pure ()
  for child in children do let _ ← types.lookupType child; pure ()

def Key.ofSource (types : TypeArena.World) (kind : CallInstanceKind)
    (arguments : Array MIR.GenericArg) : Except String Key := do
  validateKind types kind
  validateArguments types arguments
  pure ⟨kind,← types.identity kind.defId,arguments⟩

def Key.item (types : TypeArena.World) (definition : DefinitionIdentity)
    (arguments : Array MIR.GenericArg) : Except String Key := do
  Key.ofSource types (.Item (← types.definitionRef definition)) arguments

structure Store where
  private mk ::
  material : Array Key
  constructed : Array Key := #[]
  deriving Repr, DecidableEq

inductive View where
  | material (key : Key)
  | constructed (key : Key)

def Store.ofSource (types : TypeArena.World) (source : Array InstanceNode) : Except String Store := do
  let material ← source.zipIdx.mapM fun (node,index) => do
    unless node.id == index do throw "instance material ID/index mismatch"
    Key.ofSource types node.instanceKind node.genericArgs
  pure ⟨material,#[]⟩

def Store.count (store : Store) : Nat := store.material.size + store.constructed.size

def Store.lookup (store : Store) (id : InstanceId) : Except String View :=
  if id < store.material.size then
    match store.material[id]? with
    | some value => pure (.material value) | none => .error "material instance is absent"
  else match store.constructed[id - store.material.size]? with
    | some value => pure (.constructed value) | none => .error "constructed instance is absent"

private def Store.append (store : Store) (key : Key) : InstanceId × Store :=
  (store.count,{store with constructed := store.constructed.push key})

/-- Every payload, including shim kind/extra definition/type and all generic
arguments, participates in identity. Source display paths never select a key. -/
def Store.intern (types : TypeArena.World) (store : Store) (key : Key) : Except String (InstanceId × Store) := do
  let verified ← Key.ofSource types key.kind key.arguments
  unless verified == key do throw "instance key physical definition does not match its kind"
  let mut found := none
  for (candidate,index) in store.material.zipIdx do
    if candidate == key then
      unless found.isNone do throw "ambiguous canonical material instance identity"
      found := some index
  for (candidate,index) in store.constructed.zipIdx do
    if candidate == key then
      unless found.isNone do throw "duplicate canonical instance constructor"
      found := some (store.material.size + index)
  if let some id := found then pure (id,store)
  else pure (store.append key)

theorem Store.append_dense (store : Store) (key : Key) :
    (store.append key).1 = store.material.size + store.constructed.size := rfl

theorem Store.append_material_preserved (store : Store) (key : Key) :
    (store.append key).2.material = store.material := rfl

theorem Store.append_lookup (store : Store) (key : Key) :
    (store.append key).2.lookup (store.append key).1 = .ok (.constructed key) := by
  simp [Store.append, Store.lookup, Store.count,
    Nat.not_lt.mpr (Nat.le_add_right store.material.size store.constructed.size), pure, Except.pure]

end Miri.Input.InstanceArena
