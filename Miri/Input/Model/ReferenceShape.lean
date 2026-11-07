import Std

namespace Miri.Input

structure ProgramShape where
  types : Nat
  allocations : Nat
  instances : Nat
  deriving DecidableEq, BEq, Hashable, Repr

structure BodyShape where
  locals : Nat
  blocks : Nat
  deriving DecidableEq, BEq, Hashable, Repr

inductive ReferenceKind where
  | type | allocation | instance | local | block
  deriving DecidableEq, BEq, Hashable, Repr

inductive ReferenceContext where
  | raw
  | checked (program : ProgramShape) (body : BodyShape)
  deriving DecidableEq, BEq, Hashable, Repr

namespace ReferenceContext

def bound (program : ProgramShape) (body : BodyShape) : ReferenceKind → Nat
  | .type => program.types
  | .allocation => program.allocations
  | .instance => program.instances
  | .local => body.locals
  | .block => body.blocks

abbrev Ref (context : ReferenceContext) (kind : ReferenceKind) : Type :=
  match context with
  | .raw => Nat
  | .checked program body => Fin (bound program body kind)

instance (context : ReferenceContext) (kind : ReferenceKind) : BEq (Ref context kind) :=
  match context with
  | .raw => inferInstanceAs (BEq Nat)
  | .checked _ _ => inferInstanceAs (BEq (Fin _))

instance (context : ReferenceContext) (kind : ReferenceKind) : Repr (Ref context kind) :=
  match context with
  | .raw => inferInstanceAs (Repr Nat)
  | .checked _ _ => inferInstanceAs (Repr (Fin _))

def toNat {context : ReferenceContext} {kind : ReferenceKind} (reference : Ref context kind) : Nat :=
  match context with
  | .raw => reference
  | .checked _ _ => reference.val

@[simp] theorem toNat_checked (reference : Fin (bound program body kind)) :
    toNat (context := .checked program body) (kind := kind) reference = reference.val := rfl

theorem toNat_lt (reference : Ref (.checked program body) kind) :
    toNat reference < bound program body kind := reference.isLt

def Aligned (context : ReferenceContext) (locals blocks : Nat) : Prop :=
  match context with
  | .raw => True
  | .checked _ body => locals = body.locals ∧ blocks = body.blocks

abbrev Resolver (context : ReferenceContext) :=
  (kind : ReferenceKind) → Nat → Except String (context.Ref kind)

def rawResolver : Resolver .raw := fun _ id => .ok id

end ReferenceContext
end Miri.Input
