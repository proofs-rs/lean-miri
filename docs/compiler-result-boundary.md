# Compiler result boundary

An export is tied to one pinned rustc invocation. The exporter serializes MIR,
identity tables and the concrete results of compiler queries used by that MIR.
Lean validates the document, then interprets it with execution-owned state.
Changing the Rust source or compiler settings requires a new export.

## Export and execution flow

1. The pinned rustc invocation discovers reachable monomorphic MIR bodies and
   assigns physical identities to definitions, instances, types, constants,
   layouts and call sites. Generic declaration templates may still describe
   type structure; they are not answers to compiler queries.
2. For the discovered requests, the exporter asks rustc for evaluated
   constants, full canonical and contextual layouts, function ABI, selected
   call instances, covariance relations and other compiler results. A failed
   required query fails export. The document records the query input identity
   alongside each result.
3. Lean decodes immutable typed tables and checks references, result shapes
   and duplicate keys before running. A run creates its own World and imports
   the material prefix. It may intern additional structural type nodes, but a
   new node cannot reuse a material result simply because it resembles one.
4. Runtime providers look up a complete key in that run's tables. They pass
   the rustc result to the interpreter or report the missing demand with its
   identity. Local code may traverse or intern type syntax and apply the
   homogeneous array/slice element rule below; it does not select an impl,
   construct a function ABI, evaluate an executable constant or derive a
   physical layout from declaration syntax.

## Division of work

| Request | Authority | Lean operation |
| --- | --- | --- |
| Executable concrete constant | rustc evaluates the operand under its body typing environment | Decode and use the resulting value |
| Canonical or field/variant layout | rustc `layout_of` or `TyAndLayout::field` | Decode the full layout at the exact material key |
| Function or function-pointer ABI | rustc `fn_abi_of_instance` or `fn_abi_of_fn_ptr` | Read the exact instance/signature, environment and ordered extra-argument row |
| Call target or trait/instance selection | rustc's resolved instance and call-site row | Preserve the selected physical definition and complete arguments |
| Covariance relation used by execution | rustc `relate_types` for each collected demand | Read the exact source/target result row |
| Local type syntax | Material declarations and the execution's type arena | Intern and inspect structure without changing a compiler answer |

Type-level constant aliases created while instantiating a declaration use an
exported rustc evaluation row keyed by alias kind, definition and complete
generic arguments. The row names a concrete value in the type-constant pool;
Lean checks its type and reifies that value in the current execution arena.
The exporter also provides contextual field and variant layouts as projection
rows, each referring to a full rustc layout. A parent layout alone does not
authorize Lean to derive a field or variant layout.
For a homogeneous array or slice, rustc's element `field(0)` result supplies
the element layout for any element index; Lean applies that single result only
to those two shapes. Other field requests require their own indexed row.

Every result lookup checks its full identity in the current execution World.
A material numeric ID cannot be reused for a locally constructed type or
instance. If the export lacks a demanded rustc result, the provider returns an
error; it does not infer a result from a similar type, layout or signature.
The evaluator accepts only the exported evaluated form of executable MIR
constants. Missing CTFE results, failed compiler queries and incomplete demand
closures therefore remain visible failures.

The decoder stores immutable typed tables. The runtime may memoize query work
inside one execution World, together with its current allocation state. No
mutable answer cache is shared between executions. The optional frozen initial
compiler profile is captured before export queries and imported into one run;
later compiler allocations and cache entries are not merged into that snapshot.

## Validation boundary

`lake build Miri` checks Lean definitions and proofs. Fresh exports and focused
tests check that the exporter emits full compiler values and that Lean rejects
missing rows. One fresh `main` guest has run to exit 0 with this boundary;
that result establishes execution for that input and pinned compiler only.
The current runtime cannot ask rustc for an
identity first constructed after export; the exporter must include every
identity needed by a chosen execution, or the demand stops explicitly. See
[STATUS.md](../STATUS.md) for the remaining coverage and execution evidence.
Concrete Item and demanded FnPtr conversion shim bodies come from rustc's
instantiated MIR in the export closure; shims also have exact ABI rows. A novel
instance first constructed during execution is still outside that frozen
closure and fails at its body or ABI demand.
