# Numeric MIR input format

The exporter emits root schema version 4. Lean accepts this exporter input
format directly. Historical fixtures must be converted by a test preparation
step; the active decoder does not expand the previous generic JSON DAG.

A reference is a bare nonnegative integer. Its meaning is supplied by the
field or compiler query schema, not by its numeric magnitude. Type 2 and
instance 2 refer to different entities. IDs belong to one exported document.

## Identity tables

The root `types`, `instances`, and `allocations` arrays retain their explicit
`type_id`, `instance_id`, and `allocation_id` identity fields. Other occurrences
of singleton reference records become integers. Plain instance references,
including `entry_instance`, also become integers: their kind and generic
arguments are stored in the canonical `instances` row. The exporter verifies
that those fields agree before removing the repeated record. A query record containing an
identity plus query evidence remains a record: its numeric identity field is
already the reference, and the evidence is not discarded.

`semantic_tables.predicates` retains explicit `predicate_id` fields. Predicate
IDs come from the compiler identity registry and may be sparse. Predicate query
rows are query evidence, not predicate table entries.

Types are registered by rustc `Ty` identity. `type_json_inner` is called only
when populating the canonical type table; recursive and repeated type uses pass
through `type_json_with_query` and emit references. Allocation IDs remain keyed
by source `AllocId`; equal bytes never cause two allocation identities to merge.
Source allocation IDs, provenance, relocations, MIR local/block/scope indices,
and binder variable indices retain their existing meanings and scope.

## Immutable metadata tables

`semantic_tables` has `schema_version: 1` and these arrays. Metadata IDs are
zero-based array positions and are structurally unique within their own kind.

| Table | Serializer / semantic role |
| --- | --- |
| `spans` | source span records, including callsites and assembly line spans |
| `layouts` | successful and failed type layout payloads |
| `function_abis` | successful `FnAbi` payloads, including compiler query results |
| `argument_abis` | argument/return type, layout, and passing mode records |
| `abi_attributes` | argument attributes |
| `abi_registers` | cast register descriptions |
| `cast_targets` | ABI cast targets |
| `generic_args` | generic argument lists, rebased lists, abstract-constant arguments |
| `regions` | region records, including lifetime generic arguments |
| `constants` | MIR constant operands and type-system constant expressions |
| `signatures` | function input/output signatures and named shim signature descriptors |
| `binders` | ordered bound-variable lists |
| `definitions` | crate/index definition identities |
| `instance_kinds` | concrete instance kind and shim descriptors |
| `predicates` | compiler predicate identities, as described above |
| `patterns` | interned type-pattern entities and their constant references |

Nested references are encoded before the containing metadata is interned. Exact
JSON structural keys, rather than hash equality alone, determine metadata
sharing. No structural comparison combines nodes from different tables.
Definition identities previously written as `crate:index` in type shapes and
as `{crate,index}` elsewhere use the same canonical definition record.

Compiler query results use the exporter's successful value directly. In
particular, `fn_abi` and `abi_query` are function ABI IDs; function and native
`signature_query` results are signature IDs. The main-entry `signature_query`
is a distinct structured record, so its field name alone does not give it a
signature-table role. Unavailable required compiler evidence fails export.
The active importer has no status-envelope or historical transport path.

Core references follow the same rule. Type-query dictionaries, primitive type
constructors and `box_type` results carry type IDs; drop glue, virtual resolution
and function/closure resolution results carry instance IDs. Optional results
may be null. Selected foreign-static `allocation_query` carries an
allocation ID. A `supertrait_slot` result is a scalar index. The decoder carries
these query roles through validation and typed decoding, checks reference bounds
against the owning tables, and keeps scalar results scalar even when their
integer value coincides with an existing ID.

The catalog is transport data. Readiness obligations are collected at semantic
uses under their source paths, rather than again under `semantic_tables` paths.
All catalog references are still validated, including unused catalog entries.

Scalar values, enum discriminants, display/debug text, field offsets, positions,
and MIR execution syntax remain inline. They are not assigned a global shared
node ID. Evaluated `ConstValue` scalar and pointer payloads retain their scalar
values and allocation references; they are not constant-expression identities.
Thread-local initializer `allocation_template` records describe bytes used to
create a separate allocation for each thread; they are not allocation IDs.
Structural interning does not change compiler query demand or turn a
query result into an execution or safety proof.

Inline enum skeletons belong to their owning rows: ABI passing modes, layout
variants, region kinds, and constant value-tree variants contain tags, scalar
data and references to the shared children. They have no separate exported
identity or query reference. Interned type patterns have a separate reference
role and therefore use their own table.

## Reference-role audit

The migration audits producer roles as well as serializer output shapes. The
bounded type-serializer inventory contains 164 exact calls: 154 emitted uses,
eight calls that only register compiler demand, and two forwarding calls.
Emitted roles include direct type fields, ordered type lists, primitive/type
query dictionaries, and successful optional query results. That count covers
type producers; it is not a count of every semantic producer.

The separate metadata inventory covers definition/span/region/generic argument,
constant/signature/binder/predicate/instance-kind, layout and ABI producers, plus
directly constructed references. The latter include global-byte
`existing_allocation` and `covered_allocation_ids`, relocation `target`, binding
`hoisted_from`, selected-static `allocation_query`, and pure instance
slots. These roles are shared by validation, typed decoding and source dependency
traversal. Ambiguous query results use their enclosing schema; numeric scalar
results do not become references by shape.

The regression fixture deliberately reaches all metadata kinds, including ABI
register/cast descriptions and recursive disjunction patterns. Additional tests
exercise foreign-static allocation queries, dangling references, duplicate and
sparse identities, document-local memo ownership, source-order ABI collection,
and exclusion of unreferenced transport entries from demanded ABI collection.
Historical-fixture conversion is a test tool and is not an accepted importer
input format.
