import duplicate_prefix.DuplicatePrefixTypeCacheOrigins
import Miri.Input.RuntimeArrayQueries
import Miri.Input.RuntimeArrayFacts

namespace DuplicatePrefix.RuntimeArrayPopulatedHit
open Miri Miri.ABI Miri.Input Miri.Interpreter
open RuntimeArrayTypes
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false

/-- Raw source array layout fields for a one-byte element. This is checked
against the real calculator below; it is not a replacement metadata provider. -/
def byteArrayLayout (element : LayoutData) (count : UInt64) : LayoutData := {
  variants := .Single 0
  fields := .Array element.size count
  backendRepr := .Memory (sized := true)
  largestNiche := if count != 0 then element.largestNiche else none
  uninhabited := element.uninhabited && count != 0
  align := element.align
  size := Size.ofBytes count
  maxReprAlign := none
  unadjustedAbiAlign := element.align.abi
  reprC := element.reprC
  randomizationSeed := element.randomizationSeed + count }

/-- Checked source arithmetic derives canonical byte-array layout from raw
byte-size and object-bound facts, without assuming a layout-query success. -/
theorem calculate_byte_array (target : RuntimeTargetDataLayout) (element : LayoutData)
    (count : UInt64) (byte : element.size = Size.ofBytes 1)
    (room : count < target.base.objSizeBound) :
    RuntimeArrayTypes.calculate target element count = .ok (byteArrayLayout element count) := by
  have multiply : (Size.ofBytes 1).checkedMul count target.base = some (Size.ofBytes count) := by
    unfold Size.checkedMul
    simp only [Size.ofBytes, UInt64.one_mul]
    by_cases zero : count = 0
    · subst count
      simp [HasDataLayout.dataLayout, room]
    · simp [HasDataLayout.dataLayout, zero, UInt64.div_self, room]
  simp only [RuntimeArrayTypes.calculate, byte, multiply, byteArrayLayout,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

/-- A genuine populated ARRAY constructor-key hit returns its exact cached
identity/layout and the unchanged entire World. In particular it neither checks
nor modifies aliases/nextId. Correctness of miss allocation is a separate WF
obligation; no target-absence or empty-cache premise occurs here. -/
theorem intern_byte_hit (world : World) (count : UInt64) (entry : Entry)
    (width : world.metadata.target.base.pointerWidth = .w64)
    (keyHit : world.entries.find? (fun row => row.key == (⟨.u8,count⟩ : Key)) = some entry) :
    RuntimeArrayTypes.internElement world world.byteLayout.ty count = .ok (entry.value, world) := by
  unfold RuntimeArrayTypes.internElement
  unfold_internal ".RuntimeArrayTypes.elementOfId"
  simp only [beq_self_eq_true, ↓reduceIte]
  unfold RuntimeArrayTypes.intern
  have fits : count.toNat < 2^(world.metadata.target.base.pointerWidth.bits.toNat) := by
    rw [width]
    change count.toNat < 2^64
    exact count.toNat_lt
  simp only [fits, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, keyHit]
  rfl

/-- Exact typed lookup on the same cached row. Key-hit and id-hit coherence
are distinct raw facts: Origins by itself establishes neither lookup agreement
nor canonical layouts, aliases, uniqueness or next-ID validity. -/
theorem field_byte_hit (world : World) (count : UInt64) (entry : Entry)
    (keyHit : world.entries.find? (fun row => row.key == (⟨.u8,count⟩ : Key)) = some entry)
    (idHit : world.entries.find? (fun row => row.value.ty == entry.value.ty) = some entry)
    (index : Nat) (bounds : index < count.toNat) :
    RuntimeArrayTypes.lookup world entry.value.ty = .ok entry.value ∧
      RuntimeArrayTypes.fieldLayout world entry.value.ty index = .ok world.byteLayout := by
  have key : entry.key = (⟨.u8,count⟩ : Key) := by simpa using Array.find?_some keyHit
  constructor
  · simp only [RuntimeArrayTypes.lookup, idHit]
    rfl
  · simp only [RuntimeArrayTypes.fieldLayout, RuntimeArrayTypes.arrayInfo, idHit, key]
    unfold_internal ".RuntimeArrayTypes.elementLayout"
    simp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, bounds,
      decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- The actual stateful metadata consumer accepts the populated array cache
and produces its correct element layout, without changing any state. Compiler
slice/reference IDs are not arrays and are not valid interner-entry keys. -/
theorem field_query_byte_hit {S : Type} (access : RuntimeArrayQueries.Access S)
    (before : S) (world : World) (entry : Entry) (count : UInt64)
    (current : access.get before = world)
    (keyHit : world.entries.find? (fun row => row.key == (⟨.u8,count⟩ : Key)) = some entry)
    (idHit : world.entries.find? (fun row => row.value.ty == entry.value.ty) = some entry)
    (base : LocalLayout → Nat → EStateM StepError S LocalLayout)
    (index : Nat) (bounds : index < count.toNat) :
    RuntimeArrayQueries.fieldLayout access base entry.value index before = .ok world.byteLayout before := by
  have contains : world.entries.any (fun row => row.value.ty == entry.value.ty) = true :=
    Array.any_eq_true'.mpr ⟨entry, Array.mem_of_find?_eq_some idHit, by simp⟩
  have facts := field_byte_hit world count entry keyHit idHit index bounds
  unfold RuntimeArrayQueries.fieldLayout
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, current, contains, ↓reduceIte, facts.1, facts.2,
    beq_self_eq_true, Bool.not_true, Bool.false_eq_true]
  unfold_internal ".RuntimeArrayQueries.lift"
  simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    beq_self_eq_true, ↓reduceIte]

/-- A correctly populated byte-array slot has exactly the layout that the
source calculator would produce, and repeated interning returns that same
identity without allocating another ID or touching aliases. These are local
raw key/layout/lookup coherence facts, not full interner WF. -/
theorem coherent_byte_hit (world : World) (count : UInt64) (entry : Entry)
    (width : world.metadata.target.base.pointerWidth = .w64)
    (byte : world.byteLayout.layout.size = Size.ofBytes 1)
    (room : count < world.metadata.target.base.objSizeBound)
    (layout : entry.value.layout = byteArrayLayout world.byteLayout.layout count)
    (keyHit : world.entries.find? (fun row => row.key == (⟨.u8,count⟩ : Key)) = some entry)
    (idHit : world.entries.find? (fun row => row.value.ty == entry.value.ty) = some entry)
    (index : Nat) (bounds : index < count.toNat) :
    RuntimeArrayTypes.calculate world.metadata.target world.byteLayout.layout count = .ok entry.value.layout ∧
      RuntimeArrayTypes.internElement world world.byteLayout.ty count = .ok (entry.value,world) ∧
      RuntimeArrayTypes.fieldLayout world entry.value.ty index = .ok world.byteLayout := by
  refine ⟨?_, intern_byte_hit world count entry width keyHit,
    (field_byte_hit world count entry keyHit idHit index bounds).2⟩
  rw [layout]
  exact calculate_byte_array _ _ _ byte room

theorem reference_source :
    (PreparedReflection.actual.runtime.source.types.find? (·.id == 3)).map TypeNode.shapeKind =
      some .reference := by
  with_unfolding_all rfl

/-- A cached compiler reference layout lives in RuntimeMetadata.layoutCache,
not the array interner. Correct populated array entries cannot shadow it.
This derives target exclusion from source type identity, never assuming it. -/
theorem reference_not_array (world : World)
    (metadata : world.metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins world) :
    world.entries.any (·.value.ty == 3) = false := by
  have source := reference_source
  cases found : PreparedReflection.actual.runtime.source.types.find? (·.id == 3) with
  | none => simp [found] at source
  | some node =>
    have shape : node.shapeKind = .reference := by
      simpa only [found, Option.map_some, Option.some.injEq] using source
    apply DuplicatePrefixTypeCacheOrigins.exclude_nonarray world origins 3 node
    · simpa only [metadata] using found
    · rw [shape]
      intro impossible
      cases impossible

/-- Actual typed-retag metadata dispatch keeps the reference query's compiler
provider with an arbitrary correctly populated array cache. Prior array hits
cannot turn this reference into an array, and no slice/reference miss premise
or empty cache is imposed. This does not certify array layouts or next-ID WF. -/
theorem reference_shape_dispatch {K U : Type}
    (access : RuntimeArrayQueries.Access (MachineHooks.State K U)) (context : CompilerFacts.Context)
    (base : TypedRetag.Hooks K U) (before : MachineHooks.State K U)
    (metadata : (access.get before).metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (access.get before)) :
    (RuntimeArrayFacts.retagHooks access context base).typeShape 3 before = base.typeShape 3 before := by
  have absent := reference_not_array (access.get before) metadata origins
  simp only [RuntimeArrayFacts.retagHooks, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, absent, Bool.false_eq_true, ↓reduceIte]

end DuplicatePrefix.RuntimeArrayPopulatedHit
