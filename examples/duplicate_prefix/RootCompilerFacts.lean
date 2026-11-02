import duplicate_prefix.PreparedContracts

/-! Kernel-checked immutable compiler queries for the fixed root instance.
No query below assumes successful execution or a memory access. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootCompilerFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter

noncomputable def rootAbiQuery := CompilerInstanceAbi.abiOfInstance
  PreparedReflection.actual.compiler.lifecycle.instances RootBody.reflected.functionInstance #[]

theorem root_abi_supported : rootAbiQuery.isOk = true := by decide +kernel

private def checkedOk {Error Value : Type} :
    (value : Except Error Value) → value.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

private theorem checkedOk_eq {Error Value : Type}
    (value : Except Error Value) (success : value.isOk = true) :
    value = .ok (checkedOk value success) := by
  cases value with
  | ok value => rfl
  | error error => cases success

/-- Exact output of the canonical immutable full-instance ABI query. -/
def rootAbi : FnAbi MIR.TyId := checkedOk rootAbiQuery root_abi_supported

theorem root_abi_eq : rootAbiQuery = .ok rootAbi :=
  checkedOk_eq rootAbiQuery root_abi_supported

theorem root_abi_shape :
    (rootAbi.args.map (·.layout.ty), rootAbi.ret.layout.ty,
      rootAbi.cVariadic, rootAbi.fixedCount.toNat, rootAbi.conv, rootAbi.canUnwind) =
    (#[3, 5], 0, false, 2, .Rust, true) := by decide +kernel

theorem root_local_layouts_supported :
    (RootBody.reflected.body.body.locals.map fun ty =>
      (PreparedReflection.actual.runtime.lookup ty).isOk).all id = true := by decide +kernel

theorem usize_layout_supported :
    (PreparedReflection.actual.runtime.lookup 5).isOk = true := by decide +kernel

def usizeLayout : TyAndLayout MIR.TyId :=
  checkedOk (PreparedReflection.actual.runtime.lookup 5) usize_layout_supported

theorem usize_layout_eq : PreparedReflection.actual.runtime.lookup 5 = .ok usizeLayout :=
  checkedOk_eq _ usize_layout_supported

theorem usize_layout_shape :
    (usizeLayout.ty, usizeLayout.layout.size.bytes.toNat,
      usizeLayout.layout.align.abi.pow2) = (5, 8, 3) := by decide +kernel

theorem root_storage_trivial_bool :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 0 = .ok true := by decide +kernel

theorem root_storage_trivial_type2 :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 2 = .ok true := by decide +kernel

theorem root_storage_trivial_usize :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 5 = .ok true := by decide +kernel

theorem constant_binding_compatible (source : PreparedContracts.SourceComparator) :
    PreparedReflection.actual.compiler.constantBinding.compatible = true := by
  rw [PreparedReflection.actual.compiler.constantBinding.correct]
  exact source.reflexive

noncomputable def zeroGuardSite : CompilerConstantQueries.Site :=
  ⟨RootBody.reflected.body.identity.index, ⟨0, 4⟩, #[.field "kind", .field "rvalue", .field "right", .field "constant"]⟩

noncomputable def zeroGuardEvidence : Array CompilerConstantEvidence :=
  (PreparedReflection.actual.compiler.constants.evidence.filter (·.site == zeroGuardSite)).map (·.query)

theorem zero_guard_normalization :
    normalizationFromEvidence zeroGuardEvidence RootBody.reflected.functionInstance
      (.Val (.Scalar (.Int 0 8)) 5) = .ok (.Val (.Scalar (.Int 0 8)) 5) := by with_unfolding_all rfl

theorem zero_guard_evaluation :
    evaluationFromEvidence zeroGuardEvidence RootBody.reflected.functionInstance
      (.Val (.Scalar (.Int 0 8)) 5) ⟨3⟩ = .ok (.Scalar (.Int 0 8)) := by with_unfolding_all rfl

theorem bool_layout_supported :
    (PreparedReflection.actual.runtime.lookup 0).isOk = true := by decide +kernel

def boolLayout : TyAndLayout MIR.TyId :=
  checkedOk (PreparedReflection.actual.runtime.lookup 0) bool_layout_supported

theorem bool_layout_eq : PreparedReflection.actual.runtime.lookup 0 = .ok boolLayout :=
  checkedOk_eq _ bool_layout_supported

theorem bool_layout_shape :
    (boolLayout.ty, boolLayout.layout.size.bytes.toNat,
      boolLayout.layout.align.abi.pow2) = (0, 1, 0) := by decide +kernel

theorem bool_primitive_layout_eq :
    PreparedReflection.actual.compiler.primitiveLayout "bool" = .ok boolLayout := by with_unfolding_all rfl

theorem usize_primitive_layout_eq :
    PreparedReflection.actual.compiler.primitiveLayout "usize" = .ok usizeLayout := by with_unfolding_all rfl

theorem slice_layout_supported :
    (PreparedReflection.actual.runtime.lookup 3).isOk = true := by decide +kernel

def sliceLayout : TyAndLayout MIR.TyId :=
  checkedOk (PreparedReflection.actual.runtime.lookup 3) slice_layout_supported

theorem slice_layout_eq : PreparedReflection.actual.runtime.lookup 3 = .ok sliceLayout :=
  checkedOk_eq _ slice_layout_supported

theorem slice_layout_shape :
    (sliceLayout.ty, sliceLayout.layout.size.bytes.toNat, sliceLayout.layout.align.abi.pow2) =
      (3, 16, 3) := by decide +kernel

theorem root_abi_layouts :
    (rootAbi.args.getD 0 rootAbi.ret).layout = sliceLayout ∧
    (rootAbi.args.getD 1 rootAbi.ret).layout = usizeLayout ∧
    rootAbi.ret.layout = boolLayout := by
  constructor
  · with_unfolding_all rfl
  constructor <;> with_unfolding_all rfl

theorem root_storage_trivial_slice :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 3 = .ok true := by decide +kernel

theorem root_storage_trivial_never :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 6 = .ok true := by decide +kernel

open Lean Elab Command in
run_cmd do
  for declaration in #[``root_abi_supported, ``rootAbi, ``root_abi_eq,
      ``root_abi_shape, ``root_local_layouts_supported, ``usize_layout_supported,
      ``usize_layout_eq, ``usize_layout_shape, ``root_storage_trivial_bool,
      ``root_storage_trivial_type2, ``root_storage_trivial_usize,
      ``constant_binding_compatible, ``zero_guard_normalization, ``zero_guard_evaluation,
      ``bool_layout_supported, ``bool_layout_eq, ``bool_layout_shape,
      ``bool_primitive_layout_eq, ``usize_primitive_layout_eq, ``slice_layout_supported,
      ``slice_layout_eq, ``slice_layout_shape, ``root_abi_layouts, ``root_storage_trivial_slice,
      ``root_storage_trivial_never] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

#print axioms root_abi_supported
#print axioms root_abi_eq
#print axioms root_abi_shape
#print axioms root_local_layouts_supported
end
end DuplicatePrefix.RootCompilerFacts
