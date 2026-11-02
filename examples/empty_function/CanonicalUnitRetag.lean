import empty_function.ConcreteProtection
import empty_function.UnitRetagResult
import empty_function.BodyTotal

/-! These actual source-dictionary laws are proved from canonical construction.
They are not metadata assumptions or input operation-success fields. -/
namespace EmptyFunction.CanonicalUnitRetag
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Actual unit uninitialization is independent of the retained provenance,
caller state, tree size and all allocation/runner headroom. -/
theorem write_zero (s : Static) (metadata : Metadata s)
    (place : MPlaceTy Provenance) (provenance : Option Provenance)
    (layout : place.layout = s.abi.ret.layout)
    (noMetadata : place.mplace.metadata = .none)
    (aligned : place.mplace.misaligned = none) (state : State) :
    s.cfg.retag.writeUninit (UnitRetagResult.retainedPlace place provenance) state = .ok () state := by
  have fields := MetadataBinding.fields s metadata (BodyTotal.capacity_positive s)
  let changed := UnitRetagResult.retainedPlace place provenance
  have unitLayout : localMemoryLayout changed.layout =
      ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some changed.layout.ty⟩ := by
    simp [changed,UnitRetagResult.retainedPlace,localMemoryLayout,layout,
      metadata.unitSize,metadata.unitAlign,metadata.unitBackend]
  have encoding : changed.mplace = ⟨changed.mplace.ptr,.none,none⟩ := by
    have metaEq : changed.mplace.metadata = .none := noMetadata
    have alignEq : changed.mplace.misaligned = none := aligned
    cases current : changed.mplace with
    | mk pointer metadataValue misaligned =>
      have actualMetadata : metadataValue = .none := by simpa only [current] using metaEq
      have actualAlignment : misaligned = none := by simpa only [current] using alignEq
      cases actualMetadata
      cases actualAlignment
      rfl
  have target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.cfg.access.runtime.pointerSize := by
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  rw [fields.writeUninit]
  exact UnitProtection.scoped_uninit s.cfg.access changed changed.mplace.ptr (some changed.layout.ty)
    s.cfg.access.runtime.pointerSize unitLayout encoding target
    (fun machine => by rw [fields.retainTouched]) state

structure Fields (s : Static) : Prop where
  size : ∀ place : MPlaceTy Provenance, place.layout = s.abi.ret.layout →
    s.cfg.retag.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE))
  freeze : ∀ place : MPlaceTy Provenance, place.layout = s.abi.ret.layout →
    s.cfg.retag.typeIsFreeze place.layout.ty = pure true
  precise : s.cfg.retag.preciseInteriorMut = pure false
  log : s.cfg.retag.logCreation = fun _ _ _ _ _ => pure ()
  check : ∀ pointer state, s.cfg.retag.checkPtrAccess pointer Size.ZERO state = .ok () state
  write : ∀ place provenance, place.layout = s.abi.ret.layout → place.mplace.metadata = .none →
    place.mplace.misaligned = none → ∀ state,
    s.cfg.retag.writeUninit (UnitRetagResult.retainedPlace place provenance) state = .ok () state

/-- All unit checks/writes come from the real canonical runner, with no numeric
resource or environmental choice premise. -/
theorem fields (s : Static) (metadata : Metadata s) (profile : Profile s) : Fields s := by
  have dictionary := MetadataBinding.fields s metadata (BodyTotal.capacity_positive s)
  refine ⟨?_,?_,?_,dictionary.log,?_,?_⟩
  · intro place layout
    have sized : place.layout.layout.isSized = true := by rw [layout]; exact metadata.unitSized
    simpa only [layout,metadata.unitSize,metadata.unitAlign] using dictionary.sizeAndAlign place sized
  · intro place layout
    apply dictionary.freeze
    rw [layout]
    exact metadata.unitFreeze
  · rw [dictionary.precise,profile.precise]
  · intro pointer state
    rw [dictionary.checkPtrAccess]
    exact UnitProtection.check_pointer_zero s.cfg.access pointer state
  · intro place provenance layout noMetadata aligned state
    exact write_zero s metadata place provenance layout noMetadata aligned state

open Lean Elab Command in
run_cmd do
  for name in #[``write_zero,``fields] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved canonical zero-retag axiom {dependency} in {name}"
#print axioms write_zero
#print axioms fields
end EmptyFunction.CanonicalUnitRetag
