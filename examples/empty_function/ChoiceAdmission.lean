import empty_function.SourceChoicePlan

/-! Current-input binding of environmental choice supply. Every plan here is
derived from the actual effective destination and current backing/initializer
metadata. These conditions concern supplied random responses, not success of
address generation, materialization, copying or execution. The actual demand
inclusion and absence of explicit non-choice halts are separate obligations.
-/
namespace EmptyFunction.ChoiceAdmission
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open WholeCall
set_option autoImplicit false

/-- Current concrete provenance or nearest exposed wildcard geometry selects
an allocation ID. No operational resolver success is assumed. -/
inductive SelectedId (p : Packet) (id : AllocId) : Prop where
  | concrete (pointer : Pointer (Option Provenance)) (tag : BorTag)
      (effective : InputDraft.effectivePointer p = some pointer)
      (provenance : pointer.provenance = some (.concrete id tag))
  | wildcard (pointer : Pointer (Option Provenance))
      (row : AllocAddresses.InverseAddressEntry)
      (effective : InputDraft.effectivePointer p = some pointer)
      (provenance : pointer.provenance = some .wildcard)
      (rowAt : row ∈ p.before.machine.user.addresses.intToPtrMap)
      (identity : row.allocId = id)
      (exposed : p.before.machine.user.addresses.exposed.contains id = true)
      (geometry : InputDraft.WildcardCandidate p.before pointer row)

/-- Pure selected-descriptor precedence. Currently live data and function or
va-list IDs bypass conversion. Internal statics select the actual initializer;
foreign/TLS declaration IDs are not runtime storage IDs (InputDraft tracks that
coherence), and foreign relocation rows use their resolved backing mappings. -/
inductive SelectedSource (s : Static) (p : Packet) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) : Prop where
  | memory
      (selected : SelectedId p id)
      (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
      (noVaList : p.before.machine.memory.hasVaListId id = false)
      (descriptor : p.before.machine.memory.findGlobal? id = some
        ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
  | internalStatic (definition : DefId)
      (selected : SelectedId p id)
      (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
      (noVaList : p.before.machine.memory.hasVaListId id = false)
      (descriptor : p.before.machine.memory.findGlobal? id = some
        ⟨id,.static,source.byteSize,source.align,source.mutability,
          some (.static definition true false false)⟩)
      (initializer : s.prepared.image.initializers.find? (·.1 == definition) = some (definition,source))

/-- Environmental support is separate from runtime validity and arithmetic
headroom. Each branch binds the actual source/projected-local metadata to its
fixed plan. There is no existential arbitrary Plan, operation success, trace,
NoErrors or post-materialization validity field. All supported tape values are
admitted; errors in deterministic algorithms remain explicit halted plans. -/
structure Environment (s : Static) (p : Packet) : Prop where
  latent : ∀ id source, SelectedSource s p id source →
    ∃ binding : SourceChoicePlan.Binding s p.before source,
      SourceChoicePlan.Environment binding
  projected : InputDraft.NeedsEnclosingAllocation p →
    ∃ binding : SourceChoicePlan.ProjectedBinding s p,
      SourceChoicePlan.ProjectedEnvironment binding

/-- The raw immediate-projection branch has no pre-existing indirect pointer
and therefore cannot simultaneously select a latent destination allocation. -/
theorem projected_no_pointer (p : Packet)
    (projected : InputDraft.NeedsEnclosingAllocation p) :
    InputDraft.effectivePointer p = none := by
  rcases projected with ⟨frame,index,localId,offset,layout,identity,slot,value,
    current,encoding,slotAt,immediate⟩
  simp [InputDraft.effectivePointer,encoding,current,slotAt,immediate]

theorem projected_no_selected (p : Packet) (id : AllocId)
    (projected : InputDraft.NeedsEnclosingAllocation p) : ¬ SelectedId p id := by
  intro selected
  have absent := projected_no_pointer p projected
  cases selected with
  | concrete pointer tag effective provenance => simp [absent] at effective
  | wildcard pointer row effective provenance rowAt identity exposed geometry => simp [absent] at effective

/-- The two potential draw families cannot both occur for one current packet.
A conservative combined bound may nevertheless reserve one stack draw plus
three per actual source relocation. -/
theorem projected_no_source (s : Static) (p : Packet) (id : AllocId)
    (source : Allocation CtfeProvenance Unit)
    (projected : InputDraft.NeedsEnclosingAllocation p) : ¬ SelectedSource s p id source := by
  intro selected
  cases selected with
  | memory selected _ _ _ _ => exact projected_no_selected p id projected selected
  | internalStatic _ selected _ _ _ _ _ => exact projected_no_selected p id projected selected

end EmptyFunction.ChoiceAdmission

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.ChoiceAdmission." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty_function choice-admission axiom {dependency}"
