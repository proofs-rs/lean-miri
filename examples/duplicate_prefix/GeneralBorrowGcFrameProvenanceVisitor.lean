import duplicate_prefix.GeneralBorrowGcFrameProvenanceFold
namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceVisitor
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceFold
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
abbrev ActualFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra

def MetadataForm : MemPlaceMeta Provenance → Prop
  | .none => True
  | .metadata value => ScalarForm value

def PlaceForm (place : MemPlace Provenance) : Prop := MetadataForm place.metadata

def OperandForm : Operand Provenance → Prop
  | .immediate value => ImmediateForm value
  | .indirect place => PlaceForm place

def LocalForm (entry : LocalState Provenance LocalLayout) : Prop :=
  match entry.value with
  | .dead => True
  | .live value => OperandForm value

def RuntimePlaceForm : RuntimeStackPlace Provenance → Prop
  | .memory value => PlaceForm value.mplace
  | .frameLocal .. => True

structure FrameForm (frame : ActualFrame) : Prop where
  returnPlace : RuntimePlaceForm frame.returnPlace
  locals : ∀ entry ∈ frame.locals, LocalForm entry
  catchNone : frame.extra.catchUnwind = none

def LocalCarries (id : AllocId) (tag : BorTag) (entry : LocalState Provenance LocalLayout) : Prop :=
  ∃ value, entry.value = .live (.immediate value) ∧ GeneralBorrowGcFrameProvenanceScalar.Carries id tag value

def localVisit (roots : Roots) (entry : LocalState Provenance LocalLayout) : Except StepError Roots :=
  match entry.value with
  | .dead => .ok roots
  | .live value => roots.operand value

def protectedVisit (roots : Roots) (entry : AllocId × BorTag) : Except StepError Roots :=
  .ok (roots.add (some entry.1) (some entry.2))

def protectedScan (roots : Roots) : Option FrameState → Except StepError Roots
  | none => .ok roots
  | some frame => do
    let roots ← forIn (m := Except StepError) frame.protectedTags.toList roots (scan protectedVisit)
    pure roots

theorem metadata (roots : Roots) (value : MemPlaceMeta Provenance) (raw : MetadataForm value) :
    ∃ after, roots.metadata value = .ok after ∧ Extends roots after := by
  cases value with
  | none => exact ⟨roots,rfl,extends_refl roots⟩
  | metadata value => exact scalar roots value raw

theorem memPlace (roots : Roots) (place : MemPlace Provenance) (raw : PlaceForm place) :
    ∃ after, roots.memPlace place = .ok after ∧ Extends roots after := by
  obtain ⟨after,done,extension⟩ := metadata (roots.pointer place.ptr) place.metadata raw
  exact ⟨after,done,extends_trans (pointer_extends roots place.ptr) extension⟩

theorem operand (roots : Roots) (value : Operand Provenance) (raw : OperandForm value) :
    ∃ after, roots.operand value = .ok after ∧ Extends roots after := by
  cases value with
  | immediate value => exact immediate roots value raw
  | indirect place => exact memPlace roots place raw

theorem runtimePlace (roots : Roots) (value : RuntimeStackPlace Provenance) (raw : RuntimePlaceForm value) :
    ∃ after, roots.runtimePlace value = .ok after ∧ Extends roots after := by
  cases value with
  | memory place => exact memPlace roots place.mplace raw
  | frameLocal frame localId offset layout identity => exact ⟨roots,rfl,extends_refl roots⟩

theorem localEntry (roots : Roots) (entry : LocalState Provenance LocalLayout) (raw : LocalForm entry) :
    ∃ after, localVisit roots entry = .ok after ∧ Extends roots after ∧
      ∀ id tag, LocalCarries id tag entry → tag ∈ after.tags ∧ id ∈ after.allocations := by
  cases stored : entry.value with
  | dead =>
    refine ⟨roots,?_,extends_refl roots,?_⟩
    · simp only [localVisit,stored]
    · intro id tag impossible
      rcases impossible with ⟨imm,found,_⟩
      rw [stored] at found
      cases found
  | live value =>
    obtain ⟨after,done,extension⟩ := operand roots value (by simpa only [LocalForm,stored] using raw)
    refine ⟨after,?_,extension,?_⟩
    · simpa only [localVisit,stored] using done
    · intro id tag carried
      rcases carried with ⟨imm,found,pointer⟩
      have same : value = .immediate imm := LocalValue.live.inj (stored.symm.trans found)
      subst value
      obtain ⟨collected,collectedDone,_,tagFound,idFound⟩ := carries roots id tag imm pointer
      have equal : collected = after := Except.ok.inj (collectedDone.symm.trans done)
      subst collected
      exact ⟨tagFound,idFound⟩

theorem protect (roots : Roots) (frame : Option FrameState) :
    ∃ after, protectedScan roots frame = .ok after ∧ Extends roots after ∧
      ∀ id tag, (∃ borrow, frame = some borrow ∧ (id,tag) ∈ borrow.protectedTags) → tag ∈ after.tags ∧ id ∈ after.allocations := by
  cases frame with
  | none =>
    refine ⟨roots,rfl,extends_refl roots,?_⟩
    intro id tag member
    rcases member with ⟨borrow,impossible,_⟩
    cases impossible
  | some frame =>
    obtain ⟨after,done,extension,listed⟩ := collect frame.protectedTags.toList protectedVisit
      (fun id tag entry => entry = (id,tag))
      (by
        intro entry member roots
        refine ⟨_,rfl,add_extends roots _ _,?_⟩
        intro id tag same
        subst entry
        exact ⟨add_tag roots _ tag,add_allocation roots id _⟩) roots
    refine ⟨after,?_,extension,?_⟩
    · simp only [protectedScan,done,bind,Except.bind,Except.pure,pure]
    intro id tag member
    rcases member with ⟨borrow,same,present⟩
    cases same
    exact listed id tag ⟨(id,tag),Array.mem_toList_iff.mpr present,rfl⟩

/-- Exact factorization of the production frame visitor into its real return
place, live-local scan, and frame-owned protector scan. -/
theorem frame_eq (roots : Roots) (frame : ActualFrame) (catchNone : frame.extra.catchUnwind = none) :
    roots.frame frame = (do
      let first ← roots.runtimePlace frame.returnPlace
      let second ← forIn (m := Except StepError) frame.locals.toList first (scan localVisit)
      protectedScan second frame.extra.borrowTracker) := by
  have localScan :
      (fun (entry : LocalState Provenance LocalLayout) (roots : Roots) =>
        match entry.value with
        | .live value => do return .yield (← roots.operand value)
        | _ => pure (.yield roots)) = scan localVisit := by
    funext entry roots
    cases stored : entry.value <;> simp only [scan,localVisit,stored,bind,Except.bind,Except.pure,pure]
  unfold Roots.frame
  rw [catchNone]
  simp only [←Array.forIn_toList]
  simp only [scan, localVisit, protectedScan, protectedVisit]
  congr 1
  funext first
  congr 1
  · congr 1
  · funext second
    cases frame.extra.borrowTracker with
    | none => rfl
    | some borrow =>
      unfold scan protectedVisit
      simp only [bind, Except.bind, Except.pure, pure]
      cases forIn (m := Except StepError) borrow.protectedTags.toList second
        (fun entry current => Except.ok (ForInStep.yield (current.add (some entry.1) (some entry.2)))) <;> rfl


/-- A raw actual local or actual frame-owned protector is visited by the
source frame loop. Public scalar constructors and raw catch absence derive
collection success; no collector outcome or synthetic live-tag list is supplied. -/
theorem frame (roots : Roots) (frame : ActualFrame) (raw : FrameForm frame) :
    ∃ after, roots.frame frame = .ok after ∧ Extends roots after ∧
      ∀ id tag, ((∃ entry ∈ frame.locals, LocalCarries id tag entry) ∨
        ∃ borrow, frame.extra.borrowTracker = some borrow ∧ (id,tag) ∈ borrow.protectedTags) →
        tag ∈ after.tags ∧ id ∈ after.allocations := by
  obtain ⟨first,returnDone,returnExtension⟩ := runtimePlace roots frame.returnPlace raw.returnPlace
  obtain ⟨second,localsDone,localsExtension,localFound⟩ := collect frame.locals.toList localVisit LocalCarries
    (fun entry member roots => localEntry roots entry (raw.locals entry (Array.mem_toList_iff.mp member))) first
  obtain ⟨after,protectDone,protectExtension,protectedFound⟩ := protect second frame.extra.borrowTracker
  refine ⟨after,?_,extends_trans (extends_trans returnExtension localsExtension) protectExtension,?_⟩
  · rw [frame_eq roots frame raw.catchNone,returnDone]
    simp only [bind,Except.bind,localsDone,protectDone]
  · intro id tag member
    rcases member with localPointer | protector
    · rcases localPointer with ⟨entry,member,carried⟩
      have found := localFound id tag ⟨entry,Array.mem_toList_iff.mpr member,carried⟩
      exact ⟨protectExtension.1 tag found.1,protectExtension.2 id found.2⟩
    · exact protectedFound id tag protector

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceVisitor
