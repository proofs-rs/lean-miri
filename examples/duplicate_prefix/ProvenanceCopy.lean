import Lean
import duplicate_prefix.Bounds
import Miri.Memory.ProvenanceMap

/-! Provenance-copy lemmas over actual maps. The direct interval conditions
below constrain pointer locations, not the success of a copy operation. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.dsimp.instances true

namespace DuplicatePrefix.ProvenanceCopy
open Miri.ABI Miri.Memory

open Lean Elab Tactic in
elab "unfold_provenance " suffix:str : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  match found with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "Expected one source definition ending in {suffix.getString}"

open Lean Elab Tactic in
elab "unfold_provenance_at " suffix:str " at " h:ident : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  match found with
  | [name] =>
    evalTactic (← `(tactic| unfold $(mkIdent name) at $h:ident))
  | _ => throwError "Expected one source definition ending in {suffix.getString}"

open Lean Elab Command in
run_cmd do
  for (suffix, aliasName) in [
      (".Miri.Memory.ProvenanceMap.ptrFragments", `DuplicatePrefix.ProvenanceCopy.pointerFragments),
      (".Miri.Memory.ProvenanceMap.shiftedCopyOffset", `DuplicatePrefix.ProvenanceCopy.shiftedCopyOffset),
      (".Miri.Memory.ProvenanceMap.checked", `DuplicatePrefix.ProvenanceCopy.checkedResult),
      (".Miri.Memory.ProvenanceMap.insertEntry", `DuplicatePrefix.ProvenanceCopy.insertEntry),
      (".Miri.Memory.ProvenanceMap.mk", `DuplicatePrefix.ProvenanceCopy.mkMap),
      (".Miri.Memory.ProvenanceMap.removeEntries", `DuplicatePrefix.ProvenanceCopy.removeEntries),
      (".Miri.Memory.ProvenanceMap.adjustedStart", `DuplicatePrefix.ProvenanceCopy.adjustedStart)] do
    let candidates := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    let [name] := candidates | throwError "expected one source definition {suffix}"
    let info ← getConstInfo name
    liftCoreM <| addAndCompile <| .defnDecl {
      name := aliasName
      levelParams := info.levelParams
      type := info.type
      value := mkConst name (info.levelParams.map Level.param)
      hints := .regular 0
      safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst aliasName

theorem subtract_zero (offset : Size) : Size.sub offset Size.ZERO = .ok offset := by
  cases offset
  simp [Size.sub, Size.ZERO, Size.ofBytes]

theorem prefix_endpoint (n : UInt64) :
    (allocRange Size.ZERO (Size.ofBytes n)).endExclusive = .ok (Size.ofBytes n) := by
  simp [AllocRange.endExclusive, AllocRange.end, allocRange, Size.add, Size.ZERO,
    Size.ofBytes, Except.mapError]

theorem zero_endpoint (offset : Size) :
    (allocRange offset Size.ZERO).endExclusive = .ok offset := by
  cases offset
  simp [AllocRange.endExclusive, AllocRange.end, allocRange, Size.add, Size.ZERO,
    Size.ofBytes, Except.mapError]

theorem range_ptrs_at_zero (self : ProvenanceMap Prov) :
    self.rangePtrs ⟨Size.ZERO, Size.ZERO⟩ (Size.ofBytes 8) = .ok #[] := by
  unfold ProvenanceMap.rangePtrs
  unfold_provenance ".Miri.Memory.ProvenanceMap.adjustedStart"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
  simp [AllocRange.endExclusive, AllocRange.end, Size.add, allocRange, Size.ZERO, Size.ofBytes, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- No stored whole pointer crosses the prefix endpoint. Existing byte
fragments are unconstrained here: the preparation path copies them bytewise. -/
def NoPointerCrosses (self : ProvenanceMap Prov) (n : UInt64) : Prop :=
  ∀ entry ∈ self.ptrs,
    entry.1.bytes.toNat + 8 ≤ n.toNat ∨ n.toNat ≤ entry.1.bytes.toNat

theorem range_ptrs_at_n (self : ProvenanceMap Prov) (n : UInt64)
    (noCross : NoPointerCrosses self n) :
    self.rangePtrs ⟨Size.ofBytes n, Size.ZERO⟩ (Size.ofBytes 8) = .ok #[] := by
  have bounded : n.toNat - 7 < 18446744073709551616 := by
    have bound : n.toNat < 18446744073709551616 := n.toNat_lt_size
    omega
  unfold ProvenanceMap.rangePtrs
  unfold_provenance ".Miri.Memory.ProvenanceMap.adjustedStart"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
  simp [AllocRange.endExclusive, AllocRange.end, Size.add, allocRange, Size.ZERO, Size.ofBytes, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  intro offset prov member lower
  have placement := noCross (offset, prov) member
  dsimp only at placement
  simp only [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' bounded] at lower ⊢
  omega

def overlappingPointers (self : ProvenanceMap Prov) (range : AllocRange) (finish : Size) :=
  self.ptrs.filter fun entry =>
    UInt64.ofNat (range.start.bytes.toNat - 7) ≤ entry.1.bytes && entry.1.bytes < finish.bytes

theorem range_ptrs_exact (self : ProvenanceMap Prov) (range : AllocRange) (finish : Size)
    (endpoint : range.endExclusive = .ok finish) :
    self.rangePtrs range (Size.ofBytes 8) = .ok (overlappingPointers self range finish) := by
  unfold ProvenanceMap.rangePtrs overlappingPointers
  unfold_provenance ".Miri.Memory.ProvenanceMap.adjustedStart"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
  simp [endpoint, Size.ofBytes, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem mem_overlappingPointers (self : ProvenanceMap Prov) (range : AllocRange) (finish : Size)
    (entry : Size × Prov) (member : entry ∈ overlappingPointers self range finish) :
    entry ∈ self.ptrs := (Array.mem_filter.mp member).1

def prefixPointerEntries (self : ProvenanceMap Prov) (n : UInt64) : Array (Size × Prov) :=
  if (8 : UInt64) ≤ n then self.ptrs.filter (fun entry => entry.1.bytes < n - 7) else #[]

def prefixFragments (self : ProvenanceMap Prov) (n : UInt64) : Array (Size × PointerFrag Prov) :=
  (self.byteFragments.getD #[]).filter (fun entry => entry.1.bytes < n)

theorem for_in_push_entries (entries : Array α) :
    (forIn entries #[] fun entry acc =>
      (Except.ok (.yield (acc.push entry)) : Except ProvenanceMapError (ForInStep (Array α)))) =
      .ok entries := by
  change forIn entries #[] (fun entry acc => pure (.yield (acc.push entry))) =
    (pure entries : Except ProvenanceMapError (Array α))
  rw [Array.forIn_pure_yield_eq_foldl]
  congr 1
  simpa using Array.foldl_push_eq_append (as := entries) (bs := #[]) (f := id) rfl

theorem for_in_rebuild_entries (entries : Array (Size × α)) :
    (forIn entries #[] fun entry acc =>
      (Except.ok (.yield (acc.push ((⟨entry.1.bytes⟩ : Size), entry.2))) :
        Except ProvenanceMapError (ForInStep (Array (Size × α))))) = .ok entries := by
  exact for_in_push_entries entries

/-- Fragment construction itself cannot fail for an in-bounds complete
8-byte pointer, independently of the chosen fragment-selection predicate. -/
theorem pointer_fragments_exist (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8)
    (available : position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) :
    ∃ fragments, pointerFragments inRange position prov data (Size.ofBytes 8) = .ok fragments := by
  have endFits : position.bytes.toNat + (8 : UInt64).toNat < 2 ^ 64 := by
    simp only [UInt64.toNat_ofNat] at *
    omega
  unfold pointerFragments
  unfold_provenance ".Miri.Memory.ProvenanceMap.ptrFragments"
  rw [DuplicatePrefix.size_add_ok position (Size.ofBytes 8) endFits]
  simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl, UInt64.reduceGT, ↓reduceIte,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [show position.bytes.toNat + (8 : UInt64).toNat ≤ data.size from available,
    ↓reduceDIte]
  simp only [← apply_ite]
  simp [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Except.pure]
  exact ⟨_, rfl⟩

theorem shifted_copy_zero (range : AllocRange) (offset : Size)
    (fits : offset.bytes.toNat + range.start.bytes.toNat < 2 ^ 64) :
    shiftedCopyOffset range 0 offset = .ok (Size.ofBytes (offset.bytes + range.start.bytes)) := by
  unfold shiftedCopyOffset
  unfold_provenance ".Miri.Memory.ProvenanceMap.shiftedCopyOffset"
  rw [DuplicatePrefix.size_add_ok offset range.start fits]
  simp [Size.mul, Size.add, Size.ZERO, Size.ofBytes, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A general successful-iteration lifting rule, proved by induction on the
actual list `forIn` implementation. The caller must discharge each local
action; no interpreter or provenance success is assumed by this rule itself. -/
theorem list_for_in_success {α σ ε : Type} (entries : List α)
    (action : α → EStateM ε σ Unit)
    (succeeds : ∀ entry ∈ entries, ∀ state, ∃ updated, action entry state = .ok () updated)
    (state : σ) :
    ∃ updated,
      (forIn entries () fun entry _ => do
        action entry
        pure (.yield ())) state = .ok () updated := by
  induction entries generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons first rest ih =>
    obtain ⟨middle, firstSuccess⟩ := succeeds first (by simp) state
    obtain ⟨finish, restSuccess⟩ := ih
      (fun entry member => succeeds entry (by simp [member])) middle
    refine ⟨finish, ?_⟩
    simp only [List.forIn_cons, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      firstSuccess]
    exact restSuccess

theorem array_for_in_success {α σ ε : Type} (entries : Array α)
    (action : α → EStateM ε σ Unit)
    (succeeds : ∀ entry ∈ entries, ∀ state, ∃ updated, action entry state = .ok () updated)
    (state : σ) :
    ∃ updated,
      (forIn entries () fun entry _ => do
        action entry
        pure (.yield ())) state = .ok () updated := by
  rcases entries with ⟨entries⟩
  have succeedsList : ∀ entry ∈ entries, ∀ state, ∃ updated, action entry state = .ok () updated := by
    intro entry member
    exact succeeds entry (by simpa using member)
  simpa using list_for_in_success entries action succeedsList state

def insert_whole_action (range : AllocRange) (entry : Size × Prov) : ProvenanceMap.Mutation Prov Unit := do
  let shifted ← checkedResult (shiftedCopyOffset range 0 entry.1)
  let current ← EStateM.get
  EStateM.set (mkMap (insertEntry current.ptrs shifted entry.2) current.byteFragments)

def insert_fragment_action (range : AllocRange) (entry : Size × PointerFrag Prov) :
    ProvenanceMap.Mutation Prov Unit := do
  let shifted ← checkedResult (shiftedCopyOffset range 0 entry.1)
  let current ← EStateM.get
  EStateM.set (mkMap current.ptrs
    (some (insertEntry (current.byteFragments.getD #[]) shifted entry.2)))

theorem insert_whole_action_success (range : AllocRange) (entry : Size × Prov)
    (fits : entry.1.bytes.toNat + range.start.bytes.toNat < 2 ^ 64)
    (state : ProvenanceMap Prov) :
    ∃ updated, insert_whole_action range entry state = .ok () updated := by
  unfold insert_whole_action
  rw [shifted_copy_zero range entry.1 fits]
  unfold checkedResult
  unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
  exact ⟨_, rfl⟩

theorem insert_fragment_action_success (range : AllocRange) (entry : Size × PointerFrag Prov)
    (fits : entry.1.bytes.toNat + range.start.bytes.toNat < 2 ^ 64)
    (state : ProvenanceMap Prov) :
    ∃ updated, insert_fragment_action range entry state = .ok () updated := by
  unfold insert_fragment_action
  rw [shifted_copy_zero range entry.1 fits]
  unfold checkedResult
  unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
  exact ⟨_, rfl⟩

def whole_loop (range : AllocRange) (entries : Array (Size × Prov)) : ProvenanceMap.Mutation Prov Unit := do
  for entry in entries do insert_whole_action range entry

def fragment_loop (range : AllocRange) (entries : Array (Size × PointerFrag Prov)) :
    ProvenanceMap.Mutation Prov Unit := do
  let current ← EStateM.get
  EStateM.set (mkMap current.ptrs (some (current.byteFragments.getD #[])))
  for entry in entries do insert_fragment_action range entry

theorem whole_loop_success (range : AllocRange) (entries : Array (Size × Prov))
    (fits : ∀ entry ∈ entries, entry.1.bytes.toNat + range.start.bytes.toNat < 2 ^ 64)
    (state : ProvenanceMap Prov) :
    ∃ updated, whole_loop range entries state = .ok () updated := by
  have total := array_for_in_success entries (insert_whole_action range)
    (fun entry member => insert_whole_action_success range entry (fits entry member)) state
  obtain ⟨updated, success⟩ := total
  refine ⟨updated, ?_⟩
  unfold whole_loop
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  change forIn entries PUnit.unit (fun entry _ =>
    EStateM.bind (insert_whole_action range entry) (fun _ => EStateM.pure (.yield PUnit.unit))) state =
      .ok PUnit.unit updated at success
  rw [success]

theorem fragment_loop_success (range : AllocRange) (entries : Array (Size × PointerFrag Prov))
    (fits : ∀ entry ∈ entries, entry.1.bytes.toNat + range.start.bytes.toNat < 2 ^ 64)
    (state : ProvenanceMap Prov) :
    ∃ updated, fragment_loop range entries state = .ok () updated := by
  have total := array_for_in_success entries (insert_fragment_action range)
    (fun entry member => insert_fragment_action_success range entry (fits entry member))
    (mkMap state.ptrs (some (state.byteFragments.getD #[])))
  obtain ⟨updated, success⟩ := total
  refine ⟨updated, ?_⟩
  unfold fragment_loop
  simp only [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, EStateM.get, EStateM.set]
  change forIn entries PUnit.unit (fun entry _ =>
    EStateM.bind (insert_fragment_action range entry) (fun _ => EStateM.pure (.yield PUnit.unit)))
    (mkMap state.ptrs (some (state.byteFragments.getD #[]))) =
      .ok PUnit.unit updated at success
  rw [success]

def apply_once (copy : ProvenanceCopy Prov) (range : AllocRange) : ProvenanceMap.Mutation Prov Unit := do
  if !copy.ptrs.isEmpty then whole_loop range copy.ptrs
  if !copy.byteFragments.isEmpty then fragment_loop range copy.byteFragments

theorem estate_bind_assoc {ε σ α β γ : Type} (action : EStateM ε σ α)
    (next : α → EStateM ε σ β) (finish : β → EStateM ε σ γ) :
    EStateM.bind (EStateM.bind action next) finish =
      EStateM.bind action (fun value => EStateM.bind (next value) finish) := by
  funext state
  cases result : action state <;> simp [EStateM.bind, result]

theorem estate_pure_bind {ε σ α β : Type} (value : α) (next : α → EStateM ε σ β) :
    EStateM.bind (EStateM.pure value) next = next value := by rfl

theorem estate_bind_pure {ε σ α : Type} (action : EStateM ε σ α) :
    EStateM.bind action EStateM.pure = action := by
  funext state
  cases result : action state <;> simp [EStateM.bind, EStateM.pure, result]

theorem apply_copy_once_reduces (copy : ProvenanceCopy Prov) (range : AllocRange)
    (pointerCountFits : copy.ptrs.size < 2 ^ 64)
    (fragmentCountFits : copy.byteFragments.size < 2 ^ 64) :
    ProvenanceMap.applyCopy copy range 1 = apply_once copy range := by
  unfold ProvenanceMap.applyCopy apply_once whole_loop fragment_loop
  unfold insert_whole_action insert_fragment_action checkedResult insertEntry mkMap shiftedCopyOffset
  by_cases pointerEmpty : copy.ptrs.isEmpty <;>
    by_cases fragmentEmpty : copy.byteFragments.isEmpty <;>
    simp [pointerEmpty, fragmentEmpty, Nat.not_le_of_lt pointerCountFits,
      Nat.not_le_of_lt fragmentCountFits, Std.Legacy.Range.forIn_eq_forIn_range',
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, EStateM.get, EStateM.set]
  all_goals try simp only [estate_bind_assoc, estate_pure_bind, estate_bind_pure]
  all_goals try rfl

/-- The actual one-copy provenance insertion cannot fail when both source
entry arrays fit the host count and their destination offsets fit u64. This
allows arbitrary maps and byte-fragment snapshots; no empty-map premise is
used. The numeric premises are representation bounds, not success premises. -/
theorem apply_copy_once_exists (copy : ProvenanceCopy Prov) (range : AllocRange)
    (pointerCountFits : copy.ptrs.size < 2 ^ 64)
    (fragmentCountFits : copy.byteFragments.size < 2 ^ 64)
    (pointerOffsetsFit : ∀ entry ∈ copy.ptrs,
      entry.1.bytes.toNat + range.start.bytes.toNat < 2 ^ 64)
    (fragmentOffsetsFit : ∀ entry ∈ copy.byteFragments,
      entry.1.bytes.toNat + range.start.bytes.toNat < 2 ^ 64)
    (state : ProvenanceMap Prov) :
    ∃ updated, ProvenanceMap.applyCopy copy range 1 state = .ok () updated := by
  rw [apply_copy_once_reduces copy range pointerCountFits fragmentCountFits]
  by_cases pointerEmpty : copy.ptrs.isEmpty
  · by_cases fragmentEmpty : copy.byteFragments.isEmpty
    · refine ⟨state, ?_⟩
      simp [apply_once, pointerEmpty, fragmentEmpty]
      rfl
    · obtain ⟨updated, success⟩ := fragment_loop_success range copy.byteFragments fragmentOffsetsFit state
      refine ⟨updated, ?_⟩
      simpa [apply_once, pointerEmpty, fragmentEmpty] using success
  · obtain ⟨middle, pointersSuccess⟩ := whole_loop_success range copy.ptrs pointerOffsetsFit state
    by_cases fragmentEmpty : copy.byteFragments.isEmpty
    · refine ⟨middle, ?_⟩
      simpa [apply_once, pointerEmpty, fragmentEmpty, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, pointersSuccess] using pointersSuccess
    · obtain ⟨updated, fragmentsSuccess⟩ := fragment_loop_success range copy.byteFragments fragmentOffsetsFit middle
      refine ⟨updated, ?_⟩
      simp only [apply_once, pointerEmpty, fragmentEmpty, Bool.not_false,
        Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Bind.bind, EStateM.bind]
      rw [pointersSuccess]
      exact fragmentsSuccess

def clear_boundary_action (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) : ProvenanceMap.Mutation Prov Unit := do
  let fragments ← checkedResult (pointerFragments inRange position prov data (Size.ofBytes 8))
  let current ← EStateM.get
  let bytes := fragments.foldl (fun values entry => insertEntry values entry.1 entry.2)
    (current.byteFragments.getD #[])
  EStateM.set (mkMap current.ptrs (some bytes))

theorem clear_boundary_action_exists (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8)
    (available : position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) (state : ProvenanceMap Prov) :
    ∃ updated, clear_boundary_action inRange position prov data state = .ok () updated := by
  obtain ⟨fragments, success⟩ := pointer_fragments_exist inRange position prov data available storageFits
  unfold clear_boundary_action
  rw [success]
  unfold checkedResult
  unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
  exact ⟨_, rfl⟩

def clear_finish_action (range : AllocRange) (finish : Size) : ProvenanceMap.Mutation Prov Unit := do
  let start ← checkedResult (adjustedStart range (Size.ofBytes 8))
  let current ← EStateM.get
  EStateM.set (mkMap (removeEntries current.ptrs start finish) current.byteFragments)

theorem clear_finish_action_exists (range : AllocRange) (finish : Size) (state : ProvenanceMap Prov) :
    ∃ updated, clear_finish_action range finish state = .ok () updated := by
  unfold clear_finish_action adjustedStart checkedResult
  unfold_provenance ".Miri.Memory.ProvenanceMap.adjustedStart"
  unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
  simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
    show ((8 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

def clear_last_action (range : AllocRange) (finish : Size) (data : Array UInt8)
    (entries : Array (Size × Prov)) : ProvenanceMap.Mutation Prov Unit := do
  if let some (last, prov) := entries.back? then
    let lastEnd ← checkedResult ((Size.add last (Size.ofBytes 8)).mapError
      (ProvenanceMapError.memory ∘ MemoryError.sizeError))
    if lastEnd.bytes > finish.bytes then
      clear_boundary_action (fun pos => finish.bytes ≤ pos.bytes) last prov data
  clear_finish_action range finish

theorem clear_last_action_exists (range : AllocRange) (finish : Size) (data : Array UInt8)
    (entries : Array (Size × Prov))
    (pointerBounds : ∀ entry ∈ entries, entry.1.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) (state : ProvenanceMap Prov) :
    ∃ updated, clear_last_action range finish data entries state = .ok () updated := by
  cases lastEntry : entries.back? with
  | none => simpa [clear_last_action, lastEntry] using clear_finish_action_exists range finish state
  | some entry =>
    obtain ⟨position, prov⟩ := entry
    have available : position.bytes.toNat + 8 ≤ data.size :=
      pointerBounds (position, prov) (Array.mem_of_back? lastEntry)
    have fits : position.bytes.toNat + (8 : UInt64).toNat < 2 ^ 64 := by
      simp only [show (8 : UInt64).toNat = 8 from rfl]
      omega
    have addSuccess := DuplicatePrefix.size_add_ok position (Size.ofBytes 8) fits
    by_cases overlaps : (position.bytes + 8) > finish.bytes
    · obtain ⟨middle, fragmentsSuccess⟩ := clear_boundary_action_exists
        (fun pos => finish.bytes ≤ pos.bytes) position prov data available storageFits state
      obtain ⟨updated, finishSuccess⟩ := clear_finish_action_exists range finish middle
      refine ⟨updated, ?_⟩
      unfold clear_last_action
      rw [lastEntry]
      dsimp only
      rw [addSuccess]
      unfold checkedResult
      unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
      simp only [Except.mapError, Bind.bind, EStateM.bind, Pure.pure, Except.pure,
        EStateM.pure, Size.ofBytes, overlaps, ↓reduceIte]
      rw [fragmentsSuccess]
      exact finishSuccess
    · obtain ⟨updated, success⟩ := clear_finish_action_exists range finish state
      refine ⟨updated, ?_⟩
      unfold clear_last_action
      rw [lastEntry]
      dsimp only
      rw [addSuccess]
      unfold checkedResult
      unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
      simpa [Except.mapError, Bind.bind, EStateM.bind, Pure.pure, Except.pure,
        EStateM.pure, Size.ofBytes, overlaps] using success

def clear_first_action (range : AllocRange) (finish : Size) (data : Array UInt8)
    (entries : Array (Size × Prov)) : ProvenanceMap.Mutation Prov Unit := do
  if let some (first, prov) := entries[0]? then
    if first.bytes < range.start.bytes then
      clear_boundary_action (fun pos => pos.bytes < range.start.bytes) first prov data
  clear_last_action range finish data entries

theorem clear_first_action_exists (range : AllocRange) (finish : Size) (data : Array UInt8)
    (entries : Array (Size × Prov))
    (pointerBounds : ∀ entry ∈ entries, entry.1.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) (state : ProvenanceMap Prov) :
    ∃ updated, clear_first_action range finish data entries state = .ok () updated := by
  cases firstEntry : entries[0]? with
  | none => simpa [clear_first_action, firstEntry] using
      clear_last_action_exists range finish data entries pointerBounds storageFits state
  | some entry =>
    obtain ⟨position, prov⟩ := entry
    by_cases overlaps : position.bytes < range.start.bytes
    · have available : position.bytes.toNat + 8 ≤ data.size :=
        pointerBounds (position, prov) (Array.mem_of_getElem? firstEntry)
      obtain ⟨middle, fragmentsSuccess⟩ := clear_boundary_action_exists
        (fun pos => pos.bytes < range.start.bytes) position prov data available storageFits state
      obtain ⟨updated, lastSuccess⟩ := clear_last_action_exists range finish data entries pointerBounds storageFits middle
      refine ⟨updated, ?_⟩
      simp only [clear_first_action, firstEntry, overlaps, ↓reduceIte, Bind.bind, EStateM.bind]
      rw [fragmentsSuccess]
      exact lastSuccess
    · simpa [clear_first_action, firstEntry, overlaps] using
        clear_last_action_exists range finish data entries pointerBounds storageFits state

theorem pointer_end_checked (position : Size) (data : Array UInt8)
    (available : position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) :
    Size.add position (Size.ofBytes 8) = .ok (Size.ofBytes (position.bytes + 8)) := by
  have fits : position.bytes.toNat + (8 : UInt64).toNat < 2 ^ 64 := by
    simp only [show (8 : UInt64).toNat = 8 from rfl]
    omega
  exact DuplicatePrefix.size_add_ok position (Size.ofBytes 8) fits

open Lean Elab Tactic in
elab "simpa_clear_implementation" " using " h:ident : tactic => do
  let names ← ([".Miri.Memory.ProvenanceMap.checked",
    ".Miri.Memory.ProvenanceMap.adjustedStart"] : List String).mapM fun (suffix : String) => do
      let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some name else none
      match found with
      | [name] => pure (mkIdent name)
      | _ => throwError "expected one source definition {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simpa only [mkMap, removeEntries,
    show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
    show ((8 : UInt64) == 0) = false from rfl,
    show (8 : UInt64).toNat = 8 from rfl,
    show (8 : Nat) - 1 = 7 from rfl,
    Bool.false_eq_true, ↓reduceIte, estate_bind_assoc, estate_pure_bind,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, EStateM.get, EStateM.set,
    Except.mapError, Except.pure, Except.bind, $[$names:ident],*] using $h:ident))

/-- Whole-pointer storage bounds suffice for clearing any checked interval:
boundary-crossing pointers are fragmented rather than rejected. -/
theorem clear_exists (self : ProvenanceMap Prov) (range : AllocRange) (finish : Size)
    (data : Array UInt8) (endpoint : range.endExclusive = .ok finish)
    (pointerBounds : ∀ entry ∈ self.ptrs, entry.1.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) :
    ∃ updated, ProvenanceMap.clear range data (Size.ofBytes 8) self = .ok () updated := by
  unfold ProvenanceMap.clear
  unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  by_cases zero : range.size.bytes = 0
  · refine ⟨self, ?_⟩
    simp [zero, Pure.pure, EStateM.pure]
  · simp only [show (range.size.bytes == 0) = false from by simp [zero],
      Bool.false_eq_true, ↓reduceIte, endpoint, Except.mapError,
      Bind.bind, EStateM.bind, EStateM.get, EStateM.set, Pure.pure, EStateM.pure]
    unfold ProvenanceMap.rangePtrs
    unfold_provenance ".Miri.Memory.ProvenanceMap.adjustedStart"
    unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
    unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
    simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
      Bool.false_eq_true, ↓reduceIte,
      endpoint, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp only [show ((8 : UInt64) == 0) = false from rfl,
      show (8 : UInt64).toNat = 8 from rfl, show (8 : Nat) - 1 = 7 from rfl,
      Bool.false_eq_true, ↓reduceIte, Except.mapError, Except.bind,
      EStateM.bind, EStateM.get, EStateM.set, EStateM.pure]
    generalize entriesEq :
      (self.ptrs.filter fun entry =>
        decide ((Size.ofBytes (UInt64.ofNat (range.start.bytes.toNat - 7))).bytes ≤ entry.1.bytes) &&
        decide (entry.1.bytes < finish.bytes)) = entries
    let state := mkMap self.ptrs (self.byteFragments.map fun bytes => removeEntries bytes range.start finish)
    have bounds : ∀ entry ∈ entries, entry.1.bytes.toNat + 8 ≤ data.size := by
      intro entry member
      rw [← entriesEq] at member
      exact pointerBounds entry (Array.mem_filter.mp member).1
    by_cases empty : entries.isEmpty
    · refine ⟨state, ?_⟩
      simp only [empty, ↓reduceIte, EStateM.pure]
      rfl
    · simp only [empty, ↓reduceIte]
      cases firstEntry : entries[0]? <;> cases lastEntry : entries.back?
      case none.none =>
        simp only [firstEntry, lastEntry]
        exact ⟨_, rfl⟩
      case none.some lastPair =>
        obtain ⟨position, prov⟩ := lastPair
        have available := bounds (position, prov) (Array.mem_of_back? lastEntry)
        obtain ⟨fragments, fragmentsSuccess⟩ := pointer_fragments_exist
          (fun pos => finish.bytes ≤ pos.bytes) position prov data available storageFits
        unfold pointerFragments at fragmentsSuccess
        have addSuccess := pointer_end_checked position data available storageFits
        by_cases overlap : position.bytes + 8 > finish.bytes <;>
          simp_all only [firstEntry, lastEntry, addSuccess, fragmentsSuccess,
            show (Size.ofBytes (position.bytes + 8)).bytes = position.bytes + 8 from rfl,
            overlap, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Bind.bind, Except.mapError, EStateM.bind, EStateM.get, EStateM.set, EStateM.pure]
        all_goals exact ⟨_, rfl⟩
      case some.none firstPair =>
        obtain ⟨position, prov⟩ := firstPair
        have available := bounds (position, prov) (Array.mem_of_getElem? firstEntry)
        obtain ⟨fragments, fragmentsSuccess⟩ := pointer_fragments_exist
          (fun pos => pos.bytes < range.start.bytes) position prov data available storageFits
        unfold pointerFragments at fragmentsSuccess
        by_cases overlap : position.bytes < range.start.bytes <;>
          simp_all only [firstEntry, lastEntry, fragmentsSuccess, overlap, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Bind.bind,
            Except.mapError, EStateM.bind, EStateM.get, EStateM.set, EStateM.pure]
        all_goals exact ⟨_, rfl⟩
      case some.some firstPair lastPair =>
        obtain ⟨firstPosition, firstProv⟩ := firstPair
        obtain ⟨lastPosition, lastProv⟩ := lastPair
        have firstAvailable := bounds (firstPosition, firstProv) (Array.mem_of_getElem? firstEntry)
        have lastAvailable := bounds (lastPosition, lastProv) (Array.mem_of_back? lastEntry)
        obtain ⟨leftFragments, leftSuccess⟩ := pointer_fragments_exist
          (fun pos => pos.bytes < range.start.bytes) firstPosition firstProv data firstAvailable storageFits
        obtain ⟨rightFragments, rightSuccess⟩ := pointer_fragments_exist
          (fun pos => finish.bytes ≤ pos.bytes) lastPosition lastProv data lastAvailable storageFits
        unfold pointerFragments at leftSuccess rightSuccess
        have addSuccess := pointer_end_checked lastPosition data lastAvailable storageFits
        by_cases leftOverlap : firstPosition.bytes < range.start.bytes <;>
          by_cases rightOverlap : lastPosition.bytes + 8 > finish.bytes <;>
          simp_all only [firstEntry, lastEntry, addSuccess, leftSuccess, rightSuccess,
            show (Size.ofBytes (lastPosition.bytes + 8)).bytes = lastPosition.bytes + 8 from rfl,
            leftOverlap, rightOverlap, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Bind.bind, Except.mapError,
            EStateM.bind, EStateM.get, EStateM.set, EStateM.pure]
        all_goals exact ⟨_, rfl⟩


/-- Whole pointer entries and existing byte fragments can both be present.
Only pointers crossing the right endpoint need the later fragmentation case. -/
theorem prepare_prefix_no_cross (self : ProvenanceMap Prov) (n : UInt64)
    (data : Array UInt8) (noCross : NoPointerCrosses self n) :
    self.prepareCopy (allocRange Size.ZERO (Size.ofBytes n)) data (Size.ofBytes 8) =
      .ok ⟨prefixPointerEntries self n, prefixFragments self n⟩ := by
  unfold ProvenanceMap.prepareCopy
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  simp only [prefix_endpoint, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  dsimp only [allocRange]
  rw [range_ptrs_at_zero, range_ptrs_at_n self n noCross]
  unfold_provenance ".Miri.Memory.ProvenanceMap.subtractSize"
  unfold ProvenanceMap.rangeBytes
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
  by_cases large : (8 : UInt64) ≤ n
  · have nonnegative : ¬ n < (7 : UInt64) := by
      simp [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    cases fragments : self.byteFragments <;>
      simp [prefixPointerEntries, prefixFragments, fragments, large, nonnegative,
        allocRange, Size.ZERO, Size.ofBytes, Size.sub,
        AllocRange.endExclusive, AllocRange.end, Size.add, for_in_rebuild_entries,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

  · cases fragments : self.byteFragments <;>
      simp [prefixPointerEntries, prefixFragments, fragments, large,
        allocRange, Size.ZERO, Size.ofBytes, Size.sub,
        AllocRange.endExclusive, AllocRange.end, Size.add, for_in_rebuild_entries,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]


/-! The following source-refinement lemmas also cover a pointer crossing
the prefix endpoint. The transparency option affects elaboration/unification
only; the resulting ordinary proof terms are still kernel checked. -/
set_option backward.isDefEq.respectTransparency false

def checked_append_step (entry : Size × α) (initial : Array (Size × α)) :
    Except ProvenanceMapError (ForInStep (Array (Size × α))) := do
  let shifted ← (Size.sub entry.1 Size.ZERO).mapError
    (ProvenanceMapError.memory ∘ MemoryError.sizeError)
  if !((initial.back?.map fun last => decide (last.1.bytes < shifted.bytes)).getD true) then
    throw .unsortedOrDuplicateKeys
  pure (.yield (initial.push (shifted, entry.2)))

theorem checked_append_step_success (entry : Size × α) (initial : Array (Size × α))
    (before : ∀ old ∈ initial, old.1.bytes < entry.1.bytes) :
    checked_append_step entry initial = .ok (.yield (initial.push entry)) := by
  unfold checked_append_step
  rw [subtract_zero]
  simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases lastEntry : initial.back? with
  | none => simp
  | some last =>
    have ordered := before last (Array.mem_of_back? lastEntry)
    simp [ordered]

theorem list_checked_append_exact (entries : List (Size × α)) (initial : Array (Size × α))
    (ordered : entries.Pairwise fun left right => left.1.bytes < right.1.bytes)
    (before : ∀ old ∈ initial, ∀ fresh ∈ entries, old.1.bytes < fresh.1.bytes) :
    forIn entries initial checked_append_step = .ok (initial ++ entries.toArray) := by
  induction entries generalizing initial with
  | nil => simp [Pure.pure, Except.pure]
  | cons first rest ih =>
    obtain ⟨firstBefore, restOrdered⟩ := List.pairwise_cons.mp ordered
    have firstStep := checked_append_step_success first initial
      (fun old member => before old member first (by simp))
    have nextBefore : ∀ old ∈ initial.push first, ∀ fresh ∈ rest, old.1.bytes < fresh.1.bytes := by
      intro old oldMember fresh freshMember
      rcases Array.mem_push.mp oldMember with oldMember | equality
      · exact before old oldMember fresh (by simp [freshMember])
      · subst old
        exact firstBefore fresh freshMember
    rw [List.forIn_cons, firstStep]
    simp only [Bind.bind, Except.bind]
    rw [ih (initial.push first) restOrdered nextBefore]
    simp [-Array.append_singleton, Array.push_eq_append, Array.append_assoc]

theorem array_checked_append_exact (entries initial : Array (Size × α))
    (ordered : entries.toList.Pairwise fun left right => left.1.bytes < right.1.bytes)
    (before : ∀ old ∈ initial, ∀ fresh ∈ entries, old.1.bytes < fresh.1.bytes) :
    forIn entries initial checked_append_step = .ok (initial ++ entries) := by
  rcases entries with ⟨entries⟩
  have separation : ∀ old ∈ initial, ∀ fresh ∈ entries, old.1.bytes < fresh.1.bytes := by
    intro old oldMember fresh freshMember
    exact before old oldMember fresh (by simpa using freshMember)
  simpa using list_checked_append_exact entries initial ordered separation


def pointer_payload (position : Size) (data : Array UInt8)
    (available : position.bytes.toNat + 8 ≤ data.size) : Vector UInt8 8 :=
  Vector.ofFn fun index =>
    if inside : index.val < 8 then data[position.bytes.toNat + index.val]'(by omega) else 0

def pointer_fragment_entry (position : Size) (prov : Prov) (bytes : Vector UInt8 8)
    (index : Nat) : Size × PointerFrag Prov :=
  (Size.ofBytes (position.bytes + UInt64.ofNat index), ⟨UInt8.ofNat index, prov, bytes⟩)

def selected_pointer_fragments (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (available : position.bytes.toNat + 8 ≤ data.size) :
    Array (Size × PointerFrag Prov) :=
  (((List.range 8).map (pointer_fragment_entry position prov (pointer_payload position data available))).filter
    (fun entry => inRange entry.1)).toArray

theorem filter_push_fold (entries : List α) (f : α → β) (predicate : β → Bool) (initial : Array β) :
    entries.foldl (fun acc entry => if predicate (f entry) then acc.push (f entry) else acc) initial =
      initial ++ ((entries.map f).filter predicate).toArray := by
  induction entries generalizing initial with
  | nil => simp
  | cons first rest ih =>
    by_cases selected : predicate (f first) <;>
      simp only [List.foldl_cons, List.map_cons, List.filter_cons, selected,
        Bool.false_eq_true, ↓reduceIte]
    all_goals rw [ih]
    all_goals simp [-Array.append_singleton, Array.push_eq_append, Array.append_assoc]

theorem pointer_fragments_exact (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (available : position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) :
    pointerFragments inRange position prov data (Size.ofBytes 8) =
      .ok (selected_pointer_fragments inRange position prov data available) := by
  have endFits : position.bytes.toNat + (8 : UInt64).toNat < 2 ^ 64 := by
    simp only [show (8 : UInt64).toNat = 8 from rfl]
    omega
  unfold pointerFragments
  unfold_provenance ".Miri.Memory.ProvenanceMap.ptrFragments"
  rw [DuplicatePrefix.size_add_ok position (Size.ofBytes 8) endFits]
  simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
    show ¬ ((8 : UInt64) > 8) from by decide, ↓reduceIte,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [show position.bytes.toNat + (8 : UInt64).toNat ≤ data.size from available,
    ↓reduceDIte]
  simp only [← apply_ite]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    show (8 : UInt64).toNat = 8 from rfl, Nat.sub_zero, Nat.add_zero, Nat.sub_self,
    Nat.div_one]
  change (match forIn (List.range 8) (#[] : Array (Size × PointerFrag Prov))
      (fun index acc => (Except.ok (.yield
        (if inRange (pointer_fragment_entry position prov (pointer_payload position data available) index).1
          then acc.push (pointer_fragment_entry position prov (pointer_payload position data available) index)
          else acc)) : Except ProvenanceMapError _)) with
    | .error error => (Except.error error : Except ProvenanceMapError (Array (Size × PointerFrag Prov)))
    | .ok value => Except.ok value) = _
  have loopEq := List.forIn_pure_yield_eq_foldl (m := Except ProvenanceMapError)
    (l := List.range 8)
    (fun index (acc : Array (Size × PointerFrag Prov)) =>
      if inRange (pointer_fragment_entry position prov (pointer_payload position data available) index).1
      then acc.push (pointer_fragment_entry position prov (pointer_payload position data available) index)
      else acc) #[]
  simp only [Pure.pure, Except.pure] at loopEq
  rw [loopEq]
  simp only [Pure.pure, Except.pure]
  rw [filter_push_fold (List.range 8)
    (pointer_fragment_entry position prov (pointer_payload position data available))
    (fun entry => inRange entry.1) #[]]
  simp [selected_pointer_fragments]


theorem pointer_fragment_position_nat (position : Size) (prov : Prov) (bytes : Vector UInt8 8)
    (index : Nat) (indexFits : index < 8)
    (positionFits : position.bytes.toNat + 8 < 18446744073709551616) :
    (pointer_fragment_entry position prov bytes index).1.bytes.toNat = position.bytes.toNat + index := by
  have indexFits64 : index < 18446744073709551616 := by omega
  have sumFits : position.bytes.toNat + index < 2 ^ 64 := by omega
  simp [pointer_fragment_entry, Size.ofBytes, UInt64.toNat_add,
    UInt64.toNat_ofNat_of_lt' indexFits64, Nat.mod_eq_of_lt sumFits]

theorem selected_pointer_fragments_ordered (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (available : position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) :
    (selected_pointer_fragments inRange position prov data available).toList.Pairwise
      (fun left right => left.1.bytes < right.1.bytes) := by
  have positionFits : position.bytes.toNat + 8 < 18446744073709551616 := by omega
  unfold selected_pointer_fragments
  simp only [List.toList_toArray]
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  apply (List.pairwise_lt_range (n := 8)).imp_of_mem
  intro left right leftMember rightMember ordered
  have leftBound := List.mem_range.mp leftMember
  have rightBound := List.mem_range.mp rightMember
  rw [UInt64.lt_iff_toNat_lt]
  rw [pointer_fragment_position_nat position prov _ left leftBound positionFits,
    pointer_fragment_position_nat position prov _ right rightBound positionFits]
  omega

theorem selected_pointer_fragment_bounds (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (available : position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616)
    (entry : Size × PointerFrag Prov)
    (member : entry ∈ selected_pointer_fragments inRange position prov data available) :
    position.bytes.toNat ≤ entry.1.bytes.toNat ∧ entry.1.bytes.toNat < position.bytes.toNat + 8 ∧
      inRange entry.1 = true := by
  have positionFits : position.bytes.toNat + 8 < 18446744073709551616 := by omega
  unfold selected_pointer_fragments at member
  simp only [List.mem_toArray, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨index, indexMember, rfl⟩, selected⟩ := member
  have indexBound := List.mem_range.mp indexMember
  rw [pointer_fragment_position_nat position prov _ index indexBound positionFits]
  exact ⟨by omega, by omega, selected⟩


def endpointPointers (self : ProvenanceMap Prov) (n : UInt64) : Array (Size × Prov) :=
  overlappingPointers self ⟨Size.ofBytes n, Size.ZERO⟩ (Size.ofBytes n)

theorem endpoint_geometry (self : ProvenanceMap Prov) (n : UInt64) (entry : Size × Prov)
    (member : entry ∈ endpointPointers self n) :
    entry.1.bytes.toNat < n.toNat ∧ n.toNat < entry.1.bytes.toNat + 8 := by
  have fits : n.toNat - 7 < 18446744073709551616 := by
    have bound : n.toNat < 18446744073709551616 := n.toNat_lt_size
    omega
  unfold endpointPointers overlappingPointers at member
  simp only [Array.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at member
  obtain ⟨_, lower, upper⟩ := member
  simp only [Size.ofBytes, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' fits] at lower upper
  omega

theorem endpoint_none_no_cross (self : ProvenanceMap Prov) (n : UInt64)
    (noneAtEnd : (endpointPointers self n)[0]? = none) : NoPointerCrosses self n := by
  have empty : endpointPointers self n = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    have bound := Array.getElem?_eq_none_iff.mp noneAtEnd
    omega
  have fits : n.toNat - 7 < 18446744073709551616 := by
    have bound : n.toNat < 18446744073709551616 := n.toNat_lt_size
    omega
  unfold endpointPointers overlappingPointers at empty
  have excludes := Array.filter_eq_empty_iff.mp empty
  intro entry member
  have outside := excludes entry member
  simp only [Bool.and_eq_true, decide_eq_true_eq, Size.ofBytes,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' fits] at outside
  omega

def FragmentsAvoidPointers (self : ProvenanceMap Prov) : Prop :=
  ∀ fragment ∈ self.byteFragments.getD #[], ∀ pointer ∈ self.ptrs,
    fragment.1.bytes.toNat < pointer.1.bytes.toNat ∨
      pointer.1.bytes.toNat + 8 ≤ fragment.1.bytes.toNat

theorem prefix_fragments_before_endpoint (self : ProvenanceMap Prov) (n : UInt64)
    (position : Size) (prov : Prov)
    (endpointMember : (position, prov) ∈ endpointPointers self n)
    (avoid : FragmentsAvoidPointers self) :
    ∀ fragment ∈ prefixFragments self n, fragment.1.bytes.toNat < position.bytes.toNat := by
  have geometry := endpoint_geometry self n (position, prov) endpointMember
  have pointerMember : (position, prov) ∈ self.ptrs := by
    exact mem_overlappingPointers self ⟨Size.ofBytes n, Size.ZERO⟩ (Size.ofBytes n)
      (position, prov) endpointMember
  intro fragment member
  unfold prefixFragments at member
  obtain ⟨sourceMember, beforeEnd⟩ := Array.mem_filter.mp member
  have disjoint := avoid fragment sourceMember (position, prov) pointerMember
  simp only [UInt64.lt_iff_toNat_lt, decide_eq_true_eq] at beforeEnd
  dsimp only at geometry disjoint
  omega


theorem prepare_prefix_endpoint (self : ProvenanceMap Prov) (n : UInt64)
    (position : Size) (prov : Prov) (data : Array UInt8)
    (endpointAtEnd : (endpointPointers self n)[0]? = some (position, prov))
    (available : position.bytes.toNat + 8 ≤ data.size)
    (avoid : FragmentsAvoidPointers self)
    (storageFits : data.size < 18446744073709551616) :
    let inRange : Size → Bool := fun pos => position.bytes ≤ pos.bytes && pos.bytes < n
    self.prepareCopy (allocRange Size.ZERO (Size.ofBytes n)) data (Size.ofBytes 8) =
      .ok ⟨prefixPointerEntries self n,
        prefixFragments self n ++ selected_pointer_fragments inRange position prov data available⟩ := by
  dsimp only
  let inRange : Size → Bool := fun pos => position.bytes ≤ pos.bytes && pos.bytes < n
  let incoming := selected_pointer_fragments inRange position prov data available
  have endpointMember := Array.mem_of_getElem? endpointAtEnd
  have geometry := endpoint_geometry self n (position, prov) endpointMember
  have beforeEnd : position.bytes < n := UInt64.lt_iff_toNat_lt.mpr geometry.1
  have prefixBefore := prefix_fragments_before_endpoint self n position prov endpointMember avoid
  have incomingOrdered := selected_pointer_fragments_ordered inRange position prov data available storageFits
  have separated : ∀ old ∈ prefixFragments self n, ∀ fresh ∈ incoming, old.1.bytes < fresh.1.bytes := by
    intro old oldMember fresh freshMember
    have oldBound := prefixBefore old oldMember
    have freshBound := selected_pointer_fragment_bounds inRange position prov data available storageFits fresh freshMember
    rw [UInt64.lt_iff_toNat_lt]
    omega
  have appendSuccess := array_checked_append_exact incoming (prefixFragments self n) incomingOrdered separated
  have fragmentsSuccess := pointer_fragments_exact inRange position prov data available storageFits
  unfold pointerFragments at fragmentsSuccess
  dsimp only [inRange, Size.ofBytes] at fragmentsSuccess
  dsimp only [incoming, inRange] at appendSuccess
  change forIn incoming (prefixFragments self n)
    (fun entry acc => checked_append_step entry acc) = _ at appendSuccess
  simp [checked_append_step, prefixFragments, Size.sub, Size.ZERO, Size.ofBytes,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at appendSuccess
  have endQuery : self.rangePtrs ⟨Size.ofBytes n, Size.ZERO⟩ (Size.ofBytes 8) =
      .ok (endpointPointers self n) :=
    range_ptrs_exact self _ (Size.ofBytes n) (zero_endpoint (Size.ofBytes n))
  unfold ProvenanceMap.prepareCopy
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  simp only [prefix_endpoint, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  dsimp only [allocRange]
  rw [range_ptrs_at_zero, endQuery]
  unfold_provenance ".Miri.Memory.ProvenanceMap.subtractSize"
  unfold ProvenanceMap.rangeBytes
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
  by_cases large : (8 : UInt64) ≤ n
  · have nonnegative : ¬ n < (7 : UInt64) := by
      simp [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at large ⊢
      omega
    simp [prefixPointerEntries, prefixFragments, large, nonnegative,
      endpointAtEnd, beforeEnd, fragmentsSuccess, appendSuccess, inRange, incoming,
      Size.ZERO, Size.ofBytes, Size.sub, AllocRange.endExclusive, AllocRange.end,
      Size.add, for_in_rebuild_entries, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · simp [prefixPointerEntries, prefixFragments, large,
      endpointAtEnd, beforeEnd, fragmentsSuccess, appendSuccess, inRange, incoming,
      Size.ZERO, Size.ofBytes, Size.sub, AllocRange.endExclusive, AllocRange.end,
      Size.add, for_in_rebuild_entries, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]


/-- Prefix preparation succeeds for general well-formed provenance, including
an actual whole pointer crossing the copy endpoint and existing byte fragments.
No operation-success or no-boundary-crossing premise is required. -/
theorem prepare_prefix_exists (self : ProvenanceMap Prov) (n : UInt64) (data : Array UInt8)
    (pointerBounds : ∀ entry ∈ self.ptrs, entry.1.bytes.toNat + 8 ≤ data.size)
    (avoid : FragmentsAvoidPointers self)
    (storageFits : data.size < 18446744073709551616) :
    ∃ snapshot, self.prepareCopy (allocRange Size.ZERO (Size.ofBytes n)) data (Size.ofBytes 8) =
      .ok snapshot := by
  cases atEnd : (endpointPointers self n)[0]? with
  | none =>
    have noCross := endpoint_none_no_cross self n atEnd
    exact ⟨_, prepare_prefix_no_cross self n data noCross⟩
  | some entry =>
    obtain ⟨position, prov⟩ := entry
    have member := Array.mem_of_getElem? atEnd
    have sourceMember := mem_overlappingPointers self ⟨Size.ofBytes n, Size.ZERO⟩ (Size.ofBytes n)
      (position, prov) member
    have available := pointerBounds (position, prov) sourceMember
    exact ⟨_, prepare_prefix_endpoint self n position prov data atEnd available avoid storageFits⟩


theorem prefix_pointer_offsets (self : ProvenanceMap Prov) (n : UInt64)
    (entry : Size × Prov) (member : entry ∈ prefixPointerEntries self n) :
    entry.1.bytes.toNat < n.toNat := by
  unfold prefixPointerEntries at member
  split at member
  · rename_i large
    have h7 : (7 : UInt64) ≤ n := by
      simp [UInt64.le_iff_toNat_le] at large ⊢
      omega
    have memberBound := (Array.mem_filter.mp member).2
    have upper := UInt64.le_iff_toNat_le.mp (UInt64.sub_le h7)
    simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at memberBound
    omega
  · simp at member

theorem prefix_pointer_count (self : ProvenanceMap Prov) (n : UInt64) :
    (prefixPointerEntries self n).size ≤ self.ptrs.size := by
  unfold prefixPointerEntries
  split
  · exact Array.size_filter_le
  · simp

theorem prefix_fragment_offsets (self : ProvenanceMap Prov) (n : UInt64)
    (entry : Size × PointerFrag Prov) (member : entry ∈ prefixFragments self n) :
    entry.1.bytes.toNat < n.toNat := by
  have upper := (Array.mem_filter.mp member).2
  simpa [UInt64.lt_iff_toNat_lt] using upper

theorem prefix_fragment_count (self : ProvenanceMap Prov) (n : UInt64) :
    (prefixFragments self n).size ≤ (self.byteFragments.getD #[]).size :=
  Array.size_filter_le

theorem selected_fragment_count (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (available : position.bytes.toNat + 8 ≤ data.size) :
    (selected_pointer_fragments inRange position prov data available).size ≤ 8 := by
  unfold selected_pointer_fragments
  simp only [List.size_toArray]
  have bound := List.length_filter_le (fun entry : Size × PointerFrag Prov => inRange entry.1)
    ((List.range 8).map (pointer_fragment_entry position prov (pointer_payload position data available)))
  simpa using bound

def SnapshotFits (snapshot : ProvenanceCopy Prov) (n : UInt64)
    (pointerCount fragmentCount : Nat) : Prop :=
  (∀ entry ∈ snapshot.ptrs, entry.1.bytes.toNat < n.toNat) ∧
  (∀ entry ∈ snapshot.byteFragments, entry.1.bytes.toNat < n.toNat) ∧
  snapshot.ptrs.size ≤ pointerCount ∧ snapshot.byteFragments.size ≤ fragmentCount + 8

theorem prepare_prefix_with_bounds (self : ProvenanceMap Prov) (n : UInt64) (data : Array UInt8)
    (pointerBounds : ∀ entry ∈ self.ptrs, entry.1.bytes.toNat + 8 ≤ data.size)
    (avoid : FragmentsAvoidPointers self)
    (storageFits : data.size < 18446744073709551616) :
    ∃ snapshot, self.prepareCopy (allocRange Size.ZERO (Size.ofBytes n)) data (Size.ofBytes 8) =
      .ok snapshot ∧ SnapshotFits snapshot n self.ptrs.size (self.byteFragments.getD #[]).size := by
  cases atEnd : (endpointPointers self n)[0]? with
  | none =>
    have noCross := endpoint_none_no_cross self n atEnd
    refine ⟨⟨prefixPointerEntries self n, prefixFragments self n⟩,
      prepare_prefix_no_cross self n data noCross, ?_⟩
    refine ⟨prefix_pointer_offsets self n, prefix_fragment_offsets self n,
      prefix_pointer_count self n, ?_⟩
    have count := prefix_fragment_count self n
    exact Nat.le_trans count (by omega)
  | some entry =>
    obtain ⟨position, prov⟩ := entry
    have member := Array.mem_of_getElem? atEnd
    have sourceMember := mem_overlappingPointers self ⟨Size.ofBytes n, Size.ZERO⟩ (Size.ofBytes n)
      (position, prov) member
    have available := pointerBounds (position, prov) sourceMember
    let inRange : Size → Bool := fun pos => position.bytes ≤ pos.bytes && pos.bytes < n
    let selected := selected_pointer_fragments inRange position prov data available
    refine ⟨⟨prefixPointerEntries self n, prefixFragments self n ++ selected⟩,
      prepare_prefix_endpoint self n position prov data atEnd available avoid storageFits, ?_⟩
    refine ⟨prefix_pointer_offsets self n, ?_, prefix_pointer_count self n, ?_⟩
    · intro entry entryMember
      rcases Array.mem_append.mp entryMember with old | fresh
      · exact prefix_fragment_offsets self n entry old
      · have selectedBound := selected_pointer_fragment_bounds inRange position prov data available storageFits entry fresh
        have inside := selectedBound.2.2
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at inside
        exact UInt64.lt_iff_toNat_lt.mp inside.2
    · have oldCount := prefix_fragment_count self n
      have newCount := selected_fragment_count inRange position prov data available
      simp only [Array.size_append]
      dsimp only [selected]
      omega


/-- Actual provenance preparation, destination clearing and insertion succeed
for adjacent prefix copying under structural storage invariants. -/
theorem prefix_copy_pipeline_exists (self : ProvenanceMap Prov) (n : UInt64)
    (data : Array UInt8)
    (pointerBounds : ∀ entry ∈ self.ptrs, entry.1.bytes.toNat + 8 ≤ data.size)
    (avoid : FragmentsAvoidPointers self)
    (storageFits : data.size < 18446744073709551616)
    (copyFits : n.toNat + n.toNat ≤ data.size)
    (pointerCountFits : self.ptrs.size < 18446744073709551616)
    (fragmentCountFits : (self.byteFragments.getD #[]).size + 8 < 18446744073709551616) :
    ∃ snapshot cleared updated,
      self.prepareCopy (allocRange Size.ZERO (Size.ofBytes n)) data (Size.ofBytes 8) = .ok snapshot ∧
      ProvenanceMap.clear (allocRange (Size.ofBytes n) (Size.ofBytes n)) data (Size.ofBytes 8) self = .ok () cleared ∧
      ProvenanceMap.applyCopy snapshot (allocRange (Size.ofBytes n) (Size.ofBytes n)) 1 cleared = .ok () updated := by
  obtain ⟨snapshot, prepared, pointerOffsets, fragmentOffsets, pointerCount, fragmentCount⟩ :=
    prepare_prefix_with_bounds self n data pointerBounds avoid storageFits
  have sumFits : n.toNat + n.toNat < 2 ^ 64 := by omega
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes n) n sumFits
  obtain ⟨cleared, clearedOk⟩ := clear_exists self _ _ data endpoint pointerBounds storageFits
  obtain ⟨updated, copied⟩ := apply_copy_once_exists snapshot (allocRange (Size.ofBytes n) (Size.ofBytes n))
    (by omega) (by omega)
    (by intro entry member; have bound := pointerOffsets entry member; change entry.1.bytes.toNat + n.toNat < 2 ^ 64; omega)
    (by intro entry member; have bound := fragmentOffsets entry member; change entry.1.bytes.toNat + n.toNat < 2 ^ 64; omega)
    cleared
  exact ⟨snapshot, cleared, updated, prepared, clearedOk, copied⟩

theorem ordered_entry_count (entries : Array (Size × α)) (capacity : Nat)
    (ordered : entries.toList.Pairwise (fun l r => l.1.bytes.toNat < r.1.bytes.toNat))
    (bounds : ∀ entry ∈ entries, entry.1.bytes.toNat < capacity) :
    entries.size ≤ capacity := by
  let offsets := entries.toList.map (fun entry => entry.1.bytes.toNat)
  have sorted : offsets.Pairwise (· < ·) := by
    exact List.pairwise_map.mpr ordered
  have unique : offsets.Nodup := sorted.imp (fun h => Nat.ne_of_lt h)
  have contained : offsets ⊆ List.range capacity := by
    intro offset member
    change offset ∈ entries.toList.map (fun entry => entry.1.bytes.toNat) at member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (bounds entry (by simpa using entryMember))
  have count := unique.length_le_of_subset contained
  simpa [offsets] using count

/-- Structural well-formedness of the stored pointer and fragment intervals.
It does not mention success of any memory operation. -/
structure WellFormed (self : ProvenanceMap Prov) (capacity : Nat) : Prop where
  pointerOrder : self.ptrs.toList.Pairwise (fun l r => l.1.bytes.toNat + 8 ≤ r.1.bytes.toNat)
  fragmentOrder : (self.byteFragments.getD #[]).toList.Pairwise (fun l r => l.1.bytes.toNat < r.1.bytes.toNat)
  pointerBounds : ∀ entry ∈ self.ptrs, entry.1.bytes.toNat + 8 ≤ capacity
  fragmentBounds : ∀ entry ∈ self.byteFragments.getD #[], entry.1.bytes.toNat < capacity
  fragmentsAvoidPointers : FragmentsAvoidPointers self


theorem WellFormed.pointer_count {self : ProvenanceMap Prov} {capacity : Nat}
    (valid : WellFormed self capacity) : self.ptrs.size ≤ capacity := by
  apply ordered_entry_count
  · exact (WellFormed.pointerOrder valid).imp (fun h => by omega)
  · intro entry member
    have bound := (WellFormed.pointerBounds valid) entry member
    omega

theorem WellFormed.fragment_count {self : ProvenanceMap Prov} {capacity : Nat}
    (valid : WellFormed self capacity) : (self.byteFragments.getD #[]).size ≤ capacity :=
  ordered_entry_count _ _ (WellFormed.fragmentOrder valid) (WellFormed.fragmentBounds valid)

theorem prefix_copy_well_formed_exists (self : ProvenanceMap Prov) (n : UInt64)
    (data : Array UInt8)
    (valid : WellFormed self data.size)
    (storageFits : data.size + 8 < 18446744073709551616)
    (copyFits : n.toNat + n.toNat ≤ data.size) :
    ∃ snapshot cleared updated,
      self.prepareCopy (allocRange Size.ZERO (Size.ofBytes n)) data (Size.ofBytes 8) = .ok snapshot ∧
      ProvenanceMap.clear (allocRange (Size.ofBytes n) (Size.ofBytes n)) data (Size.ofBytes 8) self = .ok () cleared ∧
      ProvenanceMap.applyCopy snapshot (allocRange (Size.ofBytes n) (Size.ofBytes n)) 1 cleared = .ok () updated := by
  apply prefix_copy_pipeline_exists self n data (WellFormed.pointerBounds valid) (WellFormed.fragmentsAvoidPointers valid) (by omega) copyFits
  · have count := valid.pointer_count
    omega
  · have count := valid.fragment_count
    omega

def shift_entry (base : Size) (entry : Size × α) : Size × α :=
  (Size.ofBytes (entry.1.bytes - base.bytes), entry.2)
def shift_entries (base : Size) (entries : Array (Size × α)) := entries.map (shift_entry base)
def subtract_offset (left right : Size) : Except ProvenanceMapError Size :=
  (Size.sub left right).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)

theorem subtract_offset_ok (left right : Size) (bounded : right.bytes ≤ left.bytes) :
    subtract_offset left right = .ok (Size.ofBytes (left.bytes - right.bytes)) := by
  simp [subtract_offset, Size.sub, Except.mapError, show ¬left.bytes < right.bytes from by simpa only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] using Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp bounded)]

def collect_entries (base : Size) (entries initial : Array (Size × α)) : Except ProvenanceMapError (Array (Size × α)) :=
  forIn entries initial fun entry acc => do
    let shifted ← subtract_offset entry.1 base
    pure (.yield (acc.push (shifted, entry.2)))

theorem collect_list_exact (base : Size) (entries : List (Size × α)) (initial : Array (Size × α))
    (lower : ∀ entry ∈ entries, base.bytes ≤ entry.1.bytes) :
    (forIn entries initial fun entry acc => do
      let shifted ← subtract_offset entry.1 base
      pure (.yield (acc.push (shifted, entry.2))) : Except ProvenanceMapError _) =
      .ok (initial ++ (entries.map (shift_entry base)).toArray) := by
  induction entries generalizing initial with
  | nil => simp [Pure.pure, Except.pure]
  | cons entry rest ih =>
    have head := lower entry (by simp)
    have tail : ∀ next ∈ rest, base.bytes ≤ next.1.bytes := fun next member => lower next (by simp [member])
    simp only [List.forIn_cons, subtract_offset_ok _ _ head, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have ihNext := ih (initial.push (Size.ofBytes (entry.1.bytes - base.bytes), entry.2)) tail
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ihNext
    rw [ihNext]
    simp [-Array.append_singleton, shift_entry, Array.push_eq_append, Array.append_assoc]

theorem collect_entries_exact (base : Size) (entries initial : Array (Size × α))
    (lower : ∀ entry ∈ entries, base.bytes ≤ entry.1.bytes) :
    collect_entries base entries initial = .ok (initial ++ shift_entries base entries) := by
  unfold collect_entries
  rw [← Array.forIn_toList]
  simpa [shift_entries, ← List.map_toArray] using collect_list_exact base entries.toList initial (by simpa using lower)

def checked_shift_step (base : Size) (entry : Size × α) (initial : Array (Size × α)) :
    Except ProvenanceMapError (ForInStep (Array (Size × α))) := do
  let shifted ← subtract_offset entry.1 base
  if !((initial.back?.map fun last => decide (last.1.bytes < shifted.bytes)).getD true) then
    throw .unsortedOrDuplicateKeys
  pure (.yield (initial.push (shifted, entry.2)))

theorem checked_shift_step_ok (base : Size) (entry : Size × α) (initial : Array (Size × α))
    (lower : base.bytes ≤ entry.1.bytes)
    (before : ∀ old ∈ initial, old.1.bytes < entry.1.bytes - base.bytes) :
    checked_shift_step base entry initial = .ok (.yield (initial.push (shift_entry base entry))) := by
  unfold checked_shift_step
  rw [subtract_offset_ok _ _ lower]
  cases last : initial.back? with
  | none => simp [last, shift_entry, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some old =>
    have ordered := before old (Array.mem_of_back? last)
    simp [last, shift_entry, ordered, Size.ofBytes, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem shift_nat (base : Size) (entry : Size × α) (lower : base.bytes ≤ entry.1.bytes) :
    (shift_entry base entry).1.bytes.toNat = entry.1.bytes.toNat - base.bytes.toNat := by
  simp [shift_entry, Size.ofBytes, UInt64.toNat_sub_of_le _ _ lower]

theorem shifted_lt (base : Size) (left : Size × α) (right : Size × β)
    (lower : base.bytes ≤ left.1.bytes) (ordered : left.1.bytes < right.1.bytes) :
    (shift_entry base left).1.bytes < (shift_entry base right).1.bytes := by
  have rightLower : base.bytes ≤ right.1.bytes := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  rw [UInt64.lt_iff_toNat_lt, shift_nat base left lower, shift_nat base right rightLower]
  have lowerNat := UInt64.le_iff_toNat_le.mp lower
  have orderNat := UInt64.lt_iff_toNat_lt.mp ordered
  omega

theorem collect_checked_list_exact (base : Size) (entries : List (Size × α)) (initial : Array (Size × α))
    (lower : ∀ entry ∈ entries, base.bytes ≤ entry.1.bytes)
    (ordered : entries.Pairwise (fun left right => left.1.bytes < right.1.bytes))
    (before : ∀ old ∈ initial, ∀ fresh ∈ entries, old.1.bytes < fresh.1.bytes - base.bytes) :
    forIn entries initial (checked_shift_step base) =
      .ok (initial ++ (entries.map (shift_entry base)).toArray) := by
  induction entries generalizing initial with
  | nil => simp [Pure.pure, Except.pure]
  | cons first rest ih =>
    obtain ⟨firstBefore, restOrdered⟩ := List.pairwise_cons.mp ordered
    have firstLower := lower first (by simp)
    have firstStep := checked_shift_step_ok base first initial firstLower
      (fun old member => before old member first (by simp))
    have nextBefore : ∀ old ∈ initial.push (shift_entry base first), ∀ fresh ∈ rest,
        old.1.bytes < fresh.1.bytes - base.bytes := by
      intro old member fresh freshMember
      rcases Array.mem_push.mp member with original | rfl
      · exact before old original fresh (by simp [freshMember])
      · exact shifted_lt base first fresh firstLower (firstBefore fresh freshMember)
    simp only [List.forIn_cons, firstStep, Bind.bind, Except.bind]
    rw [ih _ (by intro entry member; exact lower entry (by simp [member])) restOrdered nextBefore]
    simp [-Array.append_singleton, Array.push_eq_append, Array.append_assoc]

theorem collect_checked_entries_exact (base : Size) (entries initial : Array (Size × α))
    (lower : ∀ entry ∈ entries, base.bytes ≤ entry.1.bytes)
    (ordered : entries.toList.Pairwise (fun left right => left.1.bytes < right.1.bytes))
    (before : ∀ old ∈ initial, ∀ fresh ∈ entries, old.1.bytes < fresh.1.bytes - base.bytes) :
    forIn entries initial (checked_shift_step base) = .ok (initial ++ shift_entries base entries) := by
  rw [← Array.forIn_toList]
  simpa [shift_entries, ← List.map_toArray] using collect_checked_list_exact base entries.toList initial
    (by simpa using lower) ordered (by simpa using before)


def begin_stage (base finish : Size) (beginOpt : Option (Size × Prov)) (data : Array UInt8) :
    Except ProvenanceMapError (Array (Size × PointerFrag Prov)) := do
  match beginOpt with
  | none => return #[]
  | some (position, prov) =>
    let ptrEnd ← (Size.add position (Size.ofBytes 8)).mapError (ProvenanceMapError.memory ∘ MemoryError.sizeError)
    let fragmentEnd := if ptrEnd.bytes < finish.bytes then ptrEnd else finish
    if base.bytes < fragmentEnd.bytes then
      let fragments ← pointerFragments (fun pos => base.bytes ≤ pos.bytes && pos.bytes < fragmentEnd.bytes) position prov data (Size.ofBytes 8)
      collect_entries base fragments #[]
    else return #[]

def AbsoluteBounds (base finish : Size) (entries : Array (Size × α)) : Prop :=
  ∀ entry ∈ entries, base.bytes ≤ entry.1.bytes ∧ entry.1.bytes < finish.bytes

def BeginOrigin (beginOpt : Option (Size × Prov)) (entries : Array (Size × α)) : Prop :=
  ∀ entry ∈ entries, ∃ position prov, beginOpt = some (position, prov) ∧ entry.1.bytes.toNat < position.bytes.toNat + 8

theorem begin_stage_exists (base finish : Size) (beginOpt : Option (Size × Prov)) (data : Array UInt8)
    (bounds : ∀ position prov, beginOpt = some (position, prov) → position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616) :
    ∃ entries, begin_stage base finish beginOpt data = .ok (shift_entries base entries) ∧
      AbsoluteBounds base finish entries ∧ BeginOrigin beginOpt entries ∧ entries.size ≤ 8 := by
  cases beginOpt with
  | none => exact ⟨#[], by simp [begin_stage, shift_entries, Pure.pure, Except.pure], by simp [AbsoluteBounds], by simp [BeginOrigin], by simp⟩
  | some pair =>
    obtain ⟨position, prov⟩ := pair
    have available := bounds position prov rfl
    have endpoint := pointer_end_checked position data available storageFits
    let fragmentEnd := if position.bytes + 8 < finish.bytes then Size.ofBytes (position.bytes + 8) else finish
    let inRange : Size → Bool := fun pos => base.bytes ≤ pos.bytes && pos.bytes < fragmentEnd.bytes
    let entries := selected_pointer_fragments inRange position prov data available
    have selected := pointer_fragments_exact inRange position prov data available storageFits
    have entryBounds : ∀ entry ∈ entries, base.bytes ≤ entry.1.bytes ∧ entry.1.bytes < fragmentEnd.bytes := by
      intro entry member
      have inside := (selected_pointer_fragment_bounds inRange position prov data available storageFits entry member).2.2
      simpa only [inRange, Bool.and_eq_true, decide_eq_true_eq] using inside
    by_cases nonempty : base.bytes < fragmentEnd.bytes
    · refine ⟨entries, ?_, ?_, ?_, selected_fragment_count inRange position prov data available⟩
      · unfold begin_stage
        dsimp only
        rw [endpoint]
        simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        change (if base.bytes < fragmentEnd.bytes then _ else _) = _
        rw [if_pos nonempty]
        change (pointerFragments inRange position prov data (Size.ofBytes 8) >>= fun fragments => collect_entries base fragments #[]) = _
        rw [selected]
        simp only [Bind.bind, Except.bind]
        rw [collect_entries_exact base entries #[] (fun entry member => (entryBounds entry member).1)]
        simp
      · intro entry member
        have bound := entryBounds entry member
        refine ⟨bound.1, ?_⟩
        have endLe : fragmentEnd.bytes ≤ finish.bytes := by
          dsimp only [fragmentEnd]
          split <;> simp_all [Size.ofBytes, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] <;> omega
        simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
        omega
      · intro entry member
        exact ⟨position, prov, rfl, (selected_pointer_fragment_bounds inRange position prov data available storageFits entry member).2.1⟩
    · refine ⟨#[], ?_, by simp [AbsoluteBounds], by simp [BeginOrigin], by simp⟩
      unfold begin_stage
      dsimp only
      rw [endpoint]
      simp only [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      change (if base.bytes < fragmentEnd.bytes then _ else _) = _
      simp [nonempty, shift_entries, Pure.pure, Except.pure]


def end_stage (base finish : Size) (beginOpt endOpt : Option (Size × Prov))
    (data : Array UInt8) (initial : Array (Size × PointerFrag Prov)) :
    Except ProvenanceMapError (Array (Size × PointerFrag Prov)) := do
  match endOpt with
  | none => return initial
  | some (position, prov) =>
    if (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true then
      if position.bytes < base.bytes then throw .unsortedOrDuplicateKeys
      if position.bytes < finish.bytes then
        let fragments ← pointerFragments (fun pos => position.bytes ≤ pos.bytes && pos.bytes < finish.bytes) position prov data (Size.ofBytes 8)
        forIn fragments initial (checked_shift_step base)
      else return initial
    else return initial

theorem end_stage_exists (base finish : Size) (beginOpt endOpt : Option (Size × Prov))
    (data : Array UInt8) (initial : Array (Size × PointerFrag Prov))
    (initialBounds : AbsoluteBounds base finish initial)
    (bounds : ∀ position prov, endOpt = some (position, prov) → position.bytes.toNat + 8 ≤ data.size)
    (validStart : ∀ position prov, endOpt = some (position, prov) →
      (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true = true → base.bytes ≤ position.bytes)
    (before : ∀ position prov, endOpt = some (position, prov) →
      (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true = true →
      ∀ old ∈ initial, old.1.bytes < position.bytes)
    (storageFits : data.size < 18446744073709551616) :
    ∃ entries, end_stage base finish beginOpt endOpt data (shift_entries base initial) = .ok (shift_entries base entries) ∧
      AbsoluteBounds base finish entries ∧ entries.size ≤ initial.size + 8 := by
  cases endOpt with
  | none => exact ⟨initial, rfl, initialBounds, by omega⟩
  | some pair =>
    obtain ⟨position, prov⟩ := pair
    have available := bounds position prov rfl
    by_cases distinct : (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true = true
    · have lower := validStart position prov rfl distinct
      have notBehind : ¬ position.bytes < base.bytes := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega
      by_cases overlap : position.bytes < finish.bytes
      · let inRange : Size → Bool := fun pos => position.bytes ≤ pos.bytes && pos.bytes < finish.bytes
        let incoming := selected_pointer_fragments inRange position prov data available
        have selected := pointer_fragments_exact inRange position prov data available storageFits
        have incomingBounds : AbsoluteBounds base finish incoming := by
          intro entry member
          have inside := (selected_pointer_fragment_bounds inRange position prov data available storageFits entry member).2.2
          simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at inside
          refine ⟨?_, inside.2⟩
          simp only [UInt64.le_iff_toNat_le] at *; omega
        have order := selected_pointer_fragments_ordered inRange position prov data available storageFits
        have separated : ∀ old ∈ shift_entries base initial, ∀ fresh ∈ incoming,
            old.1.bytes < fresh.1.bytes - base.bytes := by
          intro old oldMember fresh freshMember
          obtain ⟨original, originalMember, rfl⟩ := Array.mem_map.mp oldMember
          have originalLower := (initialBounds original originalMember).1
          have oldBefore := before position prov rfl distinct original originalMember
          have freshBound := selected_pointer_fragment_bounds inRange position prov data available storageFits fresh freshMember
          have ordered : original.1.bytes < fresh.1.bytes := by
            simp only [UInt64.lt_iff_toNat_lt] at *
            omega
          exact shifted_lt base original fresh originalLower ordered
        have appended := collect_checked_entries_exact base incoming (shift_entries base initial)
          (fun entry member => (incomingBounds entry member).1) order separated
        refine ⟨initial ++ incoming, ?_, ?_, ?_⟩
        · unfold end_stage
          dsimp only
          simp only [distinct, Bool.true_eq, ↓reduceIte, notBehind, overlap]
          rw [selected]
          simp only [Bind.bind, Except.bind]
          rw [appended]
          simp [shift_entries, Array.map_append]
        · intro entry member
          rcases Array.mem_append.mp member with old | fresh
          · exact initialBounds entry old
          · exact incomingBounds entry fresh
        · have count := selected_fragment_count inRange position prov data available
          simp only [Array.size_append]
          dsimp only [incoming]
          omega
      · exact ⟨initial, by simp [end_stage, distinct, notBehind, overlap, Pure.pure, Except.pure], initialBounds, by omega⟩
    · exact ⟨initial, by simp [end_stage, distinct, Pure.pure, Except.pure], initialBounds, by omega⟩


theorem pairwise_intervals_disjoint (entries : List (Size × α))
    (ordered : entries.Pairwise (fun l r => l.1.bytes.toNat + 8 ≤ r.1.bytes.toNat))
    (left right : Size × α) (leftMember : left ∈ entries) (rightMember : right ∈ entries) :
    left = right ∨ left.1.bytes.toNat + 8 ≤ right.1.bytes.toNat ∨ right.1.bytes.toNat + 8 ≤ left.1.bytes.toNat := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail ih =>
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (headBefore right rightTail))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact Or.inr (Or.inr (headBefore left leftTail))
      · exact ih tailOrdered leftTail rightTail

theorem endpoint_member_iff (self : ProvenanceMap Prov) (position : Size) (entry : Size × Prov) :
    entry ∈ endpointPointers self position.bytes ↔
      entry ∈ self.ptrs ∧ entry.1.bytes.toNat < position.bytes.toNat ∧ position.bytes.toNat < entry.1.bytes.toNat + 8 := by
  have fits : position.bytes.toNat - 7 < 18446744073709551616 := by
    have bounded : position.bytes.toNat < 18446744073709551616 := position.bytes.toNat_lt_size
    omega
  unfold endpointPointers overlappingPointers
  simp only [Array.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Size.ofBytes, Size.ZERO,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  simp only [UInt64.toNat_ofNat_of_lt' fits]
  constructor
  · rintro ⟨member, lower, upper⟩
    exact ⟨member, upper, by omega⟩
  · rintro ⟨member, upper, lower⟩
    exact ⟨member, by omega, upper⟩

theorem endpoint_begin_end_order (self : ProvenanceMap Prov) (capacity : Nat)
    (valid : WellFormed self capacity) (base finish : Size)
    (rangeOrder : base.bytes ≤ finish.bytes)
    (position : Size) (prov : Prov)
    (endAt : (endpointPointers self finish.bytes)[0]? = some (position, prov))
    (distinct : (((endpointPointers self base.bytes)[0]?).map fun (begin, _) => begin.bytes != position.bytes).getD true = true) :
    base.bytes ≤ position.bytes ∧
      (∀ begin beginProv, (endpointPointers self base.bytes)[0]? = some (begin, beginProv) →
        begin.bytes.toNat + 8 ≤ position.bytes.toNat) := by
  have endMember := Array.mem_of_getElem? endAt
  have endFacts := (endpoint_member_iff self finish (position, prov)).mp endMember
  cases beginAt : (endpointPointers self base.bytes)[0]? with
  | none =>
    have noCross := endpoint_none_no_cross self base.bytes beginAt
    have placement := noCross (position, prov) endFacts.1
    refine ⟨?_, ?_⟩
    · simp only [UInt64.le_iff_toNat_le] at rangeOrder ⊢
      dsimp only at endFacts placement
      omega
    · intro begin beginProv impossible
      simp [beginAt] at impossible
  | some pair =>
    obtain ⟨begin, beginProv⟩ := pair
    have beginMember := Array.mem_of_getElem? beginAt
    have beginFacts := (endpoint_member_iff self base (begin, beginProv)).mp beginMember
    have unequal : begin.bytes ≠ position.bytes := by simpa [beginAt] using distinct
    have disjoint := pairwise_intervals_disjoint self.ptrs.toList (WellFormed.pointerOrder valid)
      (begin, beginProv) (position, prov) (by simpa using beginFacts.1) (by simpa using endFacts.1)
    have before : begin.bytes.toNat + 8 ≤ position.bytes.toNat := by
      rcases disjoint with equal | before | after
      · have same := congrArg (fun entry : Size × Prov => entry.1.bytes) equal
        exact False.elim (unequal same)
      · exact before
      · simp only [UInt64.le_iff_toNat_le] at rangeOrder
        dsimp only at beginFacts endFacts after
        omega
    refine ⟨?_, ?_⟩
    · simp only [UInt64.le_iff_toNat_le]
      dsimp only at beginFacts
      omega
    · intro other otherProv otherAt
      have equal : (begin, beginProv) = (other, otherProv) := Option.some.inj otherAt
      cases equal
      exact before

def whole_entries (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64) : Array (Size × Prov) :=
  if (8 : UInt64) ≤ n then self.ptrs.filter (fun entry => base.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes - 7) else #[]
def old_entries (self : ProvenanceMap Prov) (base finish : Size) : Array (Size × PointerFrag Prov) :=
  (self.byteFragments.getD #[]).filter (fun entry => base.bytes ≤ entry.1.bytes && entry.1.bytes < finish.bytes)

theorem old_entry_bounds (self : ProvenanceMap Prov) (base finish : Size) : AbsoluteBounds base finish (old_entries self base finish) := by
  intro entry member
  have selected := (Array.mem_filter.mp member).2
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using selected

theorem old_entries_before_endpoint (self : ProvenanceMap Prov) (base finish : Size)
    (position : Size) (prov : Prov)
    (endAt : (endpointPointers self finish.bytes)[0]? = some (position, prov))
    (avoid : FragmentsAvoidPointers self) :
    ∀ entry ∈ old_entries self base finish, entry.1.bytes < position.bytes := by
  have endFacts := (endpoint_member_iff self finish (position, prov)).mp (Array.mem_of_getElem? endAt)
  intro entry member
  have sourceMember := (Array.mem_filter.mp member).1
  have inside := (old_entry_bounds self base finish entry member).2
  have disjoint := avoid entry sourceMember (position, prov) endFacts.1
  simp only [UInt64.lt_iff_toNat_lt] at inside ⊢
  dsimp only at endFacts disjoint
  omega


def whole_stage (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64) :
    Except ProvenanceMapError (Array (Size × Prov)) := do
  if (8 : UInt64) ≤ n then
    let adjustedEnd ← subtract_offset finish (Size.ofBytes 7)
    collect_entries base (self.ptrs.filter (fun entry => base.bytes ≤ entry.1.bytes && entry.1.bytes < adjustedEnd.bytes)) #[]
  else return #[]

theorem whole_stage_exact (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64)
    (finishNat : finish.bytes.toNat = base.bytes.toNat + n.toNat) :
    whole_stage self base finish n = .ok (shift_entries base (whole_entries self base finish n)) := by
  by_cases large : (8 : UInt64) ≤ n
  · have enough : (7 : UInt64) ≤ finish.bytes := by
      simp only [UInt64.le_iff_toNat_le, show (8 : UInt64).toNat = 8 from rfl, show (7 : UInt64).toNat = 7 from rfl] at large ⊢
      omega
    have lower : ∀ entry ∈ whole_entries self base finish n, base.bytes ≤ entry.1.bytes := by
      intro entry member
      simp only [whole_entries, large, ↓reduceIte, Array.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at member
      exact member.2.1
    unfold whole_stage
    rw [if_pos large]
    have adjusted := subtract_offset_ok finish (Size.ofBytes 7) enough
    rw [adjusted]
    simp only [Bind.bind, Except.bind]
    have collected := collect_entries_exact base (whole_entries self base finish n) #[] lower
    simpa only [whole_entries, large, ↓reduceIte, Size.ofBytes, Array.empty_append] using collected
  · simp [whole_stage, whole_entries, large, shift_entries, Pure.pure, Except.pure]

theorem whole_entries_bounds (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64)
    (finishNat : finish.bytes.toNat = base.bytes.toNat + n.toNat) :
    AbsoluteBounds base finish (whole_entries self base finish n) := by
  intro entry member
  unfold whole_entries at member
  split at member
  · rename_i large
    obtain ⟨_, lower, upper⟩ := by simpa only [Array.mem_filter, Bool.and_eq_true, decide_eq_true_eq] using member
    refine ⟨lower, ?_⟩
    have enough : (7 : UInt64) ≤ finish.bytes := by
      simp only [UInt64.le_iff_toNat_le, show (8 : UInt64).toNat = 8 from rfl, show (7 : UInt64).toNat = 7 from rfl] at large ⊢
      omega
    have endLe := UInt64.sub_le enough
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at upper endLe ⊢
    omega
  · simp at member

theorem whole_entries_count (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64) :
    (whole_entries self base finish n).size ≤ self.ptrs.size := by
  unfold whole_entries
  split
  · exact Array.size_filter_le
  · simp

theorem range_bytes_exact (self : ProvenanceMap Prov) (range : AllocRange) (finish : Size)
    (endpoint : range.endExclusive = .ok finish) :
    self.rangeBytes range = .ok (old_entries self range.start finish) := by
  unfold ProvenanceMap.rangeBytes
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
  cases fragments : self.byteFragments <;>
    simp [endpoint, old_entries, fragments, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

def prepare_stages (self : ProvenanceMap Prov) (range : AllocRange) (data : Array UInt8) :
    Except ProvenanceMapError (ProvenanceCopy Prov) := do
  let finish ← range.endExclusive.mapError ProvenanceMapError.memory
  let ptrs ← whole_stage self range.start finish range.size.bytes
  let beginOpt := (← self.rangePtrs (allocRange range.start Size.ZERO) (Size.ofBytes 8))[0]?
  let endOpt := (← self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8))[0]?
  if beginOpt.isSome || endOpt.isSome || self.byteFragments.isSome then
    let initial ← begin_stage range.start finish beginOpt data
    let old ← self.rangeBytes range
    let middle ← collect_entries range.start old initial
    let bytes ← end_stage range.start finish beginOpt endOpt data middle
    return ⟨ptrs, bytes⟩
  else return ⟨ptrs, #[]⟩

theorem except_bind_if (p : Prop) [Decidable p] (yes no : Except ε α) (next : α → Except ε β) :
    ((if p then yes else no) >>= next) = (if p then yes >>= next else no >>= next) := by
  split <;> rfl

theorem except_bind_option (opt : Option α) (noneCase : Except ε β) (someCase : α → Except ε β)
    (next : β → Except ε γ) :
    ((match opt with | none => noneCase | some value => someCase value) >>= next) =
      (match opt with | none => noneCase >>= next | some value => someCase value >>= next) := by
  cases opt <;> rfl

theorem except_bind_option_pair (opt : Option (α × β)) (noneCase : Except ε γ)
    (someCase : α → β → Except ε γ) (next : γ → Except ε δ) :
    ((match opt with | none => noneCase | some (a,b) => someCase a b) >>= next) =
      (match opt with | none => noneCase >>= next | some (a,b) => someCase a b >>= next) := by
  cases opt with
  | none => rfl
  | some pair => cases pair; rfl

theorem except_error_bind (error : ε) (next : α → Except ε β) :
    ((Except.error error : Except ε α) >>= next) = .error error := rfl

theorem except_bind_option_pair_first (opt : Option (α × β)) (noneCase : Except ε γ)
    (someCase : α → β → Except ε γ) (next : γ → Except ε δ) :
    ((match opt with | some (a,b) => someCase a b | _ => noneCase) >>= next) =
      (match opt with | some (a,b) => someCase a b >>= next | _ => noneCase >>= next) := by
  cases opt with
  | none => rfl
  | some pair => cases pair; rfl

theorem option_pair_none_iff (opt : Option (α × β)) :
    (∀ a b, opt = some (a,b) → False) ↔ opt = none := by
  cases opt with
  | none => simp
  | some pair => obtain ⟨a,b⟩ := pair; simp

theorem prepare_stages_exact (self : ProvenanceMap Prov) (range : AllocRange) (data : Array UInt8) :
    self.prepareCopy range data (Size.ofBytes 8) = prepare_stages self range data := by
  unfold ProvenanceMap.prepareCopy prepare_stages whole_stage begin_stage end_stage collect_entries checked_shift_step subtract_offset
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEnd"
  unfold_provenance ".Miri.Memory.ProvenanceMap.subtractSize"
  unfold_provenance ".Miri.Memory.ProvenanceMap.rangeEntries"
  simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
    show (8 : UInt64) - 1 = 7 from rfl, show ((8 : UInt64) == 0) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  unfold pointerFragments
  simp only [except_bind_if, except_bind_option_pair_first, except_bind_option_pair, except_bind_option, bind_assoc, pure_bind, throw, throwThe, MonadExceptOf.throw, except_error_bind]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals repeat' (first | rfl | (split <;> try simp_all only [option_pair_none_iff]))


theorem shifted_absolute_bounds (base finish : Size) (n : UInt64) (entries : Array (Size × α))
    (bounds : AbsoluteBounds base finish entries)
    (finishNat : finish.bytes.toNat = base.bytes.toNat + n.toNat) :
    ∀ entry ∈ shift_entries base entries, entry.1.bytes.toNat < n.toNat := by
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := Array.mem_map.mp member
  have inside := bounds original originalMember
  rw [shift_nat base original inside.1]
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at inside
  omega

def IntervalSnapshotFits (snapshot : ProvenanceCopy Prov) (n : UInt64)
    (pointerCount fragmentCount : Nat) : Prop :=
  (∀ entry ∈ snapshot.ptrs, entry.1.bytes.toNat < n.toNat) ∧
  (∀ entry ∈ snapshot.byteFragments, entry.1.bytes.toNat < n.toNat) ∧
  snapshot.ptrs.size ≤ pointerCount ∧ snapshot.byteFragments.size ≤ fragmentCount + 16

theorem prepare_interval_with_bounds (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64)
    (data : Array UInt8) (valid : WellFormed self data.size)
    (storageFits : data.size < 18446744073709551616)
    (endpoint : (allocRange base (Size.ofBytes n)).endExclusive = .ok finish)
    (finishNat : finish.bytes.toNat = base.bytes.toNat + n.toNat) :
    ∃ snapshot,
      self.prepareCopy (allocRange base (Size.ofBytes n)) data (Size.ofBytes 8) = .ok snapshot ∧
      IntervalSnapshotFits snapshot n self.ptrs.size (self.byteFragments.getD #[]).size := by
  let beginOpt := (endpointPointers self base.bytes)[0]?
  let endOpt := (endpointPointers self finish.bytes)[0]?
  have baseQuery : self.rangePtrs (allocRange base Size.ZERO) (Size.ofBytes 8) = .ok (endpointPointers self base.bytes) := by
    exact range_ptrs_exact self _ base (zero_endpoint base)
  have endQuery : self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8) = .ok (endpointPointers self finish.bytes) := by
    exact range_ptrs_exact self _ finish (zero_endpoint finish)
  have rangeOrder : base.bytes ≤ finish.bytes := by
    simp only [UInt64.le_iff_toNat_le]
    omega
  have beginBounds : ∀ position prov, beginOpt = some (position, prov) → position.bytes.toNat + 8 ≤ data.size := by
    intro position prov atBegin
    have member := Array.mem_of_getElem? atBegin
    exact WellFormed.pointerBounds valid (position, prov)
      ((endpoint_member_iff self base (position, prov)).mp member).1
  obtain ⟨beginEntries, beginOk, beginInside, beginOrigin, beginCount⟩ :=
    begin_stage_exists base finish beginOpt data beginBounds storageFits
  let old := old_entries self base finish
  let middle := beginEntries ++ old
  have middleInside : AbsoluteBounds base finish middle := by
    intro entry member
    rcases Array.mem_append.mp member with fromBegin | fromOld
    · exact beginInside entry fromBegin
    · exact old_entry_bounds self base finish entry fromOld
  have endBounds : ∀ position prov, endOpt = some (position, prov) → position.bytes.toNat + 8 ≤ data.size := by
    intro position prov atEnd
    exact WellFormed.pointerBounds valid (position, prov)
      ((endpoint_member_iff self finish (position, prov)).mp (Array.mem_of_getElem? atEnd)).1
  have distinctOrder : ∀ position prov, endOpt = some (position, prov) →
      (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true = true →
      base.bytes ≤ position.bytes ∧ (∀ begin beginProv, beginOpt = some (begin, beginProv) → begin.bytes.toNat + 8 ≤ position.bytes.toNat) := by
    intro position prov atEnd distinct
    exact endpoint_begin_end_order self data.size valid base finish rangeOrder position prov atEnd distinct
  have middleBefore : ∀ position prov, endOpt = some (position, prov) →
      (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true = true →
      ∀ entry ∈ middle, entry.1.bytes < position.bytes := by
    intro position prov atEnd distinct entry member
    rcases Array.mem_append.mp member with fromBegin | fromOld
    · obtain ⟨begin, beginProv, atBegin, upper⟩ := beginOrigin entry fromBegin
      have before := (distinctOrder position prov atEnd distinct).2 begin beginProv atBegin
      simp only [UInt64.lt_iff_toNat_lt]
      omega
    · exact old_entries_before_endpoint self base finish position prov atEnd
        (WellFormed.fragmentsAvoidPointers valid) entry fromOld
  obtain ⟨endEntries, endOk, endInside, endCount⟩ := end_stage_exists base finish beginOpt endOpt data middle
    middleInside endBounds (fun position prov atEnd distinct => (distinctOrder position prov atEnd distinct).1) middleBefore storageFits
  have wholeOk := whole_stage_exact self base finish n finishNat
  have wholeInside := whole_entries_bounds self base finish n finishNat
  have wholeCount := whole_entries_count self base finish n
  have rangeBytes := range_bytes_exact self _ finish endpoint
  have collectOld := collect_entries_exact base old (shift_entries base beginEntries)
    (fun entry member => (old_entry_bounds self base finish entry member).1)
  have collectedMiddle : collect_entries base old (shift_entries base beginEntries) = .ok (shift_entries base middle) := by
    simpa [middle, shift_entries, Array.map_append] using collectOld
  by_cases present : beginOpt.isSome || endOpt.isSome || self.byteFragments.isSome
  · refine ⟨⟨shift_entries base (whole_entries self base finish n), shift_entries base endEntries⟩, ?_, ?_⟩
    · rw [prepare_stages_exact]
      unfold prepare_stages
      simp only [endpoint, Except.mapError, Bind.bind, Except.bind]
      change (whole_stage self base finish n >>= _) = _
      rw [wholeOk]
      dsimp only [allocRange]
      change (self.rangePtrs (allocRange base Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [baseQuery]
      simp only [Bind.bind, Except.bind]
      change (self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [endQuery]
      simp only [Bind.bind, Except.bind]
      change (if beginOpt.isSome || endOpt.isSome || self.byteFragments.isSome then _ else _) = _
      rw [if_pos present, beginOk]
      simp only [Bind.bind, Except.bind]
      change (self.rangeBytes (allocRange base (Size.ofBytes n)) >>= _) = _
      rw [rangeBytes]
      simp only [Bind.bind, Except.bind]
      change (collect_entries base old (shift_entries base beginEntries) >>= _) = _
      rw [collectedMiddle]
      simp only [Bind.bind, Except.bind]
      change (end_stage base finish beginOpt endOpt data (shift_entries base middle) >>= _) = _
      rw [endOk]
      rfl
    · refine ⟨shifted_absolute_bounds base finish n _ wholeInside finishNat,
        shifted_absolute_bounds base finish n _ endInside finishNat, ?_, ?_⟩
      · simpa [shift_entries] using wholeCount
      · have oldCount : old.size ≤ (self.byteFragments.getD #[]).size := Array.size_filter_le
        simp only [shift_entries, Array.size_map]
        dsimp only [middle] at endCount
        simp only [Array.size_append] at endCount
        omega
  · refine ⟨⟨shift_entries base (whole_entries self base finish n), #[]⟩, ?_, ?_⟩
    · rw [prepare_stages_exact]
      unfold prepare_stages
      simp only [endpoint, Except.mapError, Bind.bind, Except.bind]
      change (whole_stage self base finish n >>= _) = _
      rw [wholeOk]
      dsimp only [allocRange]
      change (self.rangePtrs (allocRange base Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [baseQuery]
      simp only [Bind.bind, Except.bind]
      change (self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [endQuery]
      simp only [Bind.bind, Except.bind]
      change (if beginOpt.isSome || endOpt.isSome || self.byteFragments.isSome then _ else _) = _
      simp [present, Pure.pure, Except.pure]
    · refine ⟨shifted_absolute_bounds base finish n _ wholeInside finishNat, by simp, ?_, by simp⟩
      simpa [shift_entries] using wholeCount

theorem interval_copy_well_formed_exists (self : ProvenanceMap Prov) (base : Size) (n : UInt64)
    (data : Array UInt8) (valid : WellFormed self data.size)
    (storageFits : data.size + 16 < 18446744073709551616)
    (copyFits : base.bytes.toNat + n.toNat + n.toNat ≤ data.size) :
    let destination := Size.ofBytes (base.bytes + n)
    ∃ snapshot cleared updated,
      self.prepareCopy (allocRange base (Size.ofBytes n)) data (Size.ofBytes 8) = .ok snapshot ∧
      ProvenanceMap.clear (allocRange destination (Size.ofBytes n)) data (Size.ofBytes 8) self = .ok () cleared ∧
      ProvenanceMap.applyCopy snapshot (allocRange destination (Size.ofBytes n)) 1 cleared = .ok () updated := by
  dsimp only
  let destination := Size.ofBytes (base.bytes + n)
  have firstFits : base.bytes.toNat + n.toNat < 2 ^ 64 := by omega
  have destinationNat : destination.bytes.toNat = base.bytes.toNat + n.toNat := by
    simp [destination, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt firstFits]
  have sourceEnd := DuplicatePrefix.source_end base n firstFits
  obtain ⟨snapshot, prepared, pointerOffsets, fragmentOffsets, pointerCount, fragmentCount⟩ :=
    prepare_interval_with_bounds self base destination n data valid (by omega) sourceEnd destinationNat
  have lastFits : destination.bytes.toNat + n.toNat < 2 ^ 64 := by omega
  have destinationEnd := DuplicatePrefix.source_end destination n lastFits
  obtain ⟨cleared, clearedOk⟩ := clear_exists self _ _ data destinationEnd (WellFormed.pointerBounds valid) (by omega)
  have totalPointers := WellFormed.pointer_count valid
  have totalFragments := WellFormed.fragment_count valid
  obtain ⟨updated, applied⟩ := apply_copy_once_exists snapshot (allocRange destination (Size.ofBytes n))
    (by omega) (by omega)
    (by intro entry member; have bound := pointerOffsets entry member; change entry.1.bytes.toNat + destination.bytes.toNat < 2 ^ 64; omega)
    (by intro entry member; have bound := fragmentOffsets entry member; change entry.1.bytes.toNat + destination.bytes.toNat < 2 ^ 64; omega)
    cleared
  exact ⟨snapshot, cleared, updated, prepared, clearedOk, applied⟩


end DuplicatePrefix.ProvenanceCopy

#print axioms DuplicatePrefix.ProvenanceCopy.prepare_prefix_no_cross
#print axioms DuplicatePrefix.ProvenanceCopy.pointer_fragments_exist
#print axioms DuplicatePrefix.ProvenanceCopy.apply_copy_once_exists
#print axioms DuplicatePrefix.ProvenanceCopy.clear_exists

#print axioms DuplicatePrefix.ProvenanceCopy.prepare_prefix_exists
#print axioms DuplicatePrefix.ProvenanceCopy.prepare_prefix_endpoint

#print axioms DuplicatePrefix.ProvenanceCopy.prepare_prefix_with_bounds

#print axioms DuplicatePrefix.ProvenanceCopy.prefix_copy_pipeline_exists

#print axioms DuplicatePrefix.ProvenanceCopy.prefix_copy_well_formed_exists

#print axioms DuplicatePrefix.ProvenanceCopy.prepare_interval_with_bounds
#print axioms DuplicatePrefix.ProvenanceCopy.interval_copy_well_formed_exists
