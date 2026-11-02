import empty_function.ConcreteProtection

/-! Current non-data registry branches, without assuming an operational lookup succeeds. -/
namespace EmptyFunction.NondataProtection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-- Disjoint family from live bytes and latent data. Earlier non-data registry
entries may shadow the named raw entry, as in the actual metadata precedence. -/
inductive Registry (before : State) (id : AllocId) : Prop where
  | function (noLive : before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (present : before.machine.memory.hasFunctionPointer id = true)
  | vaList (noLive : before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (present : before.machine.memory.hasVaListId id = true)
  | global (noLive : before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (entry : GlobalAllocation) (present : before.machine.memory.findGlobal? id = some entry)
      (notMemory : entry.kind ≠ .memory) (notStatic : entry.kind ≠ .static)
  | dead (noLive : before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (noGlobal : before.machine.memory.findGlobal? id = none)
      (entry : DeadAllocation) (present : before.machine.memory.dead.find? (fun row => row.allocId == id) = some entry)

 theorem classification (before : State) (id : AllocId) (registry : Registry before id) :
    ∃ info, before.machine.memory.getAllocInfo id = .ok info ∧ info.kind ≠ .liveData := by
  have noLive : before.machine.memory.live.find? (fun row => row.1 == id) = none := by
    cases registry <;> assumption
  unfold MemoryState.getAllocInfo
  simp only [noLive]
  cases fn : before.machine.memory.hasFunctionPointer id with
  | true => exact ⟨_,rfl,by intro impossible; cases impossible⟩
  | false =>
    cases va : before.machine.memory.hasVaListId id with
    | true =>
      unfold MemoryState.hasVaListId at va
      exact ⟨⟨Size.ZERO,Align.ONE,.vaList,.Not⟩,by simp [fn,va,Except.pure]; rfl,by decide⟩
    | false =>
      have vaRaw := va
      unfold MemoryState.hasVaListId at va
      simp only [fn,va,Bool.false_eq_true,↓reduceIte]
      cases registry with
      | function _ present => simp [fn] at present
      | vaList _ present => rw [vaRaw] at present; contradiction
      | global _ entry present notMemory notStatic =>
        simp only [present]
        cases kind : entry.kind <;> simp_all [Except.pure] <;> exact ⟨_,rfl,by intro impossible; cases impossible⟩
      | dead _ noGlobal entry present =>
        exact ⟨⟨entry.size,entry.align,.dead,.Not⟩,by simp [noGlobal,present]; rfl,by intro impossible; cases impossible⟩

 theorem selected (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag)) :
    ∃ base, p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
  cases destination.pointer with
  | integer integer => rw [encoding] at integer; contradiction
  | wildcard wildcard mode tables selected => rw [encoding] at wildcard; cases Option.some.inj wildcard
  | concrete supplied suppliedTag base tables concrete cached backing parent latent =>
    have pair : supplied = id ∧ suppliedTag = tag := by simpa using concrete.symm.trans encoding
    rcases pair with ⟨rfl,rfl⟩
    exact ⟨base,cached⟩

def protectedMachine (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (tracker : MachineHooks.BorrowState) (room : tracker.global.nextPointerTag.value < 18446744073709551615) :=
  UnitRetag.registeredMachine (UnitRetag.allocatedMachine machine tracker room)
    (UnitRetag.allocatedTracker tracker room) tracker.global.nextPointerTag

 theorem protect (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition)
    (destination : InputDraft.MemoryDestination s p input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (registry : Registry p.before id)
    (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses) :
    TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
      (LocalUnit.current p.before.stack.frames frame machine) =
      .ok () (LocalUnit.current p.before.stack.frames
        (UnitRetag.registeredFrame frame {} id input.tracker.global.nextPointerTag)
        (protectedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))) := by
  obtain ⟨base,cached⟩ := selected s p input destination id tag encoding
  obtain ⟨info,classified,nondata⟩ := classification p.before id registry
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨resolve,_,_⟩ := ConcreteProtection.bindings s metadata capacity
  have ptr : destination.place.mplace.ptr = Pointer.new (some (.concrete id tag))
      (Size.ofBytes destination.place.mplace.ptr.offset.bytes) := by
    cases pointerEq : destination.place.mplace.ptr with
    | mk offset provenance =>
      simp_all [Pointer.new]
      cases offset
      rfl
  have size : s.cfg.retag.sizeAndAlign destination.place = pure (some (Size.ZERO,Align.ONE)) := by
    have sized : destination.place.layout.layout.isSized = true := by
      rw [destination.layout]; exact metadata.unitSized
    simpa only [destination.layout,metadata.unitSize,metadata.unitAlign] using
      dictionaries.sizeAndAlign destination.place sized
  have unitLayout : localMemoryLayout destination.place.layout =
      ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some destination.place.layout.ty⟩ := by
    simp [localMemoryLayout,destination.layout,metadata.unitSize,metadata.unitAlign,metadata.unitBackend]
  have target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.cfg.access.runtime.pointerSize := by
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  have result := UnitRetag.protect_then_release_nondata_concrete s.cfg.retag s.limits.retag destination.place
    p.before.stack.frames frame machine input.tracker enabled frameBorrow
    (ConcreteProtection.tag_room s p input resources) input.world.globals
    id tag destination.place.mplace.ptr.offset.bytes base ptr (by rw [addresses]; exact cached)
    info (by rw [memory]; exact classified) nondata
    s.cfg.access (ConcreteProtection.source s).pointers dictionaries.checkPtrAccess resolve
    (ConcreteProtection.source_truncate s metadata.pointerSize) size dictionaries.log unitLayout
    destination.sizedMetadata destination.alignmentCache s.cfg.access.runtime.pointerSize target
    (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
  exact result.1

end EmptyFunction.NondataProtection
