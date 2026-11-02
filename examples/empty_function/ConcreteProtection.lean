import empty_function.CanonicalInit
import empty_function.ConcreteRights

/-! Live-concrete unit protection from the existing current-state domain. -/
namespace EmptyFunction.ConcreteProtection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def source (s : Static) := CanonicalDictionaries.pointerSource s.prepared.compiler s.prepared.image
  (Configuration.leaves s.prepared s.options.place.debugAssertions)

 theorem bindings (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    s.cfg.retag.resolveAllocation = TypedValidityProviders.resolveAllocation (source s).pointers ∧
    s.cfg.retag.ensureTreeExtra = GlobalAllocationMachine.ensure .global (source s).globals ∧
    (∀ memory view, (source s).globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}}) := by
  obtain ⟨remaining,eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have built := s.built
  rw [Configuration.rootConfig,eq,EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [metadata.construction.maximum_eq,
    EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    metadata.construction.i32_eq,metadata.construction.bool_eq,metadata.construction.u8_eq,
    metadata.construction.unit_eq,metadata.construction.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  simp only [metadata.construction.maximum_eq,EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq,EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    metadata.construction.i32_eq,metadata.construction.bool_eq,metadata.construction.u8_eq,
    metadata.construction.unit_eq,metadata.construction.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  have same := Except.ok.inj built
  rw [←same]
  constructor
  · with_unfolding_all rfl
  · constructor
    · with_unfolding_all rfl
    · intro memory view; with_unfolding_all rfl

 theorem truncate64 (value : UInt64) :
    (⟨Size.ofBytes 8⟩ : PointerArithmetic).truncateToTargetUsize value = .ok value := by
  have small64 : value.toNat < 2^64 := value.toBitVec.isLt
  have small128 : value.toNat < 2^128 := by omega
  have trunc : (Size.ofBytes 8).truncate (BitVec.ofNat 128 value.toNat) =
      .ok (BitVec.ofNat 128 value.toNat) := by
    change Except.ok (BitVec.zeroExtend 128
      (BitVec.extractLsb 63 0 (BitVec.ofNat 128 value.toNat))) = _
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,BitVec.extractLsb_toNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small64,Nat.mod_eq_of_lt small128]
  unfold PointerArithmetic.truncateToTargetUsize
  rw [trunc]
  with_unfolding_all
    change (if (BitVec.ofNat 128 value.toNat).toNat < 2^64 then
      Except.ok (UInt64.ofNat (BitVec.ofNat 128 value.toNat).toNat)
      else Except.error PointerError.unsignedConversionOverflow) = _
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small128,small64]

 theorem source_truncate (s : Static) (pointerSize : s.prepared.compiler.runtime.target.pointerSize = Size.ofBytes 8)
    (value : UInt64) : (source s).pointers.arithmetic.truncateToTargetUsize value = .ok value := by
  have arithmetic : (source s).pointers.arithmetic = ⟨s.prepared.compiler.runtime.target.pointerSize⟩ := rfl
  rw [arithmetic,pointerSize]
  exact truncate64 value

 theorem selected (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    ∃ base parent, p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩ ∧ entry.allocation.extra.tagMapping.get tag = some parent := by
  cases destination.pointer with
  | integer integer => rw [encoding] at integer; contradiction
  | wildcard wildcard mode tables selected => rw [encoding] at wildcard; cases Option.some.inj wildcard
  | concrete supplied suppliedTag base tables concrete cached backing parent latent =>
    have equal := concrete.symm.trans encoding
    have pair : supplied = id ∧ suppliedTag = tag := by simpa using equal
    rcases pair with ⟨rfl,rfl⟩
    obtain ⟨index,node,tagged,_,_⟩ := parent entry live
    exact ⟨base,index,cached,tagged⟩

 theorem tag_room (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition) : input.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have bound := resources.tagRoom input.tracker input.world.enabled
  have budget : 64 ≤ resources.budget := by
    have reserve := resources.reserve
    unfold work at reserve
    omega
  change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
  omega

def protectedMachine (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (tracker : MachineHooks.BorrowState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree) :=
  {UnitRetag.registeredMachine (UnitRetag.allocatedMachine machine tracker room)
      (UnitRetag.allocatedTracker tracker room) tracker.global.nextPointerTag with
    memory := UnitRetag.replaceTree machine.memory id entry tree}

def releasedMachine (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (tracker : MachineHooks.BorrowState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree) :=
  {UnitRetag.allocatedMachine machine tracker room with memory := UnitRetag.replaceTree machine.memory id entry tree}

/-- The initial current-state domain supplies the graph, allocator, parent and
freshness facts. No byte bounds, nonnull or unit mutability condition is added. -/
 theorem protect (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (pointerSize : s.prepared.compiler.runtime.target.pointerSize = Size.ofBytes 8)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition)
    (destination : InputDraft.MemoryDestination s p input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses) :
    ∃ tree,
      TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
        (LocalUnit.current p.before.stack.frames frame machine) =
        .ok () (LocalUnit.current p.before.stack.frames
          (UnitRetag.registeredFrame frame {} id input.tracker.global.nextPointerTag)
          (protectedMachine machine input.tracker (tag_room s p input resources) id entry tree)) ∧
      tree.releaseProtector input.tracker.global.nextPointerTag
        (UnitRetag.registeredTracker (UnitRetag.allocatedTracker input.tracker (tag_room s p input resources))
          input.tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩ := by
  obtain ⟨base,parent,cached,tagged⟩ := selected s p input destination id tag encoding entry live
  have member := Array.mem_of_find?_eq_some live
  obtain ⟨formed⟩ := input.world.liveTrees (id,entry) member
  have nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
    have bound : entry.allocation.extra.nodes.size + resources.budget < 2^32 := resources.nodeRoom (id,entry) member
    have account : entry.allocation.extra.tagMapping.mapping.size +
        entry.allocation.extra.tagMapping.deassigned.size = entry.allocation.extra.nodes.size := formed.accounting
    omega
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨resolve,ensure,synchronize⟩ := bindings s metadata capacity
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
  exact UnitRetag.protect_live_concrete s.cfg.retag s.limits.retag destination.place
    p.before.stack.frames frame {} machine input.tracker enabled frameBorrow (tag_room s p input resources)
    id entry tag parent destination.place.mplace.ptr.offset.bytes base ptr
    (by rw [addresses]; exact cached) (by rw [memory]; exact live) formed tagged nodeRoom
    s.cfg.access (source s).pointers dictionaries.checkPtrAccess resolve (source_truncate s pointerSize)
    size dictionaries.log (by rw [dictionaries.precise,profile.precise])
    (by apply dictionaries.freeze; rw [destination.layout]; exact metadata.unitFreeze)
    .global (source s).globals ensure synchronize unitLayout destination.sizedMetadata destination.alignmentCache
    s.cfg.access.runtime.pointerSize target (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit

 theorem protect_with_rights (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (pointerSize : s.prepared.compiler.runtime.target.pointerSize = Size.ofBytes 8)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition)
    (destination : InputDraft.MemoryDestination s p input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses) :
    ∃ tree,
      TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
        (LocalUnit.current p.before.stack.frames frame machine) =
        .ok () (LocalUnit.current p.before.stack.frames
          (UnitRetag.registeredFrame frame {} id input.tracker.global.nextPointerTag)
          (protectedMachine machine input.tracker (tag_room s p input resources) id entry tree)) ∧
      tree.releaseProtector input.tracker.global.nextPointerTag
        (UnitRetag.registeredTracker (UnitRetag.allocatedTracker input.tracker (tag_room s p input resources))
          input.tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩ ∧
      Preservation.OldNodeRights entry.allocation.extra tree := by
  obtain ⟨base,parent,cached,tagged⟩ := selected s p input destination id tag encoding entry live
  have member := Array.mem_of_find?_eq_some live
  obtain ⟨formed⟩ := input.world.liveTrees (id,entry) member
  have nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
    have bound : entry.allocation.extra.nodes.size + resources.budget < 2^32 := resources.nodeRoom (id,entry) member
    have account : entry.allocation.extra.tagMapping.mapping.size +
        entry.allocation.extra.tagMapping.deassigned.size = entry.allocation.extra.nodes.size := formed.accounting
    omega
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨resolve,ensure,synchronize⟩ := bindings s metadata capacity
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
  obtain ⟨tree,protectedEq,released,created⟩ := UnitRetag.protect_live_concrete_observed s.cfg.retag s.limits.retag destination.place
    p.before.stack.frames frame {} machine input.tracker enabled frameBorrow (tag_room s p input resources)
    id entry tag parent destination.place.mplace.ptr.offset.bytes base ptr
    (by rw [addresses]; exact cached) (by rw [memory]; exact live) formed tagged nodeRoom
    s.cfg.access (source s).pointers dictionaries.checkPtrAccess resolve (source_truncate s pointerSize)
    size dictionaries.log (by rw [dictionaries.precise,profile.precise])
    (by apply dictionaries.freeze; rw [destination.layout]; exact metadata.unitFreeze)
    .global (source s).globals ensure synchronize unitLayout destination.sizedMetadata destination.alignmentCache
    s.cfg.access.runtime.pointerSize target (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit

  refine ⟨tree,protectedEq,released,?_⟩
  have rights := ConcreteRights.constructor entry.allocation.extra input.tracker.global.nextPointerTag
    formed tag parent tagged nodeRoom (Size.ofBytes (destination.place.mplace.ptr.offset.bytes-base))
    (⟨.ReservedFrz false,false,.None⟩ : Tree.LocationState)
  rw [created] at rights
  exact rights

/-- Reuse the constructor's release certificate after arbitrary unit-body and
counter bookkeeping. Only the actual tracker/memory fields are named here. -/
 theorem release (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (enabled : machine.borrowTracker = some (UnitRetag.allocatedTracker tracker room))
    (formed : TreeRuntimeInput.GlobalFormed tracker.global)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree)
    (released : tree.releaseProtector tracker.global.nextPointerTag
      (UnitRetag.registeredTracker (UnitRetag.allocatedTracker tracker room)
        tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩) :
    MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)
        {UnitRetag.registeredMachine machine (UnitRetag.allocatedTracker tracker room)
          tracker.global.nextPointerTag with memory := UnitRetag.replaceTree machine.memory id entry tree}) =
      .ok () (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)
        {machine with memory := UnitRetag.replaceTree machine.memory id entry tree}) := by
  obtain ⟨_,ensure,synchronize⟩ := bindings s metadata capacity
  rw [ensure]
  have result := UnitRetag.release_live_singleton (K := MiriMemoryKind) (U := RootUser)
    .global (source s).globals synchronize frames frame machine
    (UnitRetag.allocatedTracker tracker room) enabled id entry tree tracker.global.nextPointerTag
    (show (UnitRetag.allocatedTracker tracker room).global.protectedTags.get tracker.global.nextPointerTag = none
      from formed.nextNotProtected) released
  simpa only [UnitRetag.withCurrent,LocalUnit.current] using result

end EmptyFunction.ConcreteProtection
