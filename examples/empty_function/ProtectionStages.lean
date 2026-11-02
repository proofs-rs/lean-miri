import empty_function.ConcreteProtection
import empty_function.NondataProtection
import empty_function.ProtectionPlace
namespace EmptyFunction.ProtectionStages
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.NondataProtection
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.ConcreteProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
theorem selected (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : ProtectionPlace.Input s p.before input.tracker) (id : AllocId) (tag : BorTag)
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

theorem concrete (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (pointerSize : s.prepared.compiler.runtime.target.pointerSize = Size.ofBytes 8)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : ResourceMargins s p)
    (destination : ProtectionPlace.Input s p.before input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses) :
    ∃ tree,
      TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
        (LocalUnit.current frames frame machine) =
        .ok () (LocalUnit.current frames
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
    frames frame {} machine input.tracker enabled frameBorrow (tag_room s p input resources)
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


theorem selected_nondata (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : ProtectionPlace.Input s p.before input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag)) :
    ∃ base, p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
  cases destination.pointer with
  | integer integer => rw [encoding] at integer; contradiction
  | wildcard wildcard mode tables selected => rw [encoding] at wildcard; cases Option.some.inj wildcard
  | concrete supplied suppliedTag base tables concrete cached backing parent latent =>
    have pair : supplied = id ∧ suppliedTag = tag := by simpa using concrete.symm.trans encoding
    rcases pair with ⟨rfl,rfl⟩
    exact ⟨base,cached⟩

theorem nondata (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : ResourceMargins s p)
    (destination : ProtectionPlace.Input s p.before input.tracker) (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (registry : Registry p.before id)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses) :
    TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
      (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames
        (UnitRetag.registeredFrame frame {} id input.tracker.global.nextPointerTag)
        (NondataProtection.protectedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))) := by
  obtain ⟨base,cached⟩ := selected_nondata s p input destination id tag encoding
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
    frames frame machine input.tracker enabled frameBorrow
    (ConcreteProtection.tag_room s p input resources) input.world.globals
    id tag destination.place.mplace.ptr.offset.bytes base ptr (by rw [addresses]; exact cached)
    info (by rw [memory]; exact classified) nondata
    s.cfg.access (ConcreteProtection.source s).pointers dictionaries.checkPtrAccess resolve
    (ConcreteProtection.source_truncate s metadata.pointerSize) size dictionaries.log unitLayout
    destination.sizedMetadata destination.alignmentCache s.cfg.access.runtime.pointerSize target
    (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
  exact result.1


end EmptyFunction.ProtectionStages
