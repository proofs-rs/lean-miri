import empty_function.ProtectionStages
import empty_function.WildcardInit
namespace EmptyFunction.ProtectionDispatch
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows Miri.TreeBorrows.Tree
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.WildcardInit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def Resident (s : Static) (p : Packet) (pointer : Pointer (Option Provenance)) : Prop :=
  match pointer.provenance with
  | none => True
  | some (.concrete id _) =>
    (∃ entry, p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) ∨
      NondataProtection.Registry p.before id
  | some .wildcard => WildcardInit.Resident s p pointer

theorem protect (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : ResourceMargins s p)
    (destination : ProtectionPlace.Input s p.before input.tracker)
    (resident : Resident s p destination.place.mplace.ptr)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker) (tracked : frame.extra.borrowTracker = some {})
    (memoryEq : machine.memory = p.before.machine.memory)
    (addressesEq : machine.user.addresses = p.before.machine.user.addresses) :
    ∃ choice : Case p input.tracker (ConcreteProtection.tag_room s p input resources),
      TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
        (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames {frame with extra := {frame.extra with borrowTracker := some (borrow choice)}}
        (entered choice machine)) := by
  let room := ConcreteProtection.tag_room s p input resources
  cases encoding : destination.place.mplace.ptr.provenance with
  | none =>
    refine ⟨.miss,?_⟩
    have protection := CanonicalInit.integer_protection s metadata capacity destination.place destination.layout encoding
      destination.sizedMetadata destination.alignmentCache (LocalUnit.current frames frame machine) input.tracker enabled room
    change TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place _ = _ at protection
    simpa only [borrow,entered,←tracked,LocalUnit.current] using protection
  | some provenance =>
    cases provenance with
    | concrete id tag =>
      have selected : (∃ entry, p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) ∨
          NondataProtection.Registry p.before id := by simpa only [Resident,encoding] using resident
      rcases selected with ⟨entry,live⟩ | registry
      · obtain ⟨tree,protection,release,rights⟩ := ProtectionStages.concrete s metadata profile capacity metadata.pointerSize
          p input resources destination id tag encoding entry live frames frame machine enabled tracked memoryEq addressesEq
        exact ⟨.live id entry live tree release rights,protection⟩
      · exact ⟨.nondata id registry,ProtectionStages.nondata s metadata capacity p input resources destination id tag
          encoding registry frames frame machine enabled tracked memoryEq addressesEq⟩
    | wildcard =>
      obtain ⟨answer,resolved,hits,miss,nondata,liveCase⟩ := WildcardProtection.dispatch_stage s metadata profile capacity
        p input resources destination encoding frames frame machine enabled tracked memoryEq addressesEq
      cases answer with
      | none =>
        refine ⟨.miss,?_⟩
        simpa only [borrow,entered,←tracked] using (miss rfl).1
      | some answer =>
        obtain ⟨row,member,same,exposed,candidate,backing⟩ := hits
        subst answer
        have selected := (show WildcardInit.Resident s p destination.place.mplace.ptr by
          simpa only [Resident,encoding] using resident) row member exposed candidate
        rcases selected with ⟨entry,present⟩ | registry
        · obtain ⟨tree,protection,release,child,ended⟩ := liveCase row.allocId
            (Size.ofBytes (destination.place.mplace.ptr.offset.bytes-row.address)) entry rfl present
          have memberLive := Array.mem_of_find?_eq_some present
          obtain ⟨formed⟩ := input.world.liveTrees (row.allocId,entry) memberLive
          have nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
            have bound : entry.allocation.extra.nodes.size + resources.budget < 2^32 := resources.nodeRoom (row.allocId,entry) memberLive
            have accounting : entry.allocation.extra.tagMapping.mapping.size + entry.allocation.extra.tagMapping.deassigned.size = entry.allocation.extra.nodes.size := formed.accounting
            omega
          have rights := WildcardRights.constructor entry.allocation.extra input.tracker.global.nextPointerTag formed nodeRoom
            (Size.ofBytes (destination.place.mplace.ptr.offset.bytes-row.address)) (⟨.ReservedFrz false,false,.None⟩ : LocationState)
          rw [child] at rights
          exact ⟨.live row.allocId entry present tree release rights,protection⟩
        · obtain ⟨info,classification,notData⟩ := NondataProtection.classification p.before row.allocId registry
          exact ⟨.nondata row.allocId registry,
            (nondata row.allocId (Size.ofBytes (destination.place.mplace.ptr.offset.bytes-row.address)) info rfl classification notData).1⟩
end EmptyFunction.ProtectionDispatch
