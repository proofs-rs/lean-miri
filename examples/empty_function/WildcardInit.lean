import empty_function.MemoryInitFinish
import empty_function.WildcardProtection
import empty_function.WildcardRights
import empty_function.NondataProtection
namespace EmptyFunction.WildcardInit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open Miri.TreeBorrows.Tree
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The current nearest exposed candidate is already live or non-data.
Latent-data selection is a separate unfinished family, not excluded from the
final target. This is raw registry/geometry classification, not resolver success. -/
def Resident (_s : Static) (p : Packet) (pointer : Pointer (Option Provenance)) : Prop :=
  ∀ row ∈ p.before.machine.user.addresses.intToPtrMap,
    p.before.machine.user.addresses.exposed.contains row.allocId = true →
    InputDraft.WildcardCandidate p.before pointer row →
    (∃ entry, p.before.machine.memory.live.find? (fun pair => pair.1 == row.allocId) = some (row.allocId,entry)) ∨
      NondataProtection.Registry p.before row.allocId

/-- This indexed result carries certificates produced by protection, never
initial-state assumptions. -/
inductive Case (p : Packet) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) where
  | miss
  | nondata (id : AllocId) (registry : NondataProtection.Registry p.before id)
  | live (id : AllocId) (entry : InputDraft.Entry)
      (present : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (tree : BorrowTree)
      (released : tree.releaseProtector tracker.global.nextPointerTag
        (UnitRetag.registeredTracker (UnitRetag.allocatedTracker tracker room) tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩)
      (rights : Preservation.OldNodeRights entry.allocation.extra tree)

def borrow {p : Packet} {tracker : MachineHooks.BorrowState}
    {room : tracker.global.nextPointerTag.value < 18446744073709551615} : Case p tracker room → FrameState
  | .miss => {}
  | .nondata id _ => {protectedTags := #[(id,tracker.global.nextPointerTag)]}
  | .live id _ _ _ _ _ => {protectedTags := #[(id,tracker.global.nextPointerTag)]}

def entered {p : Packet} {tracker : MachineHooks.BorrowState}
    {room : tracker.global.nextPointerTag.value < 18446744073709551615}
    (choice : Case p tracker room) (machine : MachineHooks.MachineState MiriMemoryKind RootUser) :=
  match choice with
  | .miss => UnitRetag.allocatedMachine machine tracker room
  | .nondata _ _ => NondataProtection.protectedMachine machine tracker room
  | .live id entry _ tree _ _ => ConcreteProtection.protectedMachine machine tracker room id entry tree

structure Entry (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) where
  choice : Case p tracker room
  frame : LocalUnit.F
  previous : LocalUnit.F
  machine : MachineHooks.MachineState MiriMemoryKind RootUser
  installed : WholeCall.install s p = .ok () (LocalUnit.current p.before.stack.frames frame machine)
  body : frame.body = s.loaded.body
  identity : frame.bodyIdentity = s.loaded.identity
  function : frame.functionInstance = s.functionInstance
  location : frame.location = .mir ⟨0,0⟩
  locals : frame.locals = #[{value := .live (.immediate .uninit),layout := none}]
  tracked : frame.extra.borrowTracker = some (borrow choice)
  noClocks : frame.extra.dataRace = none
  returnPlace : frame.returnPlace = p.destination
  continuation : frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind)
  varargs : frame.vaList = #[]
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  machineEq : machine = entered choice (FrameRelevance.pushedMachine p.before.stack.frames frame previous
    (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1)

theorem install (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (wild : destination.place.mplace.ptr.provenance = some .wildcard)
    (resident : Resident s p destination.place.mplace.ptr) :
    Nonempty (Entry s p input.tracker (ConcreteProtection.tag_room s p input resources)) := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity; omega
  have fields := MetadataBinding.fields s metadata capacity
  let room := ConcreteProtection.tag_room s p input resources
  obtain ⟨frame,machine,push,⟨previous,machineEq⟩,tracked,noClocks,body,identity,function,location,
    returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
      CanonicalInit.push_actual s metadata profile p runtime input capacity
        (CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind))
  have enabled : machine.borrowTracker = some input.tracker := machineTracker.trans input.world.enabled
  have memoryEq : machine.memory = p.before.machine.memory := by
    rw [machineEq]
    unfold FrameRelevance.pushedMachine
    rw [fields.freshLocalsIdentity]
    split <;> rfl
  have addressesEq : machine.user.addresses = p.before.machine.user.addresses := by
    rw [machineEq]
    unfold FrameRelevance.pushedMachine
    rw [fields.freshLocalsIdentity]
    split <;> rfl
  have complete : ∀ choice : Case p input.tracker room,
      TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
        (LocalUnit.current p.before.stack.frames {frame with location := .unwinding metadata.localSpan} machine) =
        .ok () (LocalUnit.current p.before.stack.frames
          {frame with location := .unwinding metadata.localSpan, extra := {frame.extra with borrowTracker := some (borrow choice)}}
          (entered choice machine)) → Nonempty (Entry s p input.tracker room) := by
    intro choice protection
    let output : LocalUnit.F := {frame with locals := #[{value := .live (.immediate .uninit),layout := none}], location := .mir .start, extra := {frame.extra with borrowTracker := some (borrow choice)}}
    have installed := MemoryInitFinish.finish s metadata capacity p destination.place destination.encoding
      frame machine (entered choice machine) (borrow choice) push body identity function location locals noClocks callerArg protection
    have ghost : (entered choice machine).user.payload.ghost = false := by
      cases choice <;> simp only [entered,NondataProtection.protectedMachine,ConcreteProtection.protectedMachine,
        UnitRetag.registeredMachine,UnitRetag.allocatedMachine]
      all_goals rw [machineEq]
      all_goals unfold FrameRelevance.pushedMachine
      all_goals rw [fields.freshLocalsIdentity]
      all_goals split <;> exact runtime.ghost
    have shallow : (entered choice machine).user.payload.validation = .Shallow := by
      cases choice <;> simp only [entered,NondataProtection.protectedMachine,ConcreteProtection.protectedMachine,
        UnitRetag.registeredMachine,UnitRetag.allocatedMachine]
      all_goals rw [machineEq]
      all_goals unfold FrameRelevance.pushedMachine
      all_goals rw [fields.freshLocalsIdentity]
      all_goals split <;> exact runtime.shallow
    refine ⟨⟨choice,output,previous,entered choice machine,installed,body,identity,function,rfl,rfl,rfl,
      noClocks,returnPlace,returning,varargs,ghost,shallow,?_⟩⟩
    rw [machineEq]
    rfl
  obtain ⟨answer,resolved,hits,miss,nondata,liveCase⟩ := WildcardProtection.dispatch s metadata profile capacity p input resources
    destination wild {frame with location := .unwinding metadata.localSpan} machine enabled tracked memoryEq addressesEq
  cases answer with
  | none =>
    apply complete .miss
    have same : {frame with extra := {frame.extra with borrowTracker := some {}}} = frame := by rw [←tracked]
    simpa only [borrow,entered,←tracked] using (miss rfl).1
  | some answer =>
    obtain ⟨row,member,same,exposed,candidate,backing⟩ := hits
    subst answer
    rcases resident row member exposed candidate with ⟨entry,present⟩ | registry
    · obtain ⟨tree,protection,released,child,ended⟩ := liveCase row.allocId
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
      apply complete (.live row.allocId entry present tree released rights)
      exact protection
    · obtain ⟨info,classification,notData⟩ := NondataProtection.classification p.before row.allocId registry
      apply complete (.nondata row.allocId registry)
      exact (nondata row.allocId (Size.ofBytes (destination.place.mplace.ptr.offset.bytes-row.address)) info rfl classification notData).1
end EmptyFunction.WildcardInit
