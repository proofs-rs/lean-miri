import empty_function.LatentRetagPost
import empty_function.Preservation
namespace EmptyFunction.LatentProtectionPost
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The shared source tag-reservation and unit-write tail composes with the
proved reborrow across actual lazy ensure. All operation equations are internal
composition boundaries; no such equation becomes a raw input field. -/
theorem protect_from_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (parent : Provenance) (encoding : place.mplace.ptr.provenance = some parent)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (after : MachineHooks.State K (ValidityMachine.UserState U))
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tracker.global.nextPointerTag
      (withCurrent frames frame (allocatedMachine machine tracker room)) =
      .ok (some (.concrete id tracker.global.nextPointerTag)) after)
    (access : ValidityMachine.Access K U)
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit p)) :
    TypedRetag.protectInPlaceFunctionArgument h budget place (withCurrent frames frame machine) = .ok () after := by
  let result : MPlaceTy Provenance := {place with mplace := {place.mplace with ptr :=
    {place.mplace.ptr with provenance := some (.concrete id tracker.global.nextPointerTag)}}}
  have retagged : TypedRetag.retagPlace h budget place MachineHooks.protectionPolicy
      (withCurrent frames frame machine) = .ok result after := by
    unfold TypedRetag.retagPlace
    rw [size]
    simp only [bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply,withCurrent,enabled]
    rw [allocate_tag tracker.global room]
    simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    erw [reborrow]
    simp only [bind,EStateM.bind,pure,EStateM.pure,encoding,result]
  have resultEncoding : result.mplace = ⟨result.mplace.ptr,.none,none⟩ := by simp [result,noMeta,aligned]
  have written := UnitProtection.scoped_uninit access result result.mplace.ptr (some place.layout.ty)
    pointerSize unitLayout resultEncoding target retain after
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,withCurrent,enabled,Option.isSome_some,↓reduceIte]
  erw [retagged]
  simp only [bind,EStateM.bind]
  rw [writeBinding]
  exact written

/-- Lazy initialization may change root caches and the shared counter while
retaining the registered protector. Ending that protector keeps those real
materialization updates and follows the existing live release operation. -/
theorem release_after_ensure {K U : Type} [DecidableEq K]
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view = {view with machine := {view.machine with memory}})
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (protections : ProtectedTags) (tag : BorTag)
    (fresh : protections.get tag = none)
    (protectedEq : tracker.global.protectedTags = protections.insert tag .StrongProtector)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (released : tree.releaseProtector tag tracker.global.protectedTags = ⟨tree,.Released⟩) :
    let baselineTracker := {tracker with global := {tracker.global with protectedTags := protections}}
    let baselineMachine := {machine with borrowTracker := some baselineTracker}
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure kind globals)
      (withCurrent frames (registeredFrame frame {} id tag)
        {machine with memory := replaceTree machine.memory id entry tree}) =
      .ok () (withCurrent frames (registeredFrame frame {} id tag)
        {baselineMachine with memory := replaceTree machine.memory id entry tree}) := by
  dsimp only
  let baselineTracker := {tracker with global := {tracker.global with protectedTags := protections}}
  let baselineMachine := {machine with borrowTracker := some baselineTracker}
  have registered : registeredTracker baselineTracker tag = tracker := by
    dsimp only [registeredTracker,baselineTracker]
    rw [←protectedEq]
  have machineEq : registeredMachine baselineMachine baselineTracker tag = machine := by
    simp only [registeredMachine,registered,baselineMachine,←enabled]
  have certificate : tree.releaseProtector tag (registeredTracker baselineTracker tag).global.protectedTags = ⟨tree,.Released⟩ := by
    rw [registered]
    exact released
  have actual := release_live_singleton kind globals synchronize frames frame baselineMachine baselineTracker rfl
    id entry tree tag fresh certificate
  simpa only [machineEq,baselineMachine] using actual

private theorem rights_refl (tree : BorrowTree) : Preservation.OldNodeRights tree tree := by
  refine ⟨fun _ _ present => present,fun _ present => present,?_⟩
  intro index node present
  refine ⟨node,present,rfl,rfl,rfl,rfl,rfl,fun _ member => member,?_⟩
  intro byte segment member contains
  exact ⟨segment,member,contains,rfl,rfl⟩

/-- The initial source ID is not live. Its materialization and child-tree
write-back therefore preserve every original live allocation and old node's
observable rights by exact row retention, without constraining the new root. -/
theorem original_live (before after : WholeCall.State) (id : AllocId)
    (entry : InputDraft.Entry)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (installed : after.machine.memory.live =
      (before.machine.memory.live.filter fun row => row.1 != id).push (id,entry)) :
    Preservation.OriginalLiveAllocations before after := by
  intro oldId old prior
  have different : oldId ≠ id := by
    intro same
    subst oldId
    rw [absent] at prior
    cases prior
  have clean : (before.machine.memory.live.filter fun row => row.1 != id).find? (fun row => row.1 == oldId) = some (oldId,old) := by
    rw [Array.find?_filter]
    have test : (fun row : AllocId × InputDraft.Entry => (row.1 != id) && (row.1 == oldId)) =
        (fun row => row.1 == oldId) := by
      funext row
      by_cases equal : row.1 = oldId <;> simp [equal,different]
    change before.machine.memory.live.find? (fun row => (row.1 != id) && (row.1 == oldId)) = _
    rw [test]
    exact prior
  refine ⟨old,?_,rfl,rfl,rights_refl old.allocation.extra⟩
  simp only [installed,Array.find?_push,clean,Option.or]
end EmptyFunction.LatentProtectionPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LatentProtectionPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent protection composition axiom {dependency} in {name}"
