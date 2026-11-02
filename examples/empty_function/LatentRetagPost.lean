import empty_function.LatentTreePost
import empty_function.UnitRetag
namespace EmptyFunction.LatentRetagPost
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open BorrowTree.ZeroProtection
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem allocate_fresh (tree : BorrowTree) (counter tag : BorTag)
    (input : TreeRuntimeInput.TreeFormed tree counter) (fresh : tree.tagMapping.get tag = none)
    (room : tree.tagMapping.mapping.size ≤ 4294967295) :
    ∃ mapping index, tree.tagMapping.insert tag = .Inserted mapping index ∧
      mapping.get tag = some index ∧ tree.nodes.get index = none := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
      deassigned := tree.tagMapping.deassigned }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, UniIndex.ofNat?, room, fresh, mapping, index]
    have endEq : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact input.appendAligned available
    have vacant : tree.nodes.get index = none := by
      unfold UniValMap.get
      simp [endEq]
    have selected : mapping.get tag = some index := by
      simp [mapping, UniKeyMap.get, Array.find?_push]
      have emptyFind : tree.tagMapping.mapping.find? (fun _ => false) = none :=
        Array.find?_eq_none.mpr (by intro row member; simp)
      rw [emptyFind]
      rfl
    exact ⟨mapping,index,inserted,selected,vacant⟩
  | some index =>
    let mapping : UniKeyMap BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
      deassigned := tree.tagMapping.deassigned.pop }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, fresh, mapping]
    have vacant := (input.reuseValid index available).2
    have selected : mapping.get tag = some index := by
      simp [mapping, UniKeyMap.get, Array.find?_push]
      have emptyFind : tree.tagMapping.mapping.find? (fun _ => false) = none :=
        Array.find?_eq_none.mpr (by intro row member; simp)
      rw [emptyFind]
      rfl
    exact ⟨mapping,index,inserted,selected,vacant⟩


/-- Freshness is independent of the current global-counter ordering. A child
reserved before materialization may be older than its newly created parent. -/
theorem concrete (tree : BorrowTree) (counter tag parentTag : BorTag)
    (formed : TreeRuntimeInput.TreeFormed tree counter)
    (fresh : tree.tagMapping.get tag = none) (parent : UniIndex)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (room : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    ∃ after, tree.newChild offset (.concrete parentTag) tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩ ∧
      after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  obtain ⟨node,present⟩ := formed.parentPresent parentTag parent tagged
  obtain ⟨mapping,index,inserted,selected,vacant⟩ := allocate_fresh tree counter tag formed fresh room
  have release := Release.concrete_zero_release tree parentTag tag index parent node mapping inserted tagged present vacant
    selected (formed.vacantClean index vacant) offset initial protections
  obtain ⟨after,constructed⟩ := RankNormalization.concrete_child_of_rank tree formed.parentRank parentTag tag parent node
    tagged present fresh room formed.appendAligned formed.reuseValid offset initial
  exact ⟨after,constructed,by simpa only [constructed] using release⟩

theorem wildcard (tree : BorrowTree) (counter tag : BorTag)
    (formed : TreeRuntimeInput.TreeFormed tree counter)
    (fresh : tree.tagMapping.get tag = none) (room : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    ∃ after, tree.newChild offset .wildcard tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩ ∧
      after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  obtain ⟨mapping,index,inserted,selected,vacant⟩ := allocate_fresh tree counter tag formed fresh room
  have constructed := Release.wildcard_zero_eq tree tag index mapping inserted offset initial
  have release := Release.wildcard_zero_release tree tag index mapping inserted selected
    (formed.vacantClean index vacant) offset initial protections
  exact ⟨_,constructed,by simpa only [constructed] using release⟩

/-- Both possible latent parents use the real newly materialized singleton
tree. Distinct root/child tags suffice, in either numeric order. -/
theorem new_tree (root counter tag : BorTag) (size : Size)
    (formed : TreeRuntimeInput.TreeFormed (BorrowTree.new root size) counter)
    (distinct : root ≠ tag) (parent : ProvenanceExtra)
    (parentShape : parent = .wildcard ∨ parent = .concrete root)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    ∃ after, (BorrowTree.new root size).newChild offset parent tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩ ∧
      after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  have mapping : (BorrowTree.new root size).tagMapping = (⟨#[(root,⟨0⟩)],#[]⟩ : UniKeyMap BorTag) := rfl
  have fresh : (BorrowTree.new root size).tagMapping.get tag = none := by
    rw [mapping]
    simp [UniKeyMap.get,distinct]
  have room : (BorrowTree.new root size).tagMapping.mapping.size ≤ 4294967295 := by
    rw [mapping]
    change 1 ≤ 4294967295
    decide
  rcases parentShape with wild | concreteParent
  · subst parent
    exact wildcard _ counter tag formed fresh room offset initial protections
  · subst parent
    have tagged : (BorrowTree.new root size).tagMapping.get root = some ⟨0⟩ := by
      rw [mapping]
      simp [UniKeyMap.get]
    exact concrete _ counter tag root formed fresh ⟨0⟩ tagged room offset initial protections

/-- Exact reborrow composition across actual lazy ensure. All equations here
are internal post boundaries derived by the canonical raw-input proof. -/
theorem reborrow_after_ensure {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array UnitRetag.F) (frame : UnitRetag.F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (UnitRetag.withCurrent frames frame machine) =
      .ok () (UnitRetag.withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (UnitRetag.withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (UnitRetag.withCurrent frames frame machine))
    (log : h.logCreation = fun _ _ _ _ _ => pure ()) (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (info : AllocationInfo) (metadata : machine.memory.getAllocInfo id = .ok info) (data : info.kind = .liveData)
    (ensuredMachine : MachineHooks.MachineState K U)
    (ensured : h.ensureTreeExtra id
      (UnitRetag.withCurrent frames (UnitRetag.registeredFrame frame borrowFrame id tag)
        (UnitRetag.registeredMachine machine tracker tag)) =
      .ok () (UnitRetag.withCurrent frames (UnitRetag.registeredFrame frame borrowFrame id tag) ensuredMachine))
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : ensuredMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : BorrowTree)
    (constructed : entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO ⟨.ReservedFrz false,false,.None⟩) (.ReservedFrz false) true = ⟨tree,.ok ()⟩) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (UnitRetag.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (UnitRetag.withCurrent frames (UnitRetag.registeredFrame frame borrowFrame id tag)
          {ensuredMachine with memory := UnitRetag.replaceTree ensuredMachine.memory id entry tree}) := by
  let start := UnitRetag.withCurrent frames frame machine
  have current : MachineHooks.currentFrame start = .ok frame start := by
    simp [MachineHooks.currentFrame,Stack.currentFrame?,start,UnitRetag.withCurrent,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  unfold TypedRetag.reborrow
  simp only [check,resolve,log,bind,EStateM.bind,pure,EStateM.pure,MachineHooks.protectionPolicy]
  rw [current]
  simp only [frameBorrow,bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply]
  simp only [start,UnitRetag.withCurrent,enabled,bind,EStateM.bind,pure,EStateM.pure]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    set,EStateM.set,Array.isEmpty_push,Array.pop_push,Bool.false_eq_true,↓reduceIte]
  simp only [TypedRetag.checked_eq,metadata,data,bind,EStateM.bind,pure,EStateM.pure,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  erw [TypedRetag.insidePermissions_unit h budget place precise freeze]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [ensured]
  simp only [bind,EStateM.bind,pure,EStateM.pure,DedupRangeMap.new,DedupRangeMap.iterAll,
    Size.ZERO,Size.ofBytes,beq_self_eq_true,↓reduceIte,←Array.forIn_toList,List.forIn_nil,
    TypedRetag.getTree_apply,UnitRetag.withCurrent,live]
  rw [show DedupRangeMap.new Size.ZERO (⟨.ReservedFrz false,false,.None⟩ : LocationState) = {} from rfl] at constructed
  erw [constructed]
  simp only [TypedRetag.updateTree_apply,live]
  rw [UnitRetag.set_live ensuredMachine.memory id entry tree live]
  simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure]
end EmptyFunction.LatentRetagPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LatentRetagPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent reborrow join axiom {dependency} in {name}"
