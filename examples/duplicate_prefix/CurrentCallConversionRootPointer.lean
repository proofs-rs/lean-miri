import duplicate_prefix.CurrentCallConversionCacheFrames
import duplicate_prefix.PointerArithmetic
import Miri.Interpreter.PointerSource
namespace DuplicatePrefix.CurrentCallConversionRootPointer
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
abbrev Control := EvalPointerSource.Control Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost

def global (before : GlobalState) (id : AllocId) (room : before.nextPointerTag.value<18446744073709551615) : GlobalState :=
  match before.rootTag? id with
  | some _=>before
  | none=>{GeneralBorrowFnEntryRegistration.advanced before room with rootPointerTags:=before.rootPointerTags.push (id,before.nextPointerTag)}

def tag (before : GlobalState) (id : AllocId) : BorTag := (before.rootTag? id).getD before.nextPointerTag

def machine (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) : Before :=
  {before with borrowTracker:=some {tracker with global:=global tracker.global id room}}

theorem operation (before : GlobalState) (id : AllocId) (room : before.nextPointerTag.value<18446744073709551615) :
    before.rootPointerTag id=.ok (global before id room,tag before id) := by
  cases cached : before.rootTag? id with
  | some root=>simpa only [global,tag,cached,Option.getD_some] using GlobalState.rootPointerTag_existing before id root cached
  | none=>
    simp only [GlobalState.rootPointerTag,cached,TypedRetagEmpty.allocate_tag before room,bind,Except.bind,pure,Except.pure]
    simp only [global,tag,cached,Option.getD_none]
    rfl

/-- Actual deterministic root allocation retains old cache hits and spends
one unit of the finite root-miss potential when it creates a new root. -/
theorem facts (before : GlobalState) (ids : List AllocId) (id : AllocId) (member : id∈ids)
    (room : before.nextPointerTag.value<18446744073709551615) :
    before.rootPointerTag id=.ok (global before id room,tag before id) ∧
    (global before id room).rootTag? id=some (tag before id) ∧
    (∀query old,before.rootTag? query=some old→(global before id room).rootTag? query=some old) ∧
    (global before id room).nextPointerTag.value.toNat+(ids.filter (fun query=>((global before id room).rootTag? query).isNone)).length≤
      before.nextPointerTag.value.toNat+(ids.filter (fun query=>(before.rootTag? query).isNone)).length := by
  obtain ⟨next,root,actual,hit,old,potential⟩:=CurrentCallConversionCacheFrames.root before ids id member room
  have equal : (next,root)=(global before id room,tag before id):=Except.ok.inj (actual.symm.trans (operation before id room))
  have nextEq : next=global before id room:=congrArg Prod.fst equal
  have rootEq : root=tag before id:=congrArg Prod.snd equal
  subst next
  subst root
  exact ⟨actual,hit,old,potential⟩

/-- The address certificate is the internally derived actual acquisition on
the root-installed machine. This theorem retains its exact post-machine and
proves the real pointer callback; arbitrary address hooks are not claimed to
preserve the tracker afterward. -/
theorem from_address (before : Before) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker=some tracker) (provenance : CtfeProvenance) (offset : UInt64)
    (metadata : RelocationTargetMetadata before provenance.allocId)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (hooks : MachineAddress.Hooks MiriMemoryKind Control) (width : hooks.arithmetic=⟨Size.ofBytes 8⟩)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind Control (Pointer Provenance))
    (base : UInt64) (after : Before)
    (address : MachineAddress.addrFromAllocId EvalPointerSource.tape hooks provenance.allocId (some .other)
      (machine before tracker provenance.allocId room)=.ok base after) :
    PointerSource.globalRootPointer EvalPointerSource.tape hooks externStatic (Pointer.new provenance (Size.ofBytes offset)) before=
      .ok (Pointer.new (Provenance.concrete provenance.allocId (tag tracker.global provenance.allocId)) (Size.ofBytes (base+offset))) after := by
  have root:=operation tracker.global provenance.allocId room
  have wrapping:=PointerArithmetic.wrapping_offset_u64
    (Pointer.new (Provenance.concrete provenance.allocId (tag tracker.global provenance.allocId)) (Size.ofBytes base)) (Size.ofBytes offset)
  change (Pointer.new (Provenance.concrete provenance.allocId (tag tracker.global provenance.allocId)) (Size.ofBytes base)).wrappingOffset
    (Size.ofBytes offset) ⟨Size.ofBytes 8⟩=.ok _ at wrapping
  simp only [Pointer.new] at wrapping
  simp only [machine] at address
  have dispatch:=metadata.2.1
  cases found : before.memory.findGlobal? provenance.allocId with
  | none=>
    simp only [found] at dispatch
    have valid : (before.memory.hasExtraFunctionId provenance.allocId ||before.memory.hasVaListId provenance.allocId)=true:=by
      rcases dispatch with extra | variadic
      · simp only [extra,Bool.true_or]
      · simp only [variadic,Bool.or_true]
    simp only [PointerSource.globalRootPointer,Pointer.new,found,valid,enabled,root,
      get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_true,ite_false]
    first | rfl | (simp only [address,width,wrapping,EStateM.pure] <;> rfl)
  | some descriptor=>
    simp only [found] at dispatch
    cases payload : descriptor.payload with
    | none=>
      simp only [payload] at dispatch
      have kind : (descriptor.kind==.static)=false:=by exact beq_eq_false_iff_ne.mpr dispatch
      simp only [PointerSource.globalRootPointer,Pointer.new,found,payload,kind,enabled,root,
        get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
        bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,ite_true,ite_false]
      first | rfl | (simp only [address,width,wrapping,EStateM.pure] <;> rfl)
    | some value=>
      cases value <;> simp only [payload] at dispatch
      all_goals
        simp_all only [PointerSource.globalRootPointer,Pointer.new,found,payload,enabled,root,
          get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_eq_true,↓reduceIte]
        first | rfl | (simp only [address,width,wrapping,EStateM.pure] <;> rfl)
end DuplicatePrefix.CurrentCallConversionRootPointer
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionRootPointer" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual conversion root-pointer dependency {dependency}"
