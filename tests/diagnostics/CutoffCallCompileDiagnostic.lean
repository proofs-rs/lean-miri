import duplicate_prefix.Initial
import Miri.Input.CompilerInstanceAbi
import Miri.Interpreter.TypedRetag

/-!
# Known-failing cutoff call compiler diagnostic

This preserves a compiler reproducer, not a passing regression test. With the
pinned Lean 4.35.0 toolchain, compilation failed with `unknown join point
'block_0'` in `initializeRaw`, whose body is the exact `Call.initStackFrame`
application below. Extracting ordinary `@[noinline]` helpers did not resolve
that compiler failure. Evaluation was NEVER observed: there is no interpreter
error, normal-return, or other execution outcome from this diagnostic.

This file establishes no safety, UB-freedom, or ordinary-input theorem. The
fixture's validity is not certified. Any finite successful TreeState diagnostic
is separate evidence and does not establish this call's outcome.

Reproduction prerequisites: use the repository's pinned toolchains and build the
source-bound `duplicate_prefix.Initial` dependency closure with
`tools/check-duplicate-prefix.sh Initial` as described in the repository setup.
Use that invocation's generated output directory (with its current source-bound
artifacts), together with the baseline `lake env printenv LEAN_PATH`, as
`LEAN_PATH`; then run the pinned `lean -j1` on this file. A representative command
shape, after assigning `generated_output` to that verified output directory, is:

```
base=$(lake env printenv LEAN_PATH)
LEAN_PATH="$generated_output:$base" lean -j1 tests/lean/CutoffCallCompileDiagnostic.lean
```

The preserved failure was observed against the source-bound Check377 artifacts.
A generated directory's existence alone is not verification evidence. This file
is deliberately outside aggregate test imports; do not report its compilation
or evaluation as PASS without an actual successful new run.
-/

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.DataStructures
namespace CutoffCallDiagnostic
def tg : Nat → BorTag
 | 0 => ⟨1,by decide⟩
 | 1 => ⟨2,by decide⟩
 | 2 => ⟨3,by decide⟩
 | 3 => ⟨4,by decide⟩
 | 4 => ⟨5,by decide⟩
 | 5 => ⟨6,by decide⟩
 | 6 => ⟨7,by decide⟩
 | 7 => ⟨8,by decide⟩
 | 8 => ⟨9,by decide⟩
 | 9 => ⟨10,by decide⟩
 | _ => ⟨11,by decide⟩
def sz : Size := Size.ofBytes 2
def emptyInside : DedupRangeMap Tree.LocationState := DedupRangeMap.new (Size.ofBytes 0) ⟨.ReservedFrz false,true,.Read⟩
def inside : DedupRangeMap Tree.LocationState := DedupRangeMap.new sz ⟨.ReservedFrz false,true,.Read⟩
def stepChild (t : BorrowTree) (p : ProvenanceExtra) (tag : Nat) (cell empty : Bool) : BorrowTree.ChildInsertResult :=
 t.newChild (Size.ofBytes 0) p (tg tag) (if cell then DedupRangeMap.new sz ⟨.Cell,false,.Write⟩ else if empty then emptyInside else inside) (if cell then .Cell else .ReservedFrz false) false

def snapshot : BorrowTree := Id.run do
 let t := BorrowTree.new (tg 0) sz
 let e := t.exposeTag {} (tg 0)
 let a := stepChild e.tree .wildcard 1 true false
 let dr := a.tree.performBorrowAccessRange (.concrete (tg 1)) (Size.ofBytes 0) sz .Read {} .VisitChildrenOfAccessed
 let d := stepChild dr.tree (.concrete (tg 1)) 2 false false
 let x := d.tree.performBorrowAccessRange (.concrete (tg 0)) (Size.ofBytes 0) sz .Write {} .VisitChildrenOfAccessed
 let b := stepChild x.tree .wildcard 3 true false
 let v := stepChild b.tree (.concrete (tg 2)) 4 false true
 let ev := v.tree.exposeTag {} (tg 4)
 let x2 := ev.tree.performBorrowAccessRange (.concrete (tg 0)) (Size.ofBytes 0) sz .Write {} .VisitChildrenOfAccessed
 let r := x2.tree.performBorrowAccessRange (.concrete (tg 3)) (Size.ofBytes 0) sz .Read {} .VisitChildrenOfAccessed
 let w := stepChild r.tree (.concrete (tg 3)) 5 false false
 return w.tree

def limits : ExecutionMachine.Limits := ⟨1000,1000,1000,1000⟩
def options := DuplicatePrefix.Machine.exampleOptions limits 1000 1000 1000 1000 .Shallow ⟨false,false⟩
abbrev Config := ExecutionMachine.Config MiriMemoryKind DuplicatePrefix.Machine.RootUser Unit Unit ABI.ExternAbi Unit

def execute (cfg : Config) : Nat → MachineHooks.State MiriMemoryKind DuplicatePrefix.Machine.RootUser → String
 | 0,_ => "step budget exhausted"
 | n+1,current =>
   let (next,outcome) := ExecutionMachine.step cfg limits () current
   match outcome with
   | .error e => s!"remaining {n}: {repr e}"
   | .ok false => s!"terminated remaining {n}"
   | .ok true => execute cfg n next

def fixture : Except String (MachineHooks.State MiriMemoryKind DuplicatePrefix.Machine.RootUser × AllocId × AllocId × BorTag) := do
 let initial ← match DuplicatePrefix.Initial.createState DuplicatePrefix.PreparedReflection.actual.initialMemory DuplicatePrefix.Initial.strictEmptyTape DuplicatePrefix.Initial.fixedHost .Shallow with
  | .ok s => pure s
  | .error e => throw (s!"initial: {repr e}")
 let (m1, sid) := initial.machine.memory.reserveAllocId
 let sid ← match sid with | .ok id => pure id | .error e => throw (s!"reserve source: {repr e}")
 let (m2, did) := m1.reserveAllocId
 let did ← match did with | .ok id => pure id | .error e => throw (s!"reserve destination: {repr e}")
 let sa ← match Allocation.fromBytes (Prov := Provenance) #[11,22] Align.ONE .Mut with | .ok a => pure a | .error e => throw (s!"source bytes: {repr e}")
 let da ← match Allocation.fromBytes (Prov := Provenance) #[0] Align.ONE .Mut with | .ok a => pure a | .error e => throw (s!"destination bytes: {repr e}")
 let slotTag : BorTag := ⟨7,by decide⟩
 let nextTag : BorTag := ⟨8,by decide⟩
 let memory := {m2 with live := m2.live ++ #[(sid,⟨.stack,sa.withExtra snapshot⟩),(did,⟨.stack,da.withExtra (BorrowTree.new slotTag (Size.ofBytes 1))⟩)]}
 let addr := initial.machine.user.addresses
 let addr := {addr with baseAddr := addr.baseAddr ++ #[⟨sid,100000⟩,⟨did,100100⟩], intToPtrMap := addr.intToPtrMap ++ #[⟨100000,sid⟩,⟨100100,did⟩], exposed := addr.exposed.push sid}
 let core := initial.machine.user.payload.payload.user
 let extra := core.runtime.extras
 let extra := {extra with allocations := extra.allocations ++ #[(sid,⟨none,#[]⟩),(did,⟨none,#[]⟩)]}
 let core := {core with runtime := {core.runtime with extras := extra}}
 let user := {initial.machine.user with addresses := addr, payload := {initial.machine.user.payload with payload := {initial.machine.user.payload.payload with user := core}}}
 let tracker : MachineHooks.BorrowState := ⟨{nextPointerTag := nextTag,rootPointerTags := #[(sid,tg 0),(did,slotTag)]},.Default⟩
 let machine := {initial.machine with memory, user, borrowTracker := some tracker}
 let state := {initial with machine}
 return (state,sid,did,slotTag)

@[noinline] def initializeRaw (cfg : Config) (state : MachineHooks.State MiriMemoryKind DuplicatePrefix.Machine.RootUser) (abi : FnAbi MIR.TyId) (slice count : OpTy Provenance) (place : MPlaceTy Provenance) :=
 Call.initStackFrame (ExecutionMachine.callHooks cfg limits) () DuplicatePrefix.RootBody.reflected.functionInstance DuplicatePrefix.RootBody.reflected.body abi #[.Copy slice,.Copy count] false (.memory place) (.stop true) state

@[noinline] def initializeAndExecute (cfg : Config) (state : MachineHooks.State MiriMemoryKind DuplicatePrefix.Machine.RootUser) (abi : FnAbi MIR.TyId) (slice count : OpTy Provenance) (place : MPlaceTy Provenance) : String :=
 match initializeRaw cfg state abi slice count place with
 | .error e _ => s!"init error {repr e}"
 | .ok () done =>
   "init succeeds; " ++ execute cfg 200 done

def runWithConfig (cfg : Config) : Except String String := do
 let (state,sid,did,slotTag) ← fixture
 let abi ← match CompilerInstanceAbi.abiOfInstance DuplicatePrefix.PreparedReflection.actual.compiler.lifecycle.instances DuplicatePrefix.RootBody.reflected.functionInstance #[] with | .ok a => pure a | .error e => throw (s!"ABI: {repr e}")
 let sliceLayout ← match DuplicatePrefix.PreparedReflection.actual.runtime.lookup 3 with | .ok l => pure l | .error e => throw (s!"slice layout: {repr e}")
 let usizeLayout ← match DuplicatePrefix.PreparedReflection.actual.runtime.lookup 5 with | .ok l => pure l | .error e => throw (s!"usize layout: {repr e}")
 let boolLayout ← match DuplicatePrefix.PreparedReflection.actual.runtime.lookup 0 with | .ok l => pure l | .error e => throw (s!"bool layout: {repr e}")
 let slice : OpTy Provenance := ⟨.immediate (.scalarPair (Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete sid (tg 5)) (Size.ofBytes 100000))) (Scalar.fromScalarInt (ScalarInt.ofUInt64 2))),sliceLayout⟩
 let count : OpTy Provenance := ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 1))),usizeLayout⟩
 let place : MPlaceTy Provenance := ⟨⟨Pointer.new (some (.concrete did slotTag)) (Size.ofBytes 100100),.none,none⟩,boolLayout⟩
 pure (initializeAndExecute cfg state abi slice count place)

def test : String :=
 match DuplicatePrefix.Machine.actualConfig options () 10000 with
 | .error e => s!"config: {repr e}"
 | .ok cfg => match runWithConfig cfg with | .ok message => message | .error e => e
#eval IO.println test
end CutoffCallDiagnostic
