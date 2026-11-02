import Miri.TreeBorrows.RetagPolicy
/-!
Bounded executable TreeState diagnostic; no theorem about ordinary call inputs
or MIR execution. Start from a fresh two-byte allocation, create the two Cell
roots and an exposed empty Default mutable child below a disabled sibling.
Run explicit parent Reads, newChild operations, and len/as_mut_ptr helper
protector releases before the one-byte copy Read/Write. On the repaired
revision the copy Write must complete.

Policies match implicitWrites=false. The selected helper sequence is based on
GeneralBorrowRawSharedLenEntry, GeneralBorrowFreshRootScopedSharedLenHelperGraph,
and GeneralBorrowExposedScopedInactiveWritableAcceptedSourceGraph. Physical
pointer resolution, typed/compiler metadata, destination setup, and exact MIR
step alignment remain outside this diagnostic. No valid-Rust or whole-call
counterexample is claimed. Run from the repository root:
ELAN_HOME="$PWD/.elan" PATH="$PWD/.elan/bin:$PATH" lake env lean tests/lean/CutoffBorrowTraceDiagnostic.lean
-/
namespace CutoffBorrowTraceDiagnostic
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures

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

def trace : IO Unit := do
 let t := BorrowTree.new (tg 0) sz
 let e := t.exposeTag {} (tg 0)
 IO.println s!"expose0: {repr e.outcome}"
 unless (e.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let a := stepChild e.tree .wildcard 1 true false
 IO.println s!"cellA: {repr a.outcome}"
 unless (a.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let dr := a.tree.performBorrowAccessRange (.concrete (tg 1)) (Size.ofBytes 0) sz .Read {} .VisitChildrenOfAccessed
 IO.println s!"reborrow D read: {repr dr.status}"
 unless (dr.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let d := stepChild dr.tree (.concrete (tg 1)) 2 false false
 IO.println s!"childD: {repr d.outcome}"
 unless (d.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let x := d.tree.performBorrowAccessRange (.concrete (tg 0)) (Size.ofBytes 0) sz .Write {} .VisitChildrenOfAccessed
 IO.println s!"write0: {repr x.status}"
 unless (x.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let b := stepChild x.tree .wildcard 3 true false
 IO.println s!"cellB: {repr b.outcome}"
 unless (b.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let v := stepChild b.tree (.concrete (tg 2)) 4 false true
 IO.println s!"emptyV: {repr v.outcome}"
 unless (v.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let ev := v.tree.exposeTag {} (tg 4)
 IO.println s!"exposeV: {repr ev.outcome}"
 unless (ev.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let x2 := ev.tree.performBorrowAccessRange (.concrete (tg 0)) (Size.ofBytes 0) sz .Write {} .VisitChildrenOfAccessed
 IO.println s!"write0again: {repr x2.status}"
 unless (x2.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let r := x2.tree.performBorrowAccessRange (.concrete (tg 3)) (Size.ofBytes 0) sz .Read {} .VisitChildrenOfAccessed
 IO.println s!"reborrow W read: {repr r.status}"
 unless (r.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let w := stepChild r.tree (.concrete (tg 3)) 5 false false
 IO.println s!"W: {repr w.outcome}"
 unless (w.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let protect : ProtectedTags := ({} : ProtectedTags).insert (tg 6) .StrongProtector
 let fr := w.tree.performBorrowAccessRange (.concrete (tg 5)) (Size.ofBytes 0) sz .Read protect .VisitChildrenOfAccessed
 IO.println s!"FnEntry parent Read: {repr fr.status}"
 unless (fr.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let f := fr.tree.newChild (Size.ofBytes 0) (.concrete (tg 5)) (tg 6) (DedupRangeMap.new sz ⟨.ReservedFrz false,true,.None⟩) (.ReservedFrz false) true
 IO.println s!"FnEntry child: {repr f.outcome}"
 unless (f.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let sr := f.tree.performBorrowAccessRange (.concrete (tg 6)) (Size.ofBytes 0) sz .Read protect .VisitChildrenOfAccessed
 IO.println s!"Shared parent Read: {repr sr.status}"
 unless (sr.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let sh := sr.tree.newChild (Size.ofBytes 0) (.concrete (tg 6)) (tg 7) (DedupRangeMap.new sz ⟨.Frozen,true,.Read⟩) .Frozen false
 IO.println s!"Shared child: {repr sh.outcome}"
 unless (sh.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let lenProtect := protect.insert (tg 8) .StrongProtector
 let lr := sh.tree.performBorrowAccessRange (.concrete (tg 7)) (Size.ofBytes 0) sz .Read lenProtect .VisitChildrenOfAccessed
 IO.println s!"len FnEntry Read: {repr lr.status}"
 unless (lr.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let lc := lr.tree.newChild (Size.ofBytes 0) (.concrete (tg 7)) (tg 8) (DedupRangeMap.new sz ⟨.Frozen,true,.Read⟩) .Frozen true
 IO.println s!"len FnEntry child: {repr lc.outcome}"
 unless (lc.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let le := lc.tree.releaseProtector (tg 8) lenProtect
 IO.println s!"len protector release: {repr le.status}"
 unless (le.status matches .Released) do throw (IO.userError "prefix operation failed")
 let mr := le.tree.performBorrowAccessRange (.concrete (tg 6)) (Size.ofBytes 0) sz .Read protect .VisitChildrenOfAccessed
 IO.println s!"Default parent Read: {repr mr.status}"
 unless (mr.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let m := mr.tree.newChild (Size.ofBytes 0) (.concrete (tg 6)) (tg 9) inside (.ReservedFrz false) false
 IO.println s!"Default mutable child: {repr m.outcome}"
 unless (m.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let mutProtect := protect.insert (tg 10) .StrongProtector
 let ar := m.tree.performBorrowAccessRange (.concrete (tg 9)) (Size.ofBytes 0) sz .Read mutProtect .VisitChildrenOfAccessed
 IO.println s!"as_mut_ptr FnEntry Read: {repr ar.status}"
 unless (ar.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let ac := ar.tree.newChild (Size.ofBytes 0) (.concrete (tg 9)) (tg 10) (DedupRangeMap.new sz ⟨.ReservedFrz false,true,.None⟩) (.ReservedFrz false) true
 IO.println s!"as_mut_ptr FnEntry child: {repr ac.outcome}"
 unless (ac.outcome matches .ok ()) do throw (IO.userError "child insertion/exposure failed")
 let ae := ac.tree.releaseProtector (tg 10) mutProtect
 IO.println s!"as_mut_ptr protector release: {repr ae.status}"
 unless (ae.status matches .Released) do throw (IO.userError "prefix operation failed")
 let cr := ae.tree.performBorrowAccessRange (.concrete (tg 10)) (Size.ofBytes 0) (Size.ofBytes 1) .Read protect .VisitChildrenOfAccessed
 IO.println s!"copy source Read: {repr cr.status}"
 unless (cr.status matches .Completed) do throw (IO.userError "prefix operation failed")
 let y := cr.tree.performBorrowAccessRange (.concrete (tg 10)) (Size.ofBytes 1) (Size.ofBytes 1) .Write protect .VisitChildrenOfAccessed
 IO.println s!"copy destination Write: {repr y.status}"
 unless (y.status matches .Completed) do
   throw (IO.userError "unexpected final status")
 IO.println "Expected repaired finite result: every prefix operation and copy Write completes."
#eval trace
end CutoffBorrowTraceDiagnostic
