import duplicate_prefix.GeneralBorrowSparseLeafCallback
import duplicate_prefix.GeneralBorrowSparseExposedLeafRange
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafVacant
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowSparseExposedLeafState GeneralBorrowSparseLeafCallback
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
open Lean Elab in
elab "sparse_none_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_)=>
    if name.toString.endsWith ".GeneralBorrowExposedConditionalReadExactAccess.iterator" then some name else none
  match names with
  | [name]=>return mkConst name
  | _=>throwError "expected fixed NONE source iterator"

/-- The actual NONE visitor preserves every physically vacant permission row.
Only present leaves are materialized or updated; no successful callback or
vacancy outcome is supplied. The full cache is retained under this stronger
all-local-writable exposed-leaf profile for either Read or Write. -/
theorem location {tree primary extras} (shape : Geometry tree primary extras) (before : LocationTree) (protections : ProtectedTags)
    (raw : Raw tree before protections) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange) :
    let actual:=source_tree_access_at tree before none kind protections mode range
    source_access_status actual=none ∧ Raw tree (source_access_location actual) protections ∧
      (source_access_location actual).exposedCache=before.exposedCache ∧
      (∀query,tree.nodes.get query=none→(source_access_location actual).perms.get query=before.perms.get query) := by
  have one : ∀root∈primary::extras,∀current,Raw tree current protections→∀virtual,
      ∃after,tree.performWildcardAccessAt current root none kind protections virtual=⟨after,.Completed⟩ ∧
        Raw tree after protections ∧ after.exposedCache=current.exposedCache ∧
        (∀query,tree.nodes.get query=none→after.perms.get query=current.perms.get query) := by
    intro root member current ready virtual
    obtain ⟨node,present⟩:=shape.present root member
    obtain ⟨after,actual,coherent,cache,writable,others⟩:=GeneralBorrowSparseLeafCallback.step tree current protections (fun _=>True)
      root node none kind virtual present (shape.nodes root node present).2.1 (shape.nodes root node present).2.2 True.intro
      ready.1 shape.short (by intro query value _ found;exact ready.2 query value found) (by intro tag equal;cases equal)
    refine ⟨after,actual,⟨coherent,(fun query value found=>writable query value True.intro found)⟩,cache,?_⟩
    intro query vacant
    apply others query
    intro equal
    subst query
    rw [show tree.nodes.get root=some node from present] at vacant
    cases vacant
  have tail : ∀roots : List UniIndex,(∀root∈roots,root∈extras)→∀current,Raw tree current protections→
      ∃after,GeneralBorrowWildcardVirtualLeafFold.run tree roots current none kind protections=⟨after,.Completed⟩ ∧
        Raw tree after protections ∧ after.exposedCache=current.exposedCache ∧
        (∀query,tree.nodes.get query=none→after.perms.get query=current.perms.get query) := by
    intro roots
    induction roots with
    | nil=>intro subset current ready;exact ⟨current,rfl,ready,rfl,fun _ _=>rfl⟩
    | cons root rest ih=>
      intro subset current ready
      obtain ⟨middle,called,middleRaw,cache,unchanged⟩:=one root (by simp [subset root (by simp)]) current ready true
      obtain ⟨after,actual,finalRaw,finalCache,finalUnchanged⟩:=ih (fun query member=>subset query (by simp [member])) middle middleRaw
      refine ⟨after,?_,finalRaw,finalCache.trans cache,fun query vacant=>(finalUnchanged query vacant).trans (unchanged query vacant)⟩
      simpa only [GeneralBorrowWildcardVirtualLeafFold.run,called,beq_self_eq_true,ite_true] using actual
  obtain ⟨middle,first,middleRaw,cache,unchanged⟩:=one primary (by simp) before raw false
  obtain ⟨after,completed,finalRaw,finalCache,finalUnchanged⟩:=tail extras (fun _ member=>member) middle middleRaw
  obtain ⟨actual,status⟩:=sparse_none_iterator tree before middle after primary extras kind protections mode range shape.roots first completed
  dsimp only
  rw [actual]
  exact ⟨status,finalRaw,finalCache.trans cache,fun query vacant=>(finalUnchanged query vacant).trans (unchanged query vacant)⟩
end
end DuplicatePrefix.GeneralBorrowSparseExposedLeafVacant
