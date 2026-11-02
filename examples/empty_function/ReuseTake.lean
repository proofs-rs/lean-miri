import empty_function.ReuseCandidate
import empty_function.RawGenerator
namespace EmptyFunction.ReuseTake
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Lean Elab Tactic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private def helper (suffix : String) : TermElabM Name := do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix then some name else none
  let [name] := found | throwError "expected unique source helper {suffix}"
  return name
elab "reuse_actual " suffix:str : term => return mkConst (←helper suffix.getString)
elab "unfold_reuse " suffix:str : tactic => do
  let name ← helper suffix.getString
  evalTactic (← `(tactic| unfold $(mkIdent name)))

theorem ensure_present (pool : ReusePool) (index : Nat) (bounded : index < pool.pool.size) :
    (reuse_actual ".ReusePool.ensureSubpool") pool index = pool := by
  unfold_reuse ".ReusePool.ensureSubpool"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [scan,show ¬pool.pool.size ≤ index from by omega]

theorem checked_alignment (align : Align) (bytes : UInt64)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align) :
    (reuse_actual ".ReusePool.checkedPoolIndex") align = .ok align.pow2 := by
  unfold_reuse ".ReusePool.checkedPoolIndex"
  simp only [metadata,normalized,Except.mapError,bind,Except.bind,pure,Except.pure,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte]

/-- Preparing a present bucket computes its actual current candidate range.
The result may be empty; no request/operation success is assumed. -/
theorem prepare_bucket (pool : ReusePool) (bucket : Array ReusableAddress)
    (size : Size) (align : Align) (bytes : UInt64) (thread : AddressThreadId) (cross : Bool)
    (present : pool.pool[align.pow2]? = some bucket)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true) :
    pool.prepareTakeAddr true cross size align .other thread =
      ⟨pool,.ok (if (ReuseCandidate.candidate bucket size thread cross).2 ==
        (ReuseCandidate.candidate bucket size thread cross).1 then none
        else some (ReuseCandidate.candidate bucket size thread cross))⟩ := by
  have bounded := (Array.getElem?_eq_some_iff.mp present).1
  unfold ReusePool.prepareTakeAddr
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,
    checked_alignment align bytes metadata normalized,bind,pure,
    ensure_present pool align.pow2 bounded]
  unfold_reuse ".ReusePool.subpoolAt"
  unfold_reuse ".ReusePool.getSubpool?"
  simp only [present]
  change (if (ReuseCandidate.candidate bucket size thread cross).2 ==
      (ReuseCandidate.candidate bucket size thread cross).1 then _ else _) = _
  split <;> rfl

/-- No-reuse consumes its Bernoulli draw but skips all pool indexing. -/
theorem no_reuse (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId)
    (cross : Bool) (selection : Nat)
    (allowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate false = true) :
    pool.prepareTakeAddr false cross size align .other thread = ⟨pool,.ok none⟩ ∧
      pool.takeAddr false cross selection size align .other thread = ⟨pool,.ok none⟩ := by
  simp [ReusePool.prepareTakeAddr,ReusePool.takeAddr,allowed]

/-- A raw empty current candidate interval is an actual no-hole result. -/
theorem take_empty (pool : ReusePool) (bucket : Array ReusableAddress)
    (size : Size) (align : Align) (bytes : UInt64) (thread : AddressThreadId)
    (cross : Bool) (selection : Nat)
    (present : pool.pool[align.pow2]? = some bucket)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true)
    (empty : (ReuseCandidate.candidate bucket size thread cross).2 =
      (ReuseCandidate.candidate bucket size thread cross).1) :
    pool.takeAddr true cross selection size align .other thread = ⟨pool,.ok none⟩ := by
  have bounded := (Array.getElem?_eq_some_iff.mp present).1
  unfold ReusePool.takeAddr
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,
    checked_alignment align bytes metadata normalized,bind,pure,
    ensure_present pool align.pow2 bounded]
  unfold_reuse ".ReusePool.subpoolAt"
  unfold_reuse ".ReusePool.getSubpool?"
  simp only [present]
  change (if (ReuseCandidate.candidate bucket size thread cross).2 ==
      (ReuseCandidate.candidate bucket size thread cross).1 then _ else _) = _
  simp only [empty,beq_self_eq_true,↓reduceIte]

/-- Every permitted index of the actual current candidate range produces a
real stored hole. Size/thread checks follow from the source range scan; only
current physical alignment and Bernoulli support are supplied as raw facts. -/
theorem take_bucket (pool : ReusePool) (bucket : Array ReusableAddress)
    (size : Size) (align : Align) (bytes : UInt64) (thread : AddressThreadId)
    (cross : Bool) (selection : Nat)
    (present : pool.pool[align.pow2]? = some bucket)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true)
    (lower : (ReuseCandidate.candidate bucket size thread cross).1 ≤ selection)
    (upper : selection < (ReuseCandidate.candidate bucket size thread cross).2)
    (aligned : ∀ row ∈ bucket, row.address % bytes = 0) :
    ∃ (after : ReusePool) (used : ReusedAddress),
      pool.takeAddr true cross selection size align .other thread = ⟨after,.ok (some used)⟩ ∧
      ∃ row ∈ bucket, used.address = row.address := by
  obtain ⟨bounded,presentEq⟩ := Array.getElem?_eq_some_iff.mp present
  obtain ⟨valid,sizeMatch,threadMatch⟩ := ReuseCandidate.selected bucket size thread cross selection lower upper
  have nonempty : (ReuseCandidate.candidate bucket size thread cross).2 ≠
      (ReuseCandidate.candidate bucket size thread cross).1 := by omega
  have selectedRange : ¬(selection < (ReuseCandidate.candidate bucket size thread cross).1 ∨
      selection ≥ (ReuseCandidate.candidate bucket size thread cross).2) := by omega
  have fits : ¬bucket[selection].size.bytes < size.bytes := by rw [sizeMatch]; exact Std.Irrefl.irrefl _
  have threadOk : (!cross && (bucket[selection].thread != thread)) = false := by
    cases cross
    · simp only [threadMatch rfl,bne_self_eq_false,Bool.and_false]
    · rfl
  let after : ReusePool := {pool with pool := pool.pool.set align.pow2 (bucket.eraseIdx selection valid) bounded}
  let used : ReusedAddress := ⟨bucket[selection].address,
    if bucket[selection].thread == thread then none else some bucket[selection].clock⟩
  refine ⟨after,used,?_,bucket[selection],Array.getElem_mem valid,rfl⟩
  unfold ReusePool.takeAddr
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,
    checked_alignment align bytes metadata normalized,bind,pure,
    ensure_present pool align.pow2 bounded]
  unfold_reuse ".ReusePool.subpoolAt"
  unfold_reuse ".ReusePool.getSubpool?"
  simp only [present]
  unfold_reuse ".ReusePool.updateSubpool"
  simp only [← show ReuseCandidate.candidate bucket size thread cross =
      (reuse_actual ".ReusePool.candidateRange") bucket size thread cross from rfl,
    show ((ReuseCandidate.candidate bucket size thread cross).2 ==
      (ReuseCandidate.candidate bucket size thread cross).1) = false from by simpa using nonempty,
    show (selection < (ReuseCandidate.candidate bucket size thread cross).1 ||
      selection ≥ (ReuseCandidate.candidate bucket size thread cross).2) = false from by simpa using selectedRange,
    valid,bounded,pure,Except.pure,Bool.false_eq_true,↓reduceIte,↓reduceDIte,
    fits,metadata,aligned bucket[selection] (Array.getElem_mem valid),
    bne_self_eq_false,threadOk]
  rfl
end EmptyFunction.ReuseTake
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ReuseTake.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reuse take axiom {dependency} in {name}"
