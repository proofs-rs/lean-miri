import Miri.Input.CompilerConstantQueries
import empty_function.Meaning
namespace EmptyFunction.ConstantTransport
open Miri Miri.Interpreter Miri.Input
set_option maxHeartbeats 800000
theorem singleton_normalization_of_list (evidence : Array CompilerConstantEvidence)
    (fn : CallInstance) (original normalized : MIR.MirConst)
    (known : normalizationFromEvidence evidence fn original = .ok normalized) :
    ∃ e ∈ evidence, normalizationFromEvidence #[e] fn original = .ok normalized := by
  unfold normalizationFromEvidence at known
  cases selected : evidence.find? (fun e => e.fnInstance == fn && e.original == original) with
  | none => simp [selected, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at known
  | some e =>
    have key := Array.find?_some selected
    have member := Array.mem_of_find?_eq_some selected
    simp only [selected] at known
    split at known
    · have result : e.normalized = normalized := by
        simpa only [pure, Except.pure, Except.ok.injEq] using known
      refine ⟨e, member, ?_⟩
      simp [normalizationFromEvidence, key, result, pure, Except.pure]
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at known

def transportedConstantTable (owner : RuntimeProgram) (bodyIndex : Nat)
    (id : MIR.ConstantId) (e : CompilerConstantEvidence) : CompilerConstantQueries.Prepared :=
  ⟨owner, Array.ofFn (fun i : Fin (bodyIndex + 1) =>
    if i.val = bodyIndex then .ok (Array.ofFn (fun j : Fin (id.index + 1) =>
      if j.val = id.index then some (.ok e) else none))
    else .error "legacy body has no mapped evidence"), #[]⟩

theorem transportedConstantTable_lookup (owner : RuntimeProgram) (bodyIndex : Nat)
    (id : MIR.ConstantId) (e : CompilerConstantEvidence) :
    CompilerConstantQueries.lookup (transportedConstantTable owner bodyIndex id e)
      ⟨bodyIndex,id⟩ = .ok e := by
  simp [CompilerConstantQueries.lookup, transportedConstantTable, MIR.SharedTable.lookup,
    bind, Except.bind, pure, Except.pure, Except.mapError]

/-- Local representation transport for the old source-site evidence premise.
This constructs an indexed encoding; it does not identify that encoding with
production reader/preparation output. -/
theorem unit_literal_obligations (owner : RuntimeProgram) (bodyIndex : Nat)
    (tables : MIR.SyntaxTables) (body : MIR.BodyNode) (value : MIR.Body)
    (literal : MIR.ConstOperand) (checked : MIR.Contents.body tables #[] body = .ok value)
    (instruction : ((value.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
      (fun statement => statement.kind) =
        some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes)))
    (evidence : Array CompilerConstantEvidence) (fn : CallInstance)
    (normalization : normalizationFromEvidence evidence fn literal.value = .ok literal.value) :
    ∃ (prepared : CompilerConstantQueries.Prepared) (e : CompilerConstantEvidence),
      prepared.owner = owner ∧
      CompilerConstantQueries.lookup prepared
        ⟨bodyIndex,Meaning.unitConstantId tables body value literal checked instruction⟩ = .ok e ∧
      normalizationFromEvidence #[e] fn literal.value = .ok literal.value := by
  obtain ⟨e,_,normalized⟩ := singleton_normalization_of_list evidence fn _ _ normalization
  refine ⟨transportedConstantTable owner bodyIndex
    (Meaning.unitConstantId tables body value literal checked instruction) e,e,rfl,?_,normalized⟩
  exact transportedConstantTable_lookup _ _ _ _

/-- The new conditional metadata condition admits every successful legacy
normalization represented by this indexed encoding. -/
theorem legacy_domain_inclusion (owner : RuntimeProgram) (bodyIndex : Nat)
    (id : MIR.ConstantId) (evidence : Array CompilerConstantEvidence)
    (fn : CallInstance) (original : MIR.MirConst)
    (known : normalizationFromEvidence evidence fn original = .ok original) :
    ∃ prepared : CompilerConstantQueries.Prepared, prepared.owner = owner ∧
      (∀ e, CompilerConstantQueries.lookup prepared ⟨bodyIndex,id⟩ = .ok e →
        normalizationFromEvidence #[e] fn original = .ok original) := by
  obtain ⟨e,_,normalized⟩ := singleton_normalization_of_list evidence fn original original known
  refine ⟨transportedConstantTable owner bodyIndex id e,rfl,?_⟩
  intro actual query
  have same : e = actual := Except.ok.inj
    ((transportedConstantTable_lookup owner bodyIndex id e).symm.trans query)
  exact same ▸ normalized

/-- Missing typed evidence is admitted by the conditional metadata condition. -/
theorem missing_query_admitted (prepared : CompilerConstantQueries.Prepared)
    (site : CompilerConstantQueries.Site) (message : String)
    (missing : CompilerConstantQueries.lookup prepared site = .error message)
    (fn : CallInstance) (original : MIR.MirConst) :
    ∀ e, CompilerConstantQueries.lookup prepared site = .ok e →
      normalizationFromEvidence #[e] fn original = .ok original := by
  intro e query
  rw [missing] at query
  cases query

#print axioms unit_literal_obligations
#print axioms legacy_domain_inclusion
#print axioms missing_query_admitted
end EmptyFunction.ConstantTransport
