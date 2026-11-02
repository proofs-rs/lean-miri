import duplicate_prefix.ExecutionBernoulliNumericFormation
import duplicate_prefix.ExecutionIndexNumericFormation
import duplicate_prefix.GlobalAddressReuseRawSelection

namespace DuplicatePrefix.CurrentCallConversionChoiceProtocol
open Miri Miri.ABI Miri.Memory Miri.Interpreter
open ExecutionChoices
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The source records exactly one consumed typed choice and its request. -/
def consumed (tape : Tape) (request : Request) (input : Input) : Tape :=
  {tape with cursor:=tape.cursor+1,events:=tape.events.push ⟨request,input⟩}

/-- Supplied inputs work under every existing policy. No generated fallback
can repair a supplied entry of the wrong type, site or support. -/
theorem supplied_index {State : Type} (access : Access State) (state : State)
    (site : IndexSite) (count value : Nat)
    (present : (access.get state).inputs[(access.get state).cursor]?=some (.index site value))
    (valid : value<count) :
    ExecutionChoices.index access site count state=.ok value
      (access.put state (consumed (access.get state) (.index site count) (.index site value))) :=
  ExecutionIndexNumericFormation.index access state site count value valid present

/-- Raw IEEE/rational Bernoulli support describes initial probability data. -/
abbrev BoolSupport := ExecutionBernoulliNumericFormation.Legal

theorem supplied_bool {State : Type} (access : Access State) (state : State)
    (site : BoolSite) (rateBits : UInt64) (value : Bool)
    (present : (access.get state).inputs[(access.get state).cursor]?=some (.boolean site value))
    (support : BoolSupport rateBits value) :
    ExecutionChoices.bernoulli access site rateBits state=.ok value
      (access.put state (consumed (access.get state) (.bernoulli site rateBits) (.boolean site value))) :=
  ExecutionBernoulliNumericFormation.bernoulli access state site rateBits value support present

/-- Ordinary state lenses used by the actual shared choice tape. -/
structure LensLaws {State : Type} (access : Access State) : Prop where
  getPut : ∀state tape,access.get (access.put state tape)=tape
  putPut : ∀state first second,access.put (access.put state first) second=access.put state second

def generated (tape : Tape) (input : Input) (rng : UInt64) : Tape :=
  {tape with inputs:=tape.inputs.push input,generatedChoices:=tape.generatedChoices+1,diagnosticRngState:=rng}

/-- Exhausted-prefix diagnostic generation is only one policy branch of the
protocol; supplied strict and generated prefixes remain covered separately. -/
theorem generated_index {State : Type} (access : Access State) (laws : LensLaws access)
    (state : State) (site : IndexSite) (count maxChoices maxBytes : Nat)
    (policy : (access.get state).policy=.boundedDiagnostic maxChoices maxBytes)
    (exhausted : (access.get state).cursor=(access.get state).inputs.size)
    (budget : (access.get state).generatedChoices<maxChoices) (positive : 0<count) :
    ExecutionChoices.index access site count state=.ok 0
      (access.put state (consumed (generated (access.get state) (.index site 0)
        (access.get state).diagnosticRngState) (.index site count) (.index site 0))) := by
  have missing : (access.get state).inputs[(access.get state).cursor]?=none:=Array.getElem?_eq_none (by omega)
  have cursor : ¬(access.get state).cursor>(access.get state).inputs.size:=by omega
  unfold ExecutionChoices.index
  unfold_internal ".ExecutionChoices.demand"
  unfold_internal ".ExecutionChoices.diagnosticInput"
  unfold_internal ".ExecutionChoices.consume"
  simp [cursor,missing,policy,positive,show ¬maxChoices≤(access.get state).generatedChoices from by omega,
    show ¬count=0 from by omega,consumed,generated,
    pure,Pure.pure,bind,Bind.bind,get,getThe,MonadStateOf.get,EStateM.get,EStateM.bind,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,laws.getPut,laws.putPut]

open Lean Elab in
elab "choice_word" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".Miri.Interpreter.ExecutionChoices.nextDiagnosticWord" then some name else none
  let [name] := names | throwError "expected exactly one source diagnostic word function"
  Lean.Meta.mkConstWithFreshMVarLevels name

/-- The existing source's pure seeded word function, not a new generator. -/
def word : UInt64→UInt64×UInt64 := choice_word

def seededWord (tape : Tape) (seed : UInt64) : UInt64×UInt64 :=
  word (if tape.generatedChoices==0 then seed else tape.diagnosticRngState)

theorem generated_seeded_index {State : Type} (access : Access State) (laws : LensLaws access)
    (state : State) (site : IndexSite) (count maxChoices maxBytes : Nat) (seed : UInt64)
    (policy : (access.get state).policy=.boundedSeededDiagnostic maxChoices maxBytes seed)
    (exhausted : (access.get state).cursor=(access.get state).inputs.size)
    (budget : (access.get state).generatedChoices<maxChoices) (positive : 0<count) :
    let drawn:=seededWord (access.get state) seed
    let input:=Input.index site (drawn.1.toNat%count)
    ExecutionChoices.index access site count state=.ok (drawn.1.toNat%count)
      (access.put state (consumed (generated (access.get state) input drawn.2) (.index site count) input)) := by
  dsimp only
  have missing : (access.get state).inputs[(access.get state).cursor]?=none:=Array.getElem?_eq_none (by omega)
  have cursor : ¬(access.get state).cursor>(access.get state).inputs.size:=by omega
  unfold ExecutionChoices.index
  unfold_internal ".ExecutionChoices.demand"
  unfold_internal ".ExecutionChoices.seededDiagnosticInput"
  unfold_internal ".ExecutionChoices.consume"
  simp [cursor,missing,policy,show ¬maxChoices≤(access.get state).generatedChoices from by omega,
    show ¬count=0 from by omega,consumed,generated,seededWord,word,Nat.mod_lt _ positive,
    pure,Pure.pure,bind,Bind.bind,get,getThe,MonadStateOf.get,EStateM.get,EStateM.bind,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,laws.getPut,laws.putPut]

def threshold (bits : UInt64) : Nat :=
  (ExecutionBernoulliNumericFormation.parts bits).2.1*2^64/(ExecutionBernoulliNumericFormation.parts bits).2.2

def diagnosticBool (bits : UInt64) : Bool := if threshold bits<2^64 then false else true

private theorem diagnostic_legal (bits : UInt64) (valid : ExecutionBernoulliNumericFormation.Valid bits) :
    BoolSupport bits (diagnosticBool bits) := by
  refine ⟨valid,?_⟩
  by_cases low : threshold bits<2^64
  · rw [show diagnosticBool bits=false from ite_eq_left low]
    exact low
  · rw [show diagnosticBool bits=true from ite_eq_right low]
    change 0<threshold bits
    omega

theorem generated_bool {State : Type} (access : Access State) (laws : LensLaws access)
    (state : State) (site : BoolSite) (bits : UInt64) (maxChoices maxBytes : Nat)
    (policy : (access.get state).policy=.boundedDiagnostic maxChoices maxBytes)
    (exhausted : (access.get state).cursor=(access.get state).inputs.size)
    (budget : (access.get state).generatedChoices<maxChoices)
    (valid : ExecutionBernoulliNumericFormation.Valid bits) :
    let value:=diagnosticBool bits
    let input:=Input.boolean site value
    ExecutionChoices.bernoulli access site bits state=.ok value
      (access.put state (consumed (generated (access.get state) input (access.get state).diagnosticRngState)
        (.bernoulli site bits) input)) := by
  dsimp only
  have missing : (access.get state).inputs[(access.get state).cursor]?=none:=Array.getElem?_eq_none (by omega)
  have cursor : ¬(access.get state).cursor>(access.get state).inputs.size:=by omega
  have permits:=ExecutionBernoulliNumericFormation.permits bits valid
  by_cases low : threshold bits<2^64
  · have falseQuery : TerminatorMachine.permitsPreemption bits false=.ok true := by
      rw [permits];simp only [Bool.false_eq_true,↓reduceIte];exact congrArg Except.ok (decide_eq_true low)
    rw [show diagnosticBool bits=false from ite_eq_left low]
    unfold ExecutionChoices.bernoulli
    unfold_internal ".ExecutionChoices.demand"
    unfold_internal ".ExecutionChoices.diagnosticInput"
    unfold_internal ".ExecutionChoices.consume"
    simp [cursor,missing,policy,show ¬maxChoices≤(access.get state).generatedChoices from by omega,
      falseQuery,consumed,generated,pure,Pure.pure,bind,Bind.bind,get,getThe,MonadStateOf.get,EStateM.get,
      EStateM.bind,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,laws.getPut,laws.putPut]
  · have positive : 0<threshold bits:=by omega
    have falseQuery : TerminatorMachine.permitsPreemption bits false=.ok false := by
      rw [permits];simp only [Bool.false_eq_true,↓reduceIte];exact congrArg Except.ok (decide_eq_false low)
    have trueQuery : TerminatorMachine.permitsPreemption bits true=.ok true := by
      rw [permits];simp only [↓reduceIte];exact congrArg Except.ok (decide_eq_true positive)
    rw [show diagnosticBool bits=true from ite_eq_right low]
    unfold ExecutionChoices.bernoulli
    unfold_internal ".ExecutionChoices.demand"
    unfold_internal ".ExecutionChoices.diagnosticInput"
    unfold_internal ".ExecutionChoices.consume"
    simp [cursor,missing,policy,show ¬maxChoices≤(access.get state).generatedChoices from by omega,
      falseQuery,trueQuery,consumed,generated,pure,Pure.pure,bind,Bind.bind,
      get,getThe,MonadStateOf.get,EStateM.get,EStateM.bind,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,laws.getPut,laws.putPut]

def seededBool (bits : UInt64) (random : UInt64) : Bool :=
  if threshold bits<2^64 then
    if 0<threshold bits then decide (random.toNat<threshold bits) else false
  else true

theorem generated_seeded_bool {State : Type} (access : Access State) (laws : LensLaws access)
    (state : State) (site : BoolSite) (bits : UInt64) (maxChoices maxBytes : Nat) (seed : UInt64)
    (policy : (access.get state).policy=.boundedSeededDiagnostic maxChoices maxBytes seed)
    (exhausted : (access.get state).cursor=(access.get state).inputs.size)
    (budget : (access.get state).generatedChoices<maxChoices)
    (valid : ExecutionBernoulliNumericFormation.Valid bits) :
    let drawn:=seededWord (access.get state) seed
    let value:=seededBool bits drawn.1
    let input:=Input.boolean site value
    ExecutionChoices.bernoulli access site bits state=.ok value
      (access.put state (consumed (generated (access.get state) input drawn.2) (.bernoulli site bits) input)) := by
  dsimp only
  have missing : (access.get state).inputs[(access.get state).cursor]?=none:=Array.getElem?_eq_none (by omega)
  have cursor : ¬(access.get state).cursor>(access.get state).inputs.size:=by omega
  have permits:=ExecutionBernoulliNumericFormation.permits bits valid
  have decode:=ExecutionBernoulliNumericFormation.decode bits valid.1
  by_cases low : threshold bits<2^64
  · have falseQuery : TerminatorMachine.permitsPreemption bits false=.ok true := by
      rw [permits];simp only [Bool.false_eq_true,↓reduceIte];exact congrArg Except.ok (decide_eq_true low)
    by_cases positive : 0<threshold bits
    · have trueQuery : TerminatorMachine.permitsPreemption bits true=.ok true := by
        rw [permits];simp only [↓reduceIte];exact congrArg Except.ok (decide_eq_true positive)
      have allQuery : ∀value,TerminatorMachine.permitsPreemption bits value=.ok true := by
        intro value;cases value <;> assumption
      simp only [seededBool,low,positive,↓reduceIte]
      unfold ExecutionChoices.bernoulli
      unfold_internal ".ExecutionChoices.demand"
      unfold_internal ".ExecutionChoices.seededDiagnosticInput"
      unfold_internal ".ExecutionChoices.consume"
      simp [cursor,missing,policy,show ¬maxChoices≤(access.get state).generatedChoices from by omega,
        allQuery,decode,consumed,generated,seededWord,word,threshold,
        pure,Pure.pure,bind,Bind.bind,get,getThe,MonadStateOf.get,EStateM.get,EStateM.bind,EStateM.pure,
        modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,laws.getPut,laws.putPut]
    · have trueQuery : TerminatorMachine.permitsPreemption bits true=.ok false := by
        rw [permits];simp only [↓reduceIte];exact congrArg Except.ok (decide_eq_false positive)
      unfold ExecutionChoices.bernoulli
      unfold_internal ".ExecutionChoices.demand"
      unfold_internal ".ExecutionChoices.seededDiagnosticInput"
      unfold_internal ".ExecutionChoices.consume"
      simp [cursor,missing,policy,show ¬maxChoices≤(access.get state).generatedChoices from by omega,
        falseQuery,trueQuery,seededBool,low,positive,consumed,generated,seededWord,word,
        pure,Pure.pure,bind,Bind.bind,get,getThe,MonadStateOf.get,EStateM.get,EStateM.bind,EStateM.pure,
        modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,laws.getPut,laws.putPut]
  · have positive : 0<threshold bits:=by omega
    have falseQuery : TerminatorMachine.permitsPreemption bits false=.ok false := by
      rw [permits];simp only [Bool.false_eq_true,↓reduceIte];exact congrArg Except.ok (decide_eq_false low)
    have trueQuery : TerminatorMachine.permitsPreemption bits true=.ok true := by
      rw [permits];simp only [↓reduceIte];exact congrArg Except.ok (decide_eq_true positive)
    unfold ExecutionChoices.bernoulli
    unfold_internal ".ExecutionChoices.demand"
    unfold_internal ".ExecutionChoices.seededDiagnosticInput"
    unfold_internal ".ExecutionChoices.consume"
    simp [cursor,missing,policy,show ¬maxChoices≤(access.get state).generatedChoices from by omega,
      falseQuery,trueQuery,seededBool,low,consumed,generated,seededWord,word,
      pure,Pure.pure,bind,Bind.bind,get,getThe,MonadStateOf.get,EStateM.get,EStateM.bind,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,laws.getPut,laws.putPut]

/-- Initial typed index-input data, including all three existing policies. -/
inductive IndexInput (site : IndexSite) (count : Nat) : Tape→Nat→Tape→Prop where
  | supplied (tape : Tape) (value : Nat)
      (present : tape.inputs[tape.cursor]?=some (.index site value)) (valid : value<count) :
      IndexInput site count tape value (consumed tape (.index site count) (.index site value))
  | diagnostic (tape : Tape) (maxChoices maxBytes : Nat)
      (policy : tape.policy=.boundedDiagnostic maxChoices maxBytes)
      (exhausted : tape.cursor=tape.inputs.size) (budget : tape.generatedChoices<maxChoices) (positive : 0<count) :
      IndexInput site count tape 0 (consumed (generated tape (.index site 0) tape.diagnosticRngState)
        (.index site count) (.index site 0))
  | seeded (tape : Tape) (maxChoices maxBytes : Nat) (seed : UInt64)
      (policy : tape.policy=.boundedSeededDiagnostic maxChoices maxBytes seed)
      (exhausted : tape.cursor=tape.inputs.size) (budget : tape.generatedChoices<maxChoices) (positive : 0<count) :
      IndexInput site count tape ((seededWord tape seed).1.toNat%count)
        (consumed (generated tape (.index site ((seededWord tape seed).1.toNat%count)) (seededWord tape seed).2)
          (.index site count) (.index site ((seededWord tape seed).1.toNat%count)))

/-- Initial typed probability-input data; legal supplied values are not fixed
by a preferred seed or a deterministic no-reuse convention. -/
inductive BoolInput (site : BoolSite) (bits : UInt64) : Tape→Bool→Tape→Prop where
  | supplied (tape : Tape) (value : Bool)
      (present : tape.inputs[tape.cursor]?=some (.boolean site value)) (legal : BoolSupport bits value) :
      BoolInput site bits tape value (consumed tape (.bernoulli site bits) (.boolean site value))
  | diagnostic (tape : Tape) (maxChoices maxBytes : Nat)
      (policy : tape.policy=.boundedDiagnostic maxChoices maxBytes)
      (exhausted : tape.cursor=tape.inputs.size) (budget : tape.generatedChoices<maxChoices)
      (valid : ExecutionBernoulliNumericFormation.Valid bits) :
      BoolInput site bits tape (diagnosticBool bits)
        (consumed (generated tape (.boolean site (diagnosticBool bits)) tape.diagnosticRngState)
          (.bernoulli site bits) (.boolean site (diagnosticBool bits)))
  | seeded (tape : Tape) (maxChoices maxBytes : Nat) (seed : UInt64)
      (policy : tape.policy=.boundedSeededDiagnostic maxChoices maxBytes seed)
      (exhausted : tape.cursor=tape.inputs.size) (budget : tape.generatedChoices<maxChoices)
      (valid : ExecutionBernoulliNumericFormation.Valid bits) :
      BoolInput site bits tape (seededBool bits (seededWord tape seed).1)
        (consumed (generated tape (.boolean site (seededBool bits (seededWord tape seed).1)) (seededWord tape seed).2)
          (.bernoulli site bits) (.boolean site (seededBool bits (seededWord tape seed).1)))

theorem IndexInput.read {State : Type} (access : Access State) (laws : LensLaws access) (state : State)
    {site : IndexSite} {count value : Nat} {tape after : Tape}
    (data : IndexInput site count tape value after) (atTape : access.get state=tape) :
    ExecutionChoices.index access site count state=.ok value (access.put state after) := by
  cases data with
  | supplied value present valid => simpa only [atTape] using supplied_index access state site count value (by simpa only [atTape] using present) valid
  | diagnostic maxChoices maxBytes policy exhausted budget positive =>
    simpa only [atTape] using generated_index access laws state site count maxChoices maxBytes
      (by simpa only [atTape] using policy) (by simpa only [atTape] using exhausted) (by simpa only [atTape] using budget) positive
  | seeded maxChoices maxBytes seed policy exhausted budget positive =>
    simpa only [atTape] using generated_seeded_index access laws state site count maxChoices maxBytes seed
      (by simpa only [atTape] using policy) (by simpa only [atTape] using exhausted) (by simpa only [atTape] using budget) positive

theorem BoolInput.read {State : Type} (access : Access State) (laws : LensLaws access) (state : State)
    {site : BoolSite} {bits : UInt64} {value : Bool} {tape after : Tape}
    (data : BoolInput site bits tape value after) (atTape : access.get state=tape) :
    ExecutionChoices.bernoulli access site bits state=.ok value (access.put state after) := by
  cases data with
  | supplied value present legal => simpa only [atTape] using supplied_bool access state site bits value (by simpa only [atTape] using present) legal
  | diagnostic maxChoices maxBytes policy exhausted budget valid =>
    simpa only [atTape] using generated_bool access laws state site bits maxChoices maxBytes
      (by simpa only [atTape] using policy) (by simpa only [atTape] using exhausted) (by simpa only [atTape] using budget) valid
  | seeded maxChoices maxBytes seed policy exhausted budget valid =>
    simpa only [atTape] using generated_seeded_bool access laws state site bits maxChoices maxBytes seed
      (by simpa only [atTape] using policy) (by simpa only [atTape] using exhausted) (by simpa only [atTape] using budget) valid

theorem IndexInput.cursor {site : IndexSite} {count value : Nat} {tape after : Tape}
    (data : IndexInput site count tape value after) : after.cursor=tape.cursor+1 := by cases data <;> rfl

theorem BoolInput.cursor {site : BoolSite} {bits : UInt64} {value : Bool} {tape after : Tape}
    (data : BoolInput site bits tape value after) : after.cursor=tape.cursor+1 := by cases data <;> rfl

theorem IndexInput.bound {site : IndexSite} {count value : Nat} {tape after : Tape}
    (data : IndexInput site count tape value after) : value<count := by
  cases data with
  | supplied _ _ valid=>exact valid
  | diagnostic _ _ _ _ _ positive=>exact positive
  | seeded _ _ _ _ _ _ positive=>exact Nat.mod_lt _ positive

private theorem seeded_legal (bits : UInt64) (random : UInt64)
    (valid : ExecutionBernoulliNumericFormation.Valid bits) : BoolSupport bits (seededBool bits random) := by
  refine ⟨valid,?_⟩
  by_cases low : threshold bits<2^64
  · by_cases positive : 0<threshold bits
    · simp only [seededBool,low,positive,↓reduceIte]
      cases decide (random.toNat<threshold bits) with
      | false=>simp only [Bool.false_eq_true,↓reduceIte];change threshold bits<2^64;exact low
      | true=>simp only [↓reduceIte];change 0<threshold bits;exact positive
    · simp only [seededBool,low,positive,↓reduceIte,Bool.false_eq_true]
      exact low
  · simp only [seededBool,low,↓reduceIte]
    change 0<threshold bits
    omega

theorem BoolInput.legal {site : BoolSite} {bits : UInt64} {value : Bool} {tape after : Tape}
    (data : BoolInput site bits tape value after) : BoolSupport bits value := by
  cases data with
  | supplied _ _ legal=>exact legal
  | diagnostic _ _ _ _ _ valid=>exact diagnostic_legal bits valid
  | seeded _ _ _ _ _ _ valid=>exact seeded_legal bits _ valid

/-- One uncached non-TypeId managed address uses precisely these source sites.
The range is the pure selected pool view, instantiated by the address leaf. -/
structure AddressBlock (reuseBits crossBits : UInt64) (range : Bool→Bool→Option (Nat×Nat)) (tape : Tape) where
  reuse : Bool
  cross : Bool
  afterReuse : Tape
  afterCross : Tape
  afterIndex : Tape
  reuseInput : BoolInput .addressReuse reuseBits tape reuse afterReuse
  crossInput : if reuse then BoolInput .addressCrossThread crossBits afterReuse cross afterCross
    else cross=false ∧afterCross=afterReuse
  index : Nat
  indexInput : match range reuse cross with
    | none=>IndexInput .addressSlack 16 afterCross index afterIndex
    | some (begin,stop)=>IndexInput .addressPool (stop-begin) afterCross index afterIndex

theorem AddressBlock.cursor {reuseBits crossBits : UInt64} {range : Bool→Bool→Option (Nat×Nat)} {tape : Tape}
    (block : AddressBlock reuseBits crossBits range tape) : block.afterIndex.cursor≤tape.cursor+3 := by
  have reuse:=block.reuseInput.cursor
  have index : block.afterIndex.cursor=block.afterCross.cursor+1 := by
    cases selected : range block.reuse block.cross with
    | none => exact (by simpa only [selected] using block.indexInput : IndexInput .addressSlack 16 block.afterCross block.index block.afterIndex).cursor
    | some interval => exact (by simpa only [selected] using block.indexInput : IndexInput .addressPool (interval.2-interval.1) block.afterCross block.index block.afterIndex).cursor
  cases selected : block.reuse with
  | false => have same:=(by simpa only [selected,Bool.false_eq_true,↓reduceIte] using block.crossInput : block.cross=false ∧block.afterCross=block.afterReuse).2;rw [same] at index;omega
  | true => have cross:=(by simpa only [selected,↓reduceIte] using block.crossInput : BoolInput .addressCrossThread crossBits block.afterReuse block.cross block.afterCross).cursor;omega

open Miri.Memory.AllocAddresses
open GlobalAddressAlignedBumpFormation GlobalAddressReusePairwise GlobalAddressReuseContents

/-- Current allocator representation, not a restriction on Rust arguments.
Only supported alignment buckets matter; no bucket ordering is demanded. -/
def BucketsAligned (pool : ReusePool) : Prop :=
  ∀bucket index entry,bucket≤29→peek pool.pool (bucket,index)=some entry→
    entry.address%(alignment ⟨bucket⟩)=0

theorem BucketsAligned.ensure (pool : ReusePool) (index : Nat) (initial : BucketsAligned pool) :
    BucketsAligned (source_reuse_ensure pool index) := by
  intro bucket selected entry bounded present
  rw [GlobalAddressReusePairwise.ensure_peek] at present
  exact initial bucket selected entry bounded present

theorem ensure_bounds (pool : ReusePool) (index : Nat) :
    index<(source_reuse_ensure pool index).pool.size := by
  unfold_internal ".ReusePool.ensureSubpool"
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have sound : ∀bound buckets,index+1-buckets.size=bound→
      index<(Lean.Loop.forIn {} buckets scan).size := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro buckets measured
      rw [Lean.Loop.forIn_eq_of_monadTail]
      by_cases grow : buckets.size≤index
      · have smaller : index+1-(buckets.push #[]).size<bound:=by simp only [Array.size_push];omega
        simpa only [scan,grow,↓reduceIte,bind,pure] using ih _ smaller (buckets.push #[]) rfl
      · simp only [scan,grow,↓reduceIte,bind,pure]
        omega
  exact sound _ pool.pool rfl

theorem BucketsAligned.shortage (pool : ReusePool) (initial : BucketsAligned pool) :
    BucketsAligned pool.addressSpaceShortage := by
  unfold ReusePool.addressSpaceShortage
  split <;> exact initial

theorem BucketsAligned.erased (pool : ReusePool) (alignmentIndex : Nat) (bucket : Array ReusableAddress)
    (stored : pool.pool[alignmentIndex]?=some bucket) (selected : Nat) (within : selected<bucket.size)
    (initial : BucketsAligned pool) :
    BucketsAligned {pool with pool:=(pool.pool.set alignmentIndex (bucket.eraseIdx selected within)
      (Array.getElem?_eq_some_iff.mp stored).1)} := by
  intro otherIndex otherSelected entry supported present
  let valid:alignmentIndex<pool.pool.size:=(Array.getElem?_eq_some_iff.mp stored).1
  change peek (pool.pool.set alignmentIndex (bucket.eraseIdx selected within) valid) (otherIndex,otherSelected)=some entry at present
  rw [GlobalAddressReusePairwise.erased_peek pool alignmentIndex valid bucket stored selected within] at present
  have first : (GlobalAddressReusePairwise.lift alignmentIndex selected (otherIndex,otherSelected)).1=otherIndex := by
    by_cases same : otherIndex=alignmentIndex <;> simp [GlobalAddressReusePairwise.lift,same]
  have old:=initial (GlobalAddressReusePairwise.lift alignmentIndex selected (otherIndex,otherSelected)).1
    (GlobalAddressReusePairwise.lift alignmentIndex selected (otherIndex,otherSelected)).2 entry
    (by rw [first];exact supported) present
  simpa only [first] using old

/-- The exact pure pool interval used before an index request. Empty appended
buckets have the same range as an absent bucket; no conversion is executed. -/
def poolRange (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId)
    (reuse cross : Bool) : Option (Nat×Nat) :=
  if reuse then
    let bucket := pool.pool[align.pow2]?.getD #[]
    let interval:=GlobalAddressReuseRawSelection.range bucket size thread cross
    if interval.2==interval.1 then none else some interval
  else none

abbrev ManagedBlock (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (tape : Tape) :=
  AddressBlock pool.addressReuseRate.toBits pool.addressReuseCrossThreadRate.toBits
    (poolRange pool size align thread) tape

/-- Pure cache data update used in the initial relocation plan. The address
leaf proves it agrees with the real checked insertion, rather than assuming
that insertion succeeds. -/
def cacheData (addresses : GlobalAddressState) (id : AllocId) (address : UInt64) : GlobalAddressState :=
  let next:={addresses with baseAddr:=(addresses.baseAddr.filter (fun row=>row.allocId != id)).push ⟨id,address⟩}
  if address==0 then next else
    let cut:=((reuse_source ".GlobalAddressState.findInverseIndex") addresses.intToPtrMap address).1
    {next with intToPtrMap:=addresses.intToPtrMap.insertIdxIfInBounds cut ⟨address,id⟩}

/-- Arithmetic and pool data only; no interpreter outcome occurs in the plan.
Invalid selected-slot branches are ruled out by the actual candidate-range
lemma and typed index support when proving adequacy. -/
def advance (addresses : GlobalAddressState) (generation : AddressGenerationState) (id : AllocId)
    (info : AllocationInfo) (thread : AddressThreadId) (tape : Tape)
    (block : ManagedBlock generation.reusePool info.size info.align thread tape) : GlobalAddressState :=
  let prepared:=if block.reuse then (source_reuse_ensure generation.reusePool info.align.pow2) else generation.reusePool
  match poolRange generation.reusePool info.size info.align thread block.reuse block.cross with
  | none=>
    let slack : Fin 16:=⟨block.index%16,Nat.mod_lt _ (by decide)⟩
    let generator:=GlobalAddressAlignedBumpFormation.next generation.generator info.size info.align slack
    let pool:=if generator.nextBaseAddr>generator.endAddr/2 then prepared.addressSpaceShortage else prepared
    cacheData {addresses with generation:=some ⟨generator,pool⟩} id
      (GlobalAddressAlignedBumpFormation.base generation.generator info.align slack)
  | some (begin,_)=>
    let bucket:=prepared.pool[info.align.pow2]?.getD #[]
    let selected:=begin+block.index
    match bucket[selected]? with
    | none=>addresses
    | some entry=>
      let buckets:=if valid:info.align.pow2<prepared.pool.size then
        prepared.pool.set info.align.pow2 (bucket.eraseIdxIfInBounds selected) valid else prepared.pool
      cacheData {addresses with generation:=some {generation with reusePool:={prepared with pool:=buckets}}} id entry.address

/-- Initial typed-input replay for the exact selected relocation ID list.
It mentions only current metadata, pure cache/pool data and input support.
The domain supplies the selected payload order; conservative budget target
supersets are deliberately not consumed as choice requests. -/
inductive AddressProtocol {K : Type} (memory : MemoryState Provenance TreeBorrows.BorrowTree K)
    (thread : AddressThreadId) : GlobalAddressState→Tape→List AllocId→GlobalAddressState→Tape→Prop where
  | nil (addresses : GlobalAddressState) (tape : Tape) : AddressProtocol memory thread addresses tape [] addresses tape
  | cached (addresses : GlobalAddressState) (tape : Tape) (id : AllocId) (rest : List AllocId)
      (base : BaseAddressEntry) (cached : addresses.baseAddr.find? (fun row=>row.allocId==id)=some base)
      (final : GlobalAddressState) (after : Tape) (tail : AddressProtocol memory thread addresses tape rest final after) :
      AddressProtocol memory thread addresses tape (id::rest) final after
  | typeId (addresses : GlobalAddressState) (tape : Tape) (id : AllocId) (rest : List AllocId) (info : AllocationInfo)
      (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
      (metadata : memory.getAllocInfo id=.ok info) (kind : info.kind=.typeId)
      (final : GlobalAddressState) (after : Tape)
      (tail : AddressProtocol memory thread (cacheData addresses id 0) tape rest final after) :
      AddressProtocol memory thread addresses tape (id::rest) final after
  | managed (addresses : GlobalAddressState) (tape : Tape) (id : AllocId) (rest : List AllocId) (info : AllocationInfo)
      (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
      (metadata : memory.getAllocInfo id=.ok info) (kind : info.kind≠.typeId)
      (generation : AddressGenerationState) (generationEq : addresses.generation=some generation)
      (block : ManagedBlock generation.reusePool info.size info.align thread tape)
      (final : GlobalAddressState) (after : Tape)
      (tail : AddressProtocol memory thread (advance addresses generation id info thread tape block)
        block.afterIndex rest final after) :
      AddressProtocol memory thread addresses tape (id::rest) final after

end DuplicatePrefix.CurrentCallConversionChoiceProtocol
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionChoiceProtocol" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved address choice protocol dependency {dependency}"
