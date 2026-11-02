import duplicate_prefix.CurrentCallConversionAddressFrames
import duplicate_prefix.GlobalRelocationFiniteConversion
import duplicate_prefix.GlobalAddressReuseRawSelection
import duplicate_prefix.CurrentCallConversionChoiceProtocol
import duplicate_prefix.CurrentCallConversionProbability
import duplicate_prefix.CurrentCallConversionRootPointer
import duplicate_prefix.CurrentCallConversionRows
import duplicate_prefix.CurrentCallConversionBudgetPotential
import duplicate_prefix.CurrentCallConversionAdvanceNumeric
import duplicate_prefix.CurrentCallConversionBoolQueryFrame

namespace DuplicatePrefix.CurrentCallConversionFiniteFold
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open GlobalRelocationFiniteLoop GlobalRelocationSourceExtraction
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressReusePoolFrontier
open GlobalAddressBumpRangeFormation (Frontier)
open WildcardEmptyFamilyFormation (Apart)

/-- Proof-local converter invariant: no inverse allocation-ID uniqueness and
no memory/static-only target restriction. -/
private structure ManagedRows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState) : Prop where
  ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap
  apart : Apart addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory)
  rows : CurrentCallConversionInfoRows.InfoRows memory addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory)
  generationEq : addresses.generation=some generation
  managed : addresses.addressMode=.managed
  cursor : generation.generator.nextBaseAddr≠0
  frontier : Frontier addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory) generation.generator
  holes : Contents generation.reusePool (Hole addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory))
  bounded : Contents generation.reusePool (Bounded generation.generator)
  pairwise : GlobalAddressReusePairwise.Pairwise generation.reusePool

private theorem initial_rows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State memory addresses generation sizes) :
    ManagedRows memory addresses generation := by
  obtain ⟨rows,equal⟩:=CurrentCallConversionInfoRows.embed initial.resources
  exact ⟨initial.resources.recurring.ordered,CurrentCallConversionInfoRows.apart _ sizes equal initial.resources.apart,
    rows,initial.generationEq,initial.managed,initial.cursor,
    CurrentCallConversionInfoRows.frontier _ sizes equal _ initial.frontier,
    CurrentCallConversionInfoRows.holes _ sizes equal _ initial.holes,initial.bounded,initial.pairwise⟩

private theorem stage_rows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation next : AddressGenerationState)
    (initial : ManagedRows memory addresses generation)
    (cursor : next.generator.nextBaseAddr≠0)
    (frontier : Frontier addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory) next.generator)
    (holes : Contents next.reusePool (Hole addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory)))
    (bounded : Contents next.reusePool (Bounded next.generator))
    (pairwise : GlobalAddressReusePairwise.Pairwise next.reusePool) :
    ManagedRows memory {addresses with generation:=some next} next :=
  ⟨initial.ordered,initial.apart,initial.rows,rfl,initial.managed,cursor,frontier,holes,bounded,pairwise⟩

private theorem cache_rows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (initial : ManagedRows memory addresses generation) (id : AllocId)
    (target : GlobalAddressLiveErrorExclusion.Supplier memory id)
    (address : UInt64) (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (positive : address≠0) (cut : Nat)
    (partition : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address cut)
    (placement : GlobalAddressRangeFormation.Placement addresses.intToPtrMap
      (CurrentCallConversionInfoRows.sizes memory) id address cut)
    (bound : address.toNat+max 1 (CurrentCallConversionInfoRows.sizes memory id).bytes.toNat≤generation.generator.nextBaseAddr.toNat)
    (holes : Contents generation.reusePool (Hole
      (addresses.intToPtrMap.insertIdx cut ⟨address,id⟩ partition.1) (CurrentCallConversionInfoRows.sizes memory))) :
    (addresses.cacheAddress id address).outcome=.ok () ∧
      ManagedRows memory (addresses.cacheAddress id address).state generation := by
  have ordered:=GlobalAddressExposureFormation.cache_ordered_completed addresses id address uncached positive cut partition initial.ordered
  have apart:=GlobalAddressRangeFormation.cache addresses _ initial.apart id address uncached positive cut partition placement
  have inverse:=GlobalAddressManagedBumpState.cache_inverse addresses id address uncached positive cut partition
  refine ⟨ordered.1,⟨ordered.2,apart.2,?_,?_,?_,initial.cursor,?_,?_,initial.bounded,initial.pairwise⟩⟩
  · rw [inverse]
    exact CurrentCallConversionInfoRows.insert _ initial.rows id target address cut partition.1
  · unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [uncached,Option.map_none]
    split <;> try exact initial.generationEq
    split <;> split <;> try exact initial.generationEq
    all_goals split <;> exact initial.generationEq
  · unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [uncached,Option.map_none]
    split <;> try exact initial.managed
    split <;> split <;> try exact initial.managed
    all_goals split <;> exact initial.managed
  · rw [inverse]
    intro row member
    rcases Array.mem_insertIdx.mp member with equal | old
    · subst row
      exact bound
    · exact initial.frontier row old
  · rw [inverse]
    exact holes

open GlobalAddressAlignedBumpFormation

private def ManagedPost {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) : Prop :=
  ∃generation,ManagedRows memory addresses generation

private theorem returned_rows {K : Type} (memory : MemoryState Provenance BorrowTree K) (staged : GlobalAddressState)
    (id : AllocId) (address : UInt64)
    (good : ManagedPost memory (staged.cacheAddress id address).state) (clockResult : Except String Unit) :
    ManagedPost memory (GlobalAddressState.completeAcquire (match (staged.cacheAddress id address).outcome with
      | .ok _=>⟨(staged.cacheAddress id address).state,.ok (.ready address)⟩
      | .error error=>⟨(staged.cacheAddress id address).state,.error error⟩) clockResult).state := by
  cases (staged.cacheAddress id address).outcome <;> exact good

private theorem managed_rows {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (initial : ManagedRows memory addresses generation)
    (id : AllocId) (target : GlobalAddressLiveErrorExclusion.Supplier memory id)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (align : Align) (valid : align.pow2≤29) (kind : AddressMemoryKind) (thread : AddressThreadId) (choices : AddressRandomChoices)
    (room : Room generation.generator (CurrentCallConversionInfoRows.sizes memory id) align choices.slack)
    (clockResult : Except String Unit) :
    ManagedPost memory (GlobalAddressState.completeAcquire (addresses.addrFromAllocId id
      (some (GlobalAddressAlignedManagedFormation.info (CurrentCallConversionInfoRows.sizes memory id) align kind thread)) choices)
        clockResult).state := by
  let sizes:=CurrentCallConversionInfoRows.sizes memory
  let size:=sizes id
  have sizeEq : sizes id=size:=rfl
  let taken:=generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread
  have takeFacts:=GlobalAddressReuseHoleGeometry.take_separated generation.reusePool addresses.intToPtrMap sizes initial.holes initial.ordered id size sizeEq
    choices.reuse choices.crossThread choices.poolIndex align kind thread
  have pairFacts:=GlobalAddressReuseTakePairwise.take generation.reusePool (Hole addresses.intToPtrMap sizes) initial.holes initial.pairwise choices.reuse choices.crossThread choices.poolIndex size align kind thread
  have boundFacts:=GlobalAddressReusePoolFrontier.take generation.reusePool generation.generator initial.bounded choices.reuse choices.crossThread choices.poolIndex size align kind thread
  let afterTake:={addresses with generation:=some {generation with reusePool:=taken.state}}
  have afterTakeGood : ManagedRows memory afterTake {generation with reusePool:=taken.state} :=
    stage_rows memory addresses generation _ initial initial.cursor initial.frontier takeFacts.1 boundFacts.1 pairFacts.1
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,initial.managed,initial.generationEq,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,pure]
  simp only [←initial.managed]
  cases outcome : (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread).outcome with
  | error error => exact ⟨_,afterTakeGood⟩
  | ok optional =>
    try dsimp only
    cases optional with
    | none =>
      try dsimp only
      have bump:=generated generation.generator size align valid choices.slack room
      dsimp only [size,sizes] at bump
      try simp only [bump]
      have geometry:=placement addresses.intToPtrMap sizes generation.generator initial.frontier id size align valid choices.slack room
      have positive : base generation.generator align choices.slack≠0 := by
        intro zero
        have lower:=(base_bounds generation.generator size align valid choices.slack room).1
        rw [zero] at lower
        change generation.generator.nextBaseAddr.toNat+choices.slack.val≤0 at lower
        have nz : generation.generator.nextBaseAddr.toNat≠0 := by intro eq;exact initial.cursor (UInt64.toNat_inj.mp eq)
        omega
      have nextValue:=next_nat generation.generator size align valid choices.slack room
      have grows : generation.generator.nextBaseAddr.toNat≤(next generation.generator size align choices.slack).nextBaseAddr.toNat := by
        have lower:=(base_bounds generation.generator size align valid choices.slack room).1
        omega
      have nextPositive : (next generation.generator size align choices.slack).nextBaseAddr≠0 := by
        intro zero
        have nz : generation.generator.nextBaseAddr.toNat≠0 := by intro eq;exact initial.cursor (UInt64.toNat_inj.mp eq)
        rw [zero] at grows
        change generation.generator.nextBaseAddr.toNat≤0 at grows
        omega
      let nextPool:=if (next generation.generator size align choices.slack).nextBaseAddr > (next generation.generator size align choices.slack).endAddr/2 then taken.state.addressSpaceShortage else taken.state
      let nextGeneration:AddressGenerationState:=⟨next generation.generator size align choices.slack,nextPool⟩
      let staged:={addresses with generation:=some nextGeneration}
      have poolSame : nextPool.pool=taken.state.pool := by
        unfold nextPool
        split
        · unfold ReusePool.addressSpaceShortage;split <;> rfl
        · rfl
      have stagedGood : ManagedRows memory staged nextGeneration := by
        apply stage_rows memory addresses generation nextGeneration initial nextPositive
        · intro row member
          have old:=initial.frontier row member
          exact Nat.le_trans old grows
        · change Contents nextPool _
          unfold Contents
          rw [poolSame]
          exact takeFacts.1
        · have mono:=GlobalAddressReusePoolFrontier.mono taken.state generation.generator _ boundFacts.1 grows
          change Contents nextPool _
          unfold Contents
          rw [poolSame]
          exact mono
        · change GlobalAddressReusePairwise.Pairwise nextPool
          unfold GlobalAddressReusePairwise.Pairwise
          rw [poolSame]
          exact pairFacts.1
      have newHoles : Contents nextPool (Hole (addresses.intToPtrMap.insertIdx addresses.intToPtrMap.size ⟨base generation.generator align choices.slack,id⟩ geometry.1.1) sizes) := by
        unfold Contents
        rw [poolSame]
        exact fresh_insert taken.state addresses.intToPtrMap sizes generation.generator takeFacts.1 boundFacts.1 id size align valid choices.slack room _ geometry.1.1
      have cached:=cache_rows memory staged nextGeneration stagedGood id target _ uncached positive _ geometry.1 geometry.2 (Nat.le_of_eq nextValue.symm) newHoles
      try simp only [←initial.managed]
      change ManagedPost memory (GlobalAddressState.completeAcquire (match (staged.cacheAddress id (base generation.generator align choices.slack)).outcome with
        | .ok _ => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id (base generation.generator align choices.slack)).state,.ok (.ready (base generation.generator align choices.slack))⟩)
        | .error error => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id (base generation.generator align choices.slack)).state,.error error⟩)) clockResult).state
      exact returned_rows memory staged id _ ⟨_,cached.2⟩ clockResult
    | some used =>
      try dsimp only
      obtain ⟨positive,cut,partition,placement⟩:=takeFacts.2 used outcome
      obtain ⟨entry,_,same,fits,remaining⟩:=pairFacts.2.2 used outcome
      have inserted:=GlobalAddressReuseInsertedHoles.take generation.reusePool addresses.intToPtrMap sizes initial.holes initial.pairwise choices.reuse choices.crossThread choices.poolIndex size align kind thread id sizeEq
      have newHoles:=inserted.2 used outcome cut partition.1
      have bound:=boundFacts.2 used outcome
      have cached:=cache_rows memory afterTake _ afterTakeGood id target used.address uncached positive cut partition placement bound newHoles
      cases clock : used.clockToAcquire with
      | some clock =>
        dsimp only
        cases clockResult with
        | error message => exact ⟨_,afterTakeGood⟩
        | ok value =>
          cases value
          try simp only [←initial.managed]
          change ManagedPost memory (match (afterTake.cacheAddress id used.address).outcome with
            | .ok _ => (show AddressStateResult AddressAssignment from ⟨(afterTake.cacheAddress id used.address).state,.ok (.ready used.address)⟩)
            | .error error => (show AddressStateResult AddressAssignment from ⟨(afterTake.cacheAddress id used.address).state,.error error⟩)).state
          cases (afterTake.cacheAddress id used.address).outcome <;> exact ⟨_,cached.2⟩
      | none =>
        dsimp only
        try simp only [←initial.managed]
        exact returned_rows memory afterTake id used.address ⟨_,cached.2⟩ clockResult

private theorem range_shape (entries : Array ReusableAddress) (size : Size) (thread : AddressThreadId)
    (cross : Bool) :
    (GlobalAddressReuseRawSelection.range entries size thread cross).1≤(GlobalAddressReuseRawSelection.range entries size thread cross).2 ∧
    ∀selected,(GlobalAddressReuseRawSelection.range entries size thread cross).1≤selected→
      selected<(GlobalAddressReuseRawSelection.range entries size thread cross).2→
      ∃entry,entries[selected]?=some entry ∧entry.size.bytes=size.bytes ∧(cross=false→entry.thread=thread) := by
  unfold GlobalAddressReuseRawSelection.range
  unfold_internal ".ReusePool.candidateRange"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let begin : Nat := (reuse_source ".ReusePool.partitionPoint") entries fun entry=>
    entry.size.bytes<size.bytes || (entry.size.bytes==size.bytes && !cross && entry.thread<thread)
  let good : Nat×Bool→Prop := fun state=>begin≤state.1 ∧∀selected,begin≤selected→selected<state.1→
    ∃entry,entries[selected]?=some entry ∧entry.size.bytes=size.bytes ∧(cross=false→entry.thread=thread)
  let measure : Nat×Bool→Nat := fun state=>if state.2 then (entries.size+1-state.1)+1 else 0
  have step : ∀state,good state→
      (∃final,scan () state=.done final ∧good final) ∨
      ∃next,scan () state=.yield next ∧good next ∧measure next<measure state := by
    rintro ⟨offset,running⟩ initial
    cases running with
    | false => exact Or.inl ⟨(offset,false),by simp [scan],initial⟩
    | true =>
      have atEq : (reuse_source ".ReusePool.entryAt?") entries offset=entries[offset]?:=rfl
      cases found : entries[offset]? with
      | none => exact Or.inr ⟨(offset,false),by simp [scan,atEq,found],initial,by simp [measure]⟩
      | some entry =>
        by_cases bad : (entry.size.bytes != size.bytes || !cross && entry.thread != thread)=true
        · exact Or.inr ⟨(offset,false),by simp only [scan,atEq,found,bad,↓reduceIte],initial,by simp [measure]⟩
        · have sizeEq : entry.size.bytes=size.bytes := by
            by_cases equal : entry.size.bytes=size.bytes
            · exact equal
            · exact False.elim (bad (by simp [equal]))
          have threadEq : cross=false→entry.thread=thread := by
            intro c
            by_cases equal : entry.thread=thread
            · exact equal
            · exact False.elim (bad (by simp [c,equal]))
          have bounded : offset<entries.size:=(Array.getElem?_eq_some_iff.mp found).1
          refine Or.inr ⟨(offset+1,true),by simp only [scan,atEq,found,bad,Bool.false_eq_true,↓reduceIte],?_,?_⟩
          · refine ⟨by have old:=initial.1;omega,?_⟩
            intro selected lower upper
            by_cases equal : selected=offset
            · subst selected;exact ⟨entry,found,sizeEq,threadEq⟩
            · exact initial.2 selected lower (by omega)
          · simp only [measure,↓reduceIte]
            omega
  have final:=GeneralBorrowLoop.invariant scan measure good step (begin,true)
    (by refine ⟨Nat.le_refl _,?_⟩;intro selected lower upper;omega)
  exact final

private abbrev ActualControl := Miri.Input.EvalPointerSource.Control Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost
private abbrev ActualMachine := MachineAddress.State Miri.Memory.MiriMemoryKind ActualControl
private def actualTape : ExecutionChoices.Access ActualMachine := Miri.Input.EvalPointerSource.tape

private theorem actual_tape_laws : CurrentCallConversionChoiceProtocol.LensLaws actualTape :=
  ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩

private def withAddresses (machine : ActualMachine) (addresses : GlobalAddressState) : ActualMachine :=
  {machine with user:={machine.user with addresses}}

private def addressMachine (machine : ActualMachine) (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) : ActualMachine :=
  withAddresses (actualTape.put machine tape) addresses

private theorem actual_tape_get (machine : ActualMachine) : actualTape.put machine (actualTape.get machine)=machine := rfl

private theorem keyed_found {V : Type} {key : V→UInt64} (table : KeyedArray UInt64 V key) (id : UInt64) (value : V)
    (found : table.find? id=some value) : table.contains id=true := by
  unfold KeyedArray.contains
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  change (((reuse_source ".KeyedArray.indexState") table).2.get? id).isSome=true
  cases present : ((reuse_source ".KeyedArray.indexState") table).2.get? id with
  | some indices=>rfl
  | none=>
    unfold KeyedArray.find? at found
    simp only [present,bind,Option.bind] at found
    cases found

private theorem keyed_any {V : Type} {key : V→UInt64} (table : KeyedArray UInt64 V key) (id : UInt64) (predicate : V→Bool)
    (found : table.any? id predicate=true) : table.contains id=true := by
  unfold KeyedArray.contains
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  change (((reuse_source ".KeyedArray.indexState") table).2.get? id).isSome=true
  cases present : ((reuse_source ".KeyedArray.indexState") table).2.get? id with
  | some indices=>rfl
  | none=>
    unfold KeyedArray.any? at found
    simp only [present,Id.run,pure] at found
    cases found

private theorem supplier_live {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (supplier : GlobalAddressLiveErrorExclusion.Supplier memory id) : memory.isAllocLive id=true := by
  cases supplier with
  | localRow entry present =>
    have live:=MemoryCopyBridge.live_any_of_present memory id entry present
    simp only [MemoryState.isAllocLive,live,Bool.true_or]
  | functionRow absent present =>
    simp only [MemoryState.hasFunctionPointer,Bool.or_eq_true] at present
    rcases present with present | present
    · simp only [MemoryState.isAllocLive,present,Bool.true_or,Bool.or_true]
    · have live:=keyed_any _ id.value _ present
      simp only [MemoryState.isAllocLive,live,Bool.or_true]
  | vaListRow absent noFunction present =>
    unfold MemoryState.hasVaListId at present
    simp only [MemoryState.isAllocLive,present,Bool.or_true,Bool.true_or]
  | globalRow descriptor absent noFunction noVaList present =>
    unfold MemoryState.findGlobal? at present
    have live:=keyed_found _ id.value descriptor present
    simp only [MemoryState.isAllocLive,live,Bool.or_true]

private theorem cached_address (hooks : MachineAddress.Hooks Miri.Memory.MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (base : BaseAddressEntry)
    (hit : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base) :
    MachineAddress.addrFromAllocId actualTape hooks id (some .other) machine=.ok base.address machine := by
  simp only [MachineAddress.addrFromAllocId,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,hit]

private theorem cache_zero (addresses : GlobalAddressState) (id : AllocId)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none) :
    addresses.cacheAddress id 0=⟨CurrentCallConversionChoiceProtocol.cacheData addresses id 0,.ok ()⟩ := by
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.insertBase"
  simp only [uncached,Option.map_none,CurrentCallConversionChoiceProtocol.cacheData,
    beq_self_eq_true,↓reduceIte,Id.run,pure]

private theorem type_id_address (hooks : MachineAddress.Hooks Miri.Memory.MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (info : AllocationInfo)
    (uncached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : machine.memory.getAllocInfo id=.ok info) (kind : info.kind=.typeId)
    (live : machine.memory.isAllocLive id=true) :
    MachineAddress.addrFromAllocId actualTape hooks id (some .other) machine=.ok 0
      (withAddresses machine (CurrentCallConversionChoiceProtocol.cacheData machine.user.addresses id 0)) := by
  have zero:=cache_zero machine.user.addresses id uncached
  unfold MachineAddress.addrFromAllocId MachineAddress.assign
  unfold_internal ".MachineAddress.addresses"
  unfold_internal ".MachineAddress.finish"
  unfold_internal ".MachineAddress.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    uncached,metadata,kind,live,bne_self_eq_false,show (AllocationKind.typeId==AllocationKind.dead)=false from rfl,beq_iff_eq,beq_self_eq_true,reduceCtorEq,Bool.not_true,Bool.false_or,Bool.false_and,
    Bool.true_or,Bool.and_false,Bool.false_eq_true,↓reduceIte]
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,beq_self_eq_true,Bool.not_true,↓reduceIte,zero,Id.run,pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  rfl

private theorem cache_state (addresses : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none) (positive : address≠0)
    (cut : Nat) (partition : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address cut) :
    (addresses.cacheAddress id address).state=CurrentCallConversionChoiceProtocol.cacheData addresses id address := by
  have search:=WildcardInteriorHitAddress.inverse_cut addresses.intToPtrMap address cut partition
  have nonzero : (address==0)=false:=by simpa using positive
  unfold GlobalAddressState.cacheAddress CurrentCallConversionChoiceProtocol.cacheData
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.insertBase"
  simp only [uncached,Option.map_none,nonzero,Bool.false_eq_true,↓reduceIte,search,
    Array.insertIdxIfInBounds,partition.1,↓reduceDIte,Id.run,bind,pure]

private theorem ensured_bucket (pool : ReusePool) (index : Nat) :
    (source_reuse_ensure pool index).pool[index]?=some ((pool.pool[index]?).getD #[]) := by
  have bounded:=CurrentCallConversionChoiceProtocol.ensure_bounds pool index
  have stored:=Array.getElem?_eq_getElem bounded
  let bucket:=(source_reuse_ensure pool index).pool[index]
  have bucketEq : bucket=(pool.pool[index]?).getD #[] := by
    apply Array.ext_getElem?
    intro selected
    have equal:=GlobalAddressReusePairwise.ensure_peek pool index (index,selected)
    unfold GlobalAddressReusePairwise.peek at equal
    rw [stored] at equal
    cases old : pool.pool[index]? with
    | none => simpa only [old,Option.bind_some,Option.bind_none,Option.getD_none,Array.getElem?_empty] using equal
    | some oldBucket => simpa only [old,Option.bind_some,Option.getD_some] using equal
  exact stored.trans (congrArg some bucketEq)

private theorem cache_completed_state (addresses : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (success : (addresses.cacheAddress id address).outcome=.ok ()) :
    (addresses.cacheAddress id address).state=CurrentCallConversionChoiceProtocol.cacheData addresses id address := by
  unfold GlobalAddressState.cacheAddress at success ⊢
  unfold CurrentCallConversionChoiceProtocol.cacheData
  unfold_internal_at ".GlobalAddressState.findBase" at success
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal_at ".GlobalAddressState.insertBase" at success
  unfold_internal ".GlobalAddressState.insertBase"
  simp only [uncached,Option.map_none,Id.run,bind,pure] at success ⊢
  by_cases zero : (address==0)=true
  · simp only [zero,↓reduceIte]
  · simp only [zero,↓reduceIte] at success ⊢
    generalize inverse : ((reuse_source ".GlobalAddressState.findInverseIndex") addresses.intToPtrMap address)=pair at success ⊢
    rcases pair with ⟨position,found⟩
    cases found with
    | true =>
      simp only [↓reduceIte] at success
      cases old : addresses.intToPtrMap[position]? <;> simp only [old] at success <;> cases success
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte] at success ⊢
      by_cases bounded : position≤addresses.intToPtrMap.size
      · simp only [bounded,↓reduceDIte,Array.insertIdxIfInBounds]
      · simp only [bounded,↓reduceDIte] at success
        cases success

private theorem ensure_shape (pool : ReusePool) (index : Nat) :
    source_reuse_ensure pool index={pool with pool:=(source_reuse_ensure pool index).pool} := by
  unfold_internal ".ReusePool.ensureSubpool"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]

private theorem poolRange_ensure (pool : ReusePool) (size : Size) (align : Align)
    (thread : AddressThreadId) (reuse cross : Bool) :
    CurrentCallConversionChoiceProtocol.poolRange (source_reuse_ensure pool align.pow2) size align thread reuse cross=
      CurrentCallConversionChoiceProtocol.poolRange pool size align thread reuse cross := by
  unfold CurrentCallConversionChoiceProtocol.poolRange
  rw [ensured_bucket]
  simp only [Option.getD_some]

private theorem prepare_no_reuse (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId)
    (allowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate false=true) :
    pool.prepareTakeAddr false false size align .other thread=⟨pool,.ok none⟩ := by
  unfold ReusePool.prepareTakeAddr
  simp only [show (AddressMemoryKind.other==AddressMemoryKind.stack)=false from rfl,allowed,
    Bool.not_true,Bool.not_false,beq_self_eq_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]

private theorem prepare_reuse (pool : ReusePool) (size : Size) (align : Align)
    (thread : AddressThreadId) (cross : Bool) (valid : align.pow2≤29)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross=true) :
    pool.prepareTakeAddr true cross size align .other thread=
      ⟨source_reuse_ensure pool align.pow2,.ok
        (CurrentCallConversionChoiceProtocol.poolRange pool size align thread true cross)⟩ := by
  unfold ReusePool.prepareTakeAddr CurrentCallConversionChoiceProtocol.poolRange
  simp only [show (AddressMemoryKind.other==AddressMemoryKind.stack)=false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,
    GlobalAddressReuseRawSelection.checked align valid,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  unfold_internal ".ReusePool.subpoolAt"
  unfold_internal ".ReusePool.getSubpool?"
  simp only [ensured_bucket,Option.map_some,Except.ok.injEq,GlobalAddressReuseRawSelection.range_eq,
    pure,Pure.pure,Except.pure,Id.run]
  split <;> rfl

private theorem selected_raw (pool : ReusePool) (size : Size) (align : Align)
    (thread : AddressThreadId) (cross : Bool) (valid : align.pow2≤29)
    (aligned : CurrentCallConversionChoiceProtocol.BucketsAligned pool)
    (begin stop selected : Nat)
    (interval : CurrentCallConversionChoiceProtocol.poolRange pool size align thread true cross=some (begin,stop))
    (within : selected<stop-begin) :
    ∃raw : GlobalAddressReuseRawSelection.Input pool size align thread cross,raw.selected=begin+selected := by
  let bucket:=pool.pool[align.pow2]?.getD #[]
  have intervalEq : GlobalAddressReuseRawSelection.range bucket size thread cross=(begin,stop) := by
    unfold CurrentCallConversionChoiceProtocol.poolRange at interval
    simp only [↓reduceIte] at interval
    split at interval
    · cases interval
    · exact Option.some.inj interval
  have shape:=range_shape bucket size thread cross
  rw [intervalEq] at shape
  obtain ⟨entry,present,sizeEq,sameThread⟩:=shape.2 (begin+selected) (by omega) (by omega)
  have stored : pool.pool[align.pow2]?=some bucket := by
    cases old : pool.pool[align.pow2]? with
    | none => have bad:=present; simp only [bucket,old,Option.getD_none,Array.getElem?_empty] at bad;cases bad
    | some actual => simpa only [bucket,old,Option.getD_some] using old
  have validSelected:begin+selected<bucket.size:=(Array.getElem?_eq_some_iff.mp present).1
  have value : bucket[begin+selected]=entry := (Array.getElem?_eq_some_iff.mp present).2
  refine ⟨⟨bucket,stored,begin+selected,validSelected,?_,?_,?_,?_,?_⟩,rfl⟩
  · rw [intervalEq];simp only;omega
  · rw [intervalEq];simp only;omega
  · rw [value,sizeEq];exact UInt64.le_refl _
  · rw [value]
    exact aligned align.pow2 (begin+selected) entry valid (by
      unfold GlobalAddressReusePairwise.peek;rw [stored];exact present)
  · rw [value];exact sameThread

private theorem reused_complete {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (initial : ManagedRows memory addresses generation) (id : AllocId)
    (info : AllocationInfo) (thread : AddressThreadId)
    (metadata : memory.getAllocInfo id=.ok info)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (cross : Bool) (raw : GlobalAddressReuseRawSelection.Input generation.reusePool info.size info.align thread cross)
    (valid : info.align.pow2≤29)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross=true)
    (slack : Fin 16) :
    let choices : AddressRandomChoices:=⟨true,cross,raw.selected,slack⟩
    let staged : GlobalAddressState:={addresses with generation:=some {generation with reusePool:=GlobalAddressReuseRawSelection.output generation.reusePool info.size info.align thread cross raw}}
    GlobalAddressState.completeAcquire (addresses.addrFromAllocId id
      (some (GlobalAddressAlignedManagedFormation.info info.size info.align .other thread)) choices) (.ok ())=
      ⟨(staged.cacheAddress id (raw.bucket[raw.selected]'raw.valid).address).state,.ok (.ready (raw.bucket[raw.selected]'raw.valid).address)⟩ := by
  dsimp only
  have taken:=GlobalAddressReuseRawSelection.take generation.reusePool info.size info.align thread cross raw valid reuseAllowed crossAllowed
  have sizeEq:=CurrentCallConversionInfoRows.queried_size metadata
  have separated:=GlobalAddressReuseHoleGeometry.take_separated generation.reusePool addresses.intToPtrMap
    (CurrentCallConversionInfoRows.sizes memory) initial.holes initial.ordered id info.size sizeEq
    true cross raw.selected info.align .other thread
  let used : ReusedAddress:=⟨(raw.bucket[raw.selected]'raw.valid).address,
    if (raw.bucket[raw.selected]'raw.valid).thread==thread then none else some (raw.bucket[raw.selected]'raw.valid).clock⟩
  have takeOutcome : (generation.reusePool.takeAddr true cross raw.selected info.size info.align .other thread).outcome=.ok (some used) :=
    congrArg ReusePoolResult.outcome taken
  obtain ⟨positive,cut,partition,placement⟩:=separated.2 used takeOutcome
  have cached:=GlobalAddressRangeFormation.cache
    {addresses with generation:=some {generation with reusePool:=GlobalAddressReuseRawSelection.output generation.reusePool info.size info.align thread cross raw}}
    (CurrentCallConversionInfoRows.sizes memory) initial.apart id used.address uncached positive cut partition placement
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,initial.managed,initial.generationEq,taken,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  dsimp only [used] at cached
  simp only [←initial.managed]
  by_cases same : (raw.bucket[raw.selected]'raw.valid).thread=thread
  all_goals simp only [same,↓reduceIte]
  all_goals simp only [GlobalAddressState.completeAcquire,cached.1]

private theorem take_empty_reuse (pool : ReusePool) (size : Size) (align : Align)
    (thread : AddressThreadId) (cross : Bool) (valid : align.pow2≤29)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross=true)
    (empty : CurrentCallConversionChoiceProtocol.poolRange pool size align thread true cross=none)
    (selected : Nat) :
    pool.takeAddr true cross selected size align .other thread=⟨source_reuse_ensure pool align.pow2,.ok none⟩ := by
  have intervalEmpty : ((GlobalAddressReuseRawSelection.range (pool.pool[align.pow2]?.getD #[]) size thread cross).2==
      (GlobalAddressReuseRawSelection.range (pool.pool[align.pow2]?.getD #[]) size thread cross).1)=true := by
    unfold CurrentCallConversionChoiceProtocol.poolRange at empty
    simp only [↓reduceIte] at empty
    split at empty
    · assumption
    · cases empty
  unfold ReusePool.takeAddr
  simp only [show (AddressMemoryKind.other==AddressMemoryKind.stack)=false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,GlobalAddressReuseRawSelection.checked align valid,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  unfold_internal ".ReusePool.subpoolAt"
  unfold_internal ".ReusePool.getSubpool?"
  simp only [ensured_bucket,pure,Pure.pure,Except.pure,Id.run,GlobalAddressReuseRawSelection.range_eq,intervalEmpty,↓reduceIte]

private def fresh_data (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (pool : ReusePool) (size : Size) (align : Align) (slack : Fin 16) : GlobalAddressState :=
  let generator:=next generation.generator size align slack
  {addresses with generation:=some ⟨generator,if generator.nextBaseAddr>generator.endAddr/2 then pool.addressSpaceShortage else pool⟩}

private theorem fresh_complete {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (initial : ManagedRows memory addresses generation) (id : AllocId) (info : AllocationInfo)
    (metadata : memory.getAllocInfo id=.ok info)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (thread : AddressThreadId) (choices : AddressRandomChoices) (pool : ReusePool)
    (taken : generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex
      info.size info.align .other thread=⟨pool,.ok none⟩)
    (valid : info.align.pow2≤29) (room : Room generation.generator info.size info.align choices.slack) :
    let staged:=fresh_data addresses generation pool info.size info.align choices.slack
    GlobalAddressState.completeAcquire (addresses.addrFromAllocId id
      (some (GlobalAddressAlignedManagedFormation.info info.size info.align .other thread)) choices) (.ok ())=
      ⟨(staged.cacheAddress id (base generation.generator info.align choices.slack)).state,
        .ok (.ready (base generation.generator info.align choices.slack))⟩ := by
  dsimp only
  have geometry:=placement addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory)
    generation.generator initial.frontier id info.size info.align valid choices.slack room
  have positive : base generation.generator info.align choices.slack≠0 := by
    intro zero
    have lower:=(base_bounds generation.generator info.size info.align valid choices.slack room).1
    rw [zero] at lower
    change generation.generator.nextBaseAddr.toNat+choices.slack.val≤0 at lower
    have cursor : generation.generator.nextBaseAddr.toNat≠0 := by
      intro equal;exact initial.cursor (UInt64.toNat_inj.mp equal)
    omega
  have cached:=GlobalAddressRangeFormation.cache (fresh_data addresses generation pool info.size info.align choices.slack)
    (CurrentCallConversionInfoRows.sizes memory) initial.apart id _ uncached positive _ geometry.1 geometry.2
  have bumped:=generated generation.generator info.size info.align valid choices.slack room
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,initial.managed,initial.generationEq,taken,bumped,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  simp only [←initial.managed]
  change GlobalAddressState.completeAcquire (match ((fresh_data addresses generation pool info.size info.align choices.slack).cacheAddress id (base generation.generator info.align choices.slack)).outcome with
    | .ok _=>⟨((fresh_data addresses generation pool info.size info.align choices.slack).cacheAddress id (base generation.generator info.align choices.slack)).state,.ok (.ready (base generation.generator info.align choices.slack))⟩
    | .error error=>⟨((fresh_data addresses generation pool info.size info.align choices.slack).cacheAddress id (base generation.generator info.align choices.slack)).state,.error error⟩) (.ok ())=_
  rw [cached.1]
  rfl

private theorem fresh_cache {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (initial : ManagedRows memory addresses generation) (id : AllocId) (info : AllocationInfo)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (pool : ReusePool) (slack : Fin 16) (valid : info.align.pow2≤29)
    (room : Room generation.generator info.size info.align slack) :
    let staged:=fresh_data addresses generation pool info.size info.align slack
    (staged.cacheAddress id (base generation.generator info.align slack)).state=
      CurrentCallConversionChoiceProtocol.cacheData staged id (base generation.generator info.align slack) := by
  have geometry:=placement addresses.intToPtrMap (CurrentCallConversionInfoRows.sizes memory)
    generation.generator initial.frontier id info.size info.align valid slack room
  have positive : base generation.generator info.align slack≠0 := by
    intro zero
    have lower:=(base_bounds generation.generator info.size info.align valid slack room).1
    rw [zero] at lower
    change generation.generator.nextBaseAddr.toNat+slack.val≤0 at lower
    have cursor : generation.generator.nextBaseAddr.toNat≠0 := by
      intro equal;exact initial.cursor (UInt64.toNat_inj.mp equal)
    omega
  exact cache_state (fresh_data addresses generation pool info.size info.align slack) id _ uncached positive _ geometry.1

private theorem reused_cache {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (initial : ManagedRows memory addresses generation) (id : AllocId) (info : AllocationInfo)
    (metadata : memory.getAllocInfo id=.ok info)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (thread : AddressThreadId) (cross : Bool)
    (raw : GlobalAddressReuseRawSelection.Input generation.reusePool info.size info.align thread cross)
    (valid : info.align.pow2≤29)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross=true) :
    let staged:GlobalAddressState:={addresses with generation:=some {generation with reusePool:=GlobalAddressReuseRawSelection.output generation.reusePool info.size info.align thread cross raw}}
    (staged.cacheAddress id (raw.bucket[raw.selected]'raw.valid).address).state=
      CurrentCallConversionChoiceProtocol.cacheData staged id (raw.bucket[raw.selected]'raw.valid).address := by
  dsimp only
  have taken:=GlobalAddressReuseRawSelection.take generation.reusePool info.size info.align thread cross raw valid reuseAllowed crossAllowed
  have separated:=GlobalAddressReuseHoleGeometry.take_separated generation.reusePool addresses.intToPtrMap
    (CurrentCallConversionInfoRows.sizes memory) initial.holes initial.ordered id info.size
    (CurrentCallConversionInfoRows.queried_size metadata) true cross raw.selected info.align .other thread
  let used:ReusedAddress:=⟨(raw.bucket[raw.selected]'raw.valid).address,
    if (raw.bucket[raw.selected]'raw.valid).thread==thread then none else some (raw.bucket[raw.selected]'raw.valid).clock⟩
  have takeOutcome : (generation.reusePool.takeAddr true cross raw.selected info.size info.align .other thread).outcome=.ok (some used) :=
    congrArg ReusePoolResult.outcome taken
  obtain ⟨positive,cut,partition,_⟩:=separated.2 used takeOutcome
  exact cache_state _ id _ uncached positive cut partition

private theorem actual_slack (machine : ActualMachine) (index : Nat) (after : ExecutionChoices.Tape)
    (data : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 (actualTape.get machine) index after) :
    (reuse_source ".MachineAddress.slack") actualTape machine=.ok (⟨index,data.bound⟩ : Fin 16) (actualTape.put machine after) := by
  have step:=data.read actualTape actual_tape_laws machine rfl
  unfold_internal ".MachineAddress.slack"
  simp only [step,data.bound,↓reduceDIte,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

private theorem assign_from_complete (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (info : AllocationInfo) (choices : AddressRandomChoices)
    (next : GlobalAddressState) (base : UInt64)
    (uncached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : machine.memory.getAllocInfo id=.ok info) (nondead : info.kind≠.dead) (nontype : info.kind≠.typeId)
    (live : machine.memory.isAllocLive id=true) (managed : machine.user.addresses.addressMode=.managed)
    (race : machine.dataRace=none)
    (completed : GlobalAddressState.completeAcquire
      (machine.user.addresses.addrFromAllocId id (some (GlobalAddressAlignedManagedFormation.info info.size info.align
        .other (UInt32.ofNat machine.threads.activeThread.toNat))) choices) (.ok ())=⟨next,.ok (.ready base)⟩) :
    MachineAddress.assign hooks id (some .other) choices machine=.ok base (withAddresses machine next) := by
  unfold MachineAddress.assign
  unfold_internal ".MachineAddress.addresses"
  unfold_internal ".MachineAddress.finish"
  unfold_internal ".MachineAddress.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    uncached,metadata,live,managed,beq_iff_eq,nondead,nontype,bne_self_eq_false,
    Bool.false_and,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  let pending:=machine.user.addresses.addrFromAllocId id
    (some (GlobalAddressAlignedManagedFormation.info info.size info.align .other
      (UInt32.ofNat machine.threads.activeThread.toNat))) choices
  change GlobalAddressState.completeAcquire pending (.ok ())=⟨next,.ok (.ready base)⟩ at completed
  have literal : machine.user.addresses.addrFromAllocId id
      (some {kind:=.liveData,live:=true,size:=info.size,align:=info.align,memoryKind:=some .other,thread:=UInt32.ofNat machine.threads.activeThread.toNat}) choices=pending := rfl
  rw [literal]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    EStateM.bind,EStateM.pure,EStateM.get,race]
  cases outcome : pending.outcome with
  | error reason=>
    have impossible:=congrArg AddressStateResult.outcome completed
    simp only [GlobalAddressState.completeAcquire,outcome] at impossible
    cases impossible
  | ok assignment=>
    cases assignment with
    | ready address=>
      have stateEq:=congrArg AddressStateResult.state completed
      have valueEq:=congrArg AddressStateResult.outcome completed
      simp only [GlobalAddressState.completeAcquire,outcome] at stateEq valueEq
      cases valueEq
      rw [←stateEq]
      simp only [withAddresses,race,EStateM.pure,EStateM.bind]
    | acquireRequired other address clock=>
      simp only [GlobalAddressState.completeAcquire,outcome] at completed
      cases cache : (pending.state.cacheAddress other address).outcome with
      | error reason=>
        have impossible:=congrArg AddressStateResult.outcome completed
        simp only [cache] at impossible
        cases impossible
      | ok value=>
        cases value
        simp only [cache] at completed
        have stateEq:=congrArg AddressStateResult.state completed
        dsimp only [AddressStateResult.state] at stateEq
        have valueEq:=congrArg AddressStateResult.outcome completed
        cases valueEq
        rw [←stateEq]
        simp only [cache,withAddresses,race,get,getThe,MonadStateOf.get,EStateM.get,
          bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
          modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]


private theorem no_reuse_address (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (info : AllocationInfo) (generation : AddressGenerationState)
    (initial : ManagedRows machine.memory machine.user.addresses generation)
    (uncached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : machine.memory.getAllocInfo id=.ok info) (nondead : info.kind≠.dead) (nontype : info.kind≠.typeId)
    (live : machine.memory.isAllocLive id=true) (race : machine.dataRace=none) (valid : info.align.pow2≤29)
    (firstTape afterTape : ExecutionChoices.Tape) (index : Nat)
    (reuseData : CurrentCallConversionChoiceProtocol.BoolInput .addressReuse generation.reusePool.addressReuseRate.toBits
      (actualTape.get machine) false firstTape)
    (slackData : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 firstTape index afterTape)
    (room : Room generation.generator info.size info.align ⟨index,slackData.bound⟩) :
    let slack : Fin 16:=⟨index,slackData.bound⟩
    let staged:=GlobalAddressAlignedManagedFormation.ready machine.user.addresses generation info.size info.align slack
    MachineAddress.addrFromAllocId actualTape hooks id (some .other) machine=
      .ok (base generation.generator info.align slack)
        (addressMachine machine (staged.cacheAddress id (base generation.generator info.align slack)).state afterTape) := by
  dsimp only
  let slack : Fin 16:=⟨index,slackData.bound⟩
  let staged:=GlobalAddressAlignedManagedFormation.ready machine.user.addresses generation info.size info.align slack
  have allowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseRate false reuseData.legal
  have source:=GlobalAddressAlignedManagedFormation.source machine.user.addresses generation
    (CurrentCallConversionInfoRows.sizes machine.memory) initial.apart initial.frontier initial.managed initial.generationEq
    initial.cursor id info.size (CurrentCallConversionInfoRows.queried_size metadata) info.align valid uncached .other
    (UInt32.ofNat machine.threads.activeThread.toNat) slack allowed room
  have completed : GlobalAddressState.completeAcquire (machine.user.addresses.addrFromAllocId id
      (some (GlobalAddressAlignedManagedFormation.info info.size info.align .other
        (UInt32.ofNat machine.threads.activeThread.toNat))) (GlobalAddressAlignedManagedFormation.choices slack)) (.ok ())=
      ⟨(staged.cacheAddress id (base generation.generator info.align slack)).state,
        .ok (.ready (base generation.generator info.align slack))⟩ := by
    rw [source.1]
    rfl
  have assigned:=assign_from_complete hooks (actualTape.put machine afterTape) id info
    (GlobalAddressAlignedManagedFormation.choices slack) _ (base generation.generator info.align slack)
    uncached metadata nondead nontype live initial.managed race completed
  have first:=reuseData.read actualTape actual_tape_laws machine rfl
  have slackAt : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16
      (actualTape.get (actualTape.put machine firstTape)) index afterTape := by
    rw [actual_tape_laws.getPut]
    exact slackData
  have second:=actual_slack (actualTape.put machine firstTape) index afterTape slackAt
  have prepared:=prepare_no_reuse generation.reusePool info.size info.align
    (UInt32.ofNat machine.threads.activeThread.toNat) allowed
  have unchanged : {machine.user.addresses with generation:=some {generation with reusePool:=generation.reusePool}}=
      machine.user.addresses := by
    change {machine.user.addresses with generation:=some generation}=machine.user.addresses
    rw [←initial.generationEq]
  have deadFlag : (info.kind==AllocationKind.dead)=false:=by simpa using nondead
  have typeFlag : (info.kind==AllocationKind.typeId)=false:=by simpa using nontype
  unfold MachineAddress.addrFromAllocId
  unfold_internal ".MachineAddress.rate"
  unfold_internal ".MachineAddress.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    uncached,metadata,live,deadFlag,typeFlag,initial.managed,initial.generationEq,beq_iff_eq,reduceCtorEq,
    bne_self_eq_false,Bool.not_true,Bool.false_eq_true,Bool.false_or,↓reduceIte,first,prepared,
    unchanged,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  have threadEq : (actualTape.put machine firstTape).threads=machine.threads:=rfl
  simp only [threadEq,prepared]
  have initialAgain : {machine.user.addresses with addressMode:=.managed,generation:=some generation}=machine.user.addresses := by
    rw [←initial.managed,←initial.generationEq]
  have reset : {actualTape.put machine firstTape with
      threads:=machine.threads
      user:={(actualTape.put machine firstTape).user with addresses:={machine.user.addresses with addressMode:=.managed,generation:=some generation}}}=actualTape.put machine firstTape := by
    rw [initialAgain]
    rfl
  rw [reset]
  simp only [EStateM.bind,EStateM.pure,second,actual_tape_laws.putPut]
  exact assigned


private theorem reused_address (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (info : AllocationInfo) (generation : AddressGenerationState)
    (initial : ManagedRows machine.memory machine.user.addresses generation)
    (uncached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : machine.memory.getAllocInfo id=.ok info) (nondead : info.kind≠.dead) (nontype : info.kind≠.typeId)
    (live : machine.memory.isAllocLive id=true) (race : machine.dataRace=none) (valid : info.align.pow2≤29)
    (cross : Bool) (raw : GlobalAddressReuseRawSelection.Input generation.reusePool info.size info.align
      (UInt32.ofNat machine.threads.activeThread.toNat) cross)
    (firstTape secondTape afterTape : ExecutionChoices.Tape) (index : Nat)
    (reuseData : CurrentCallConversionChoiceProtocol.BoolInput .addressReuse generation.reusePool.addressReuseRate.toBits
      (actualTape.get machine) true firstTape)
    (crossData : CurrentCallConversionChoiceProtocol.BoolInput .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits
      firstTape cross secondTape)
    (indexData : CurrentCallConversionChoiceProtocol.IndexInput .addressPool
      ((GlobalAddressReuseRawSelection.range raw.bucket info.size (UInt32.ofNat machine.threads.activeThread.toNat) cross).2-
       (GlobalAddressReuseRawSelection.range raw.bucket info.size (UInt32.ofNat machine.threads.activeThread.toNat) cross).1)
      secondTape index afterTape)
    (selected : raw.selected=(GlobalAddressReuseRawSelection.range raw.bucket info.size
      (UInt32.ofNat machine.threads.activeThread.toNat) cross).1+index) :
    let staged : GlobalAddressState:={machine.user.addresses with generation:=some {generation with reusePool:=GlobalAddressReuseRawSelection.output generation.reusePool info.size info.align (UInt32.ofNat machine.threads.activeThread.toNat) cross raw}}
    MachineAddress.addrFromAllocId actualTape hooks id (some .other) machine=
      .ok (raw.bucket[raw.selected]'raw.valid).address
        (addressMachine machine (staged.cacheAddress id (raw.bucket[raw.selected]'raw.valid).address).state afterTape) := by
  dsimp only
  have allowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseRate true reuseData.legal
  have crossAllowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseCrossThreadRate cross crossData.legal
  let choices : AddressRandomChoices:=⟨true,cross,raw.selected,⟨0,by decide⟩⟩
  have completed:=reused_complete machine.memory machine.user.addresses generation initial id info
    (UInt32.ofNat machine.threads.activeThread.toNat) metadata uncached cross raw valid allowed crossAllowed choices.slack
  have assigned:=assign_from_complete hooks (actualTape.put machine afterTape) id info choices _
    (raw.bucket[raw.selected]'raw.valid).address uncached metadata nondead nontype live initial.managed race completed
  have first:=reuseData.read actualTape actual_tape_laws machine rfl
  have second:=crossData.read actualTape actual_tape_laws (actualTape.put machine firstTape) (actual_tape_laws.getPut _ _)
  have third:=indexData.read actualTape actual_tape_laws (actualTape.put machine secondTape) (actual_tape_laws.getPut _ _)
  have prepared:=GlobalAddressReuseRawSelection.prepare generation.reusePool info.size info.align
    (UInt32.ofNat machine.threads.activeThread.toNat) cross raw valid allowed crossAllowed
  have deadFlag : (info.kind==AllocationKind.dead)=false:=by simpa using nondead
  have typeFlag : (info.kind==AllocationKind.typeId)=false:=by simpa using nontype
  unfold MachineAddress.addrFromAllocId
  unfold_internal ".MachineAddress.rate"
  unfold_internal ".MachineAddress.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    uncached,metadata,live,deadFlag,typeFlag,initial.managed,initial.generationEq,beq_iff_eq,reduceCtorEq,
    bne_self_eq_false,Bool.not_true,Bool.false_eq_true,Bool.false_or,↓reduceIte,first,second,actual_tape_laws.putPut,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  have threadEq : (actualTape.put machine secondTape).threads=machine.threads:=rfl
  simp only [threadEq,prepared]
  have initialAgain : {machine.user.addresses with addressMode:=.managed,generation:=some generation}=machine.user.addresses := by
    rw [←initial.managed,←initial.generationEq]
  have reset : {actualTape.put machine secondTape with
      threads:=machine.threads
      user:={(actualTape.put machine secondTape).user with addresses:={machine.user.addresses with addressMode:=.managed,generation:=some generation}}}=actualTape.put machine secondTape := by
    rw [initialAgain]
    rfl
  rw [reset]
  simp only [EStateM.bind,EStateM.pure,third,actual_tape_laws.putPut,←selected]
  simpa only [choices,addressMachine,initial.managed] using assigned

private theorem tape_addresses (machine : ActualMachine) (addresses : GlobalAddressState)
    (tape : ExecutionChoices.Tape) :
    actualTape.put (withAddresses machine addresses) tape=withAddresses (actualTape.put machine tape) addresses := rfl

private theorem empty_reuse_address (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (info : AllocationInfo) (generation : AddressGenerationState)
    (initial : ManagedRows machine.memory machine.user.addresses generation)
    (uncached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : machine.memory.getAllocInfo id=.ok info) (nondead : info.kind≠.dead) (nontype : info.kind≠.typeId)
    (live : machine.memory.isAllocLive id=true) (race : machine.dataRace=none) (valid : info.align.pow2≤29)
    (cross : Bool) (firstTape secondTape afterTape : ExecutionChoices.Tape) (index : Nat)
    (reuseData : CurrentCallConversionChoiceProtocol.BoolInput .addressReuse generation.reusePool.addressReuseRate.toBits
      (actualTape.get machine) true firstTape)
    (crossData : CurrentCallConversionChoiceProtocol.BoolInput .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits
      firstTape cross secondTape)
    (slackData : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 secondTape index afterTape)
    (empty : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align
      (UInt32.ofNat machine.threads.activeThread.toNat) true cross=none)
    (room : Room generation.generator info.size info.align ⟨index,slackData.bound⟩) :
    let pool:=source_reuse_ensure generation.reusePool info.align.pow2
    let staged:=fresh_data machine.user.addresses generation pool info.size info.align ⟨index,slackData.bound⟩
    MachineAddress.addrFromAllocId actualTape hooks id (some .other) machine=
      .ok (base generation.generator info.align ⟨index,slackData.bound⟩)
        (addressMachine machine (staged.cacheAddress id (base generation.generator info.align ⟨index,slackData.bound⟩)).state afterTape) := by
  dsimp only
  let pool:=source_reuse_ensure generation.reusePool info.align.pow2
  let newGen:AddressGenerationState:={generation with reusePool:=pool}
  let newAddresses:GlobalAddressState:={machine.user.addresses with generation:=some newGen}
  let newMachine:=addressMachine machine newAddresses secondTape
  let slack:Fin 16:=⟨index,slackData.bound⟩
  have poolShape:=ensure_shape generation.reusePool info.align.pow2
  have allowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseRate true reuseData.legal
  have crossAllowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseCrossThreadRate cross crossData.legal
  have allowed2 : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true=true := by
    change ReusePool.bernoulliChoiceAllowed (source_reuse_ensure generation.reusePool info.align.pow2).addressReuseRate true=true
    rw [poolShape];exact allowed
  have crossAllowed2 : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross=true := by
    change ReusePool.bernoulliChoiceAllowed (source_reuse_ensure generation.reusePool info.align.pow2).addressReuseCrossThreadRate cross=true
    rw [poolShape];exact crossAllowed
  have empty2 : CurrentCallConversionChoiceProtocol.poolRange pool info.size info.align
      (UInt32.ofNat machine.threads.activeThread.toNat) true cross=none :=
    (poolRange_ensure generation.reusePool info.size info.align _ true cross).trans empty
  have taken:=take_empty_reuse pool info.size info.align (UInt32.ofNat machine.threads.activeThread.toNat)
    cross valid allowed2 crossAllowed2 empty2 0
  have poolId : source_reuse_ensure pool info.align.pow2=pool :=
    GlobalAddressReuseRawSelection.ensure pool info.align.pow2 (CurrentCallConversionChoiceProtocol.ensure_bounds generation.reusePool info.align.pow2)
  rw [poolId] at taken
  have newInitial : ManagedRows machine.memory newAddresses newGen :=
    stage_rows machine.memory machine.user.addresses generation newGen initial initial.cursor initial.frontier
      (GlobalAddressReuseContents.ensure generation.reusePool info.align.pow2 _ initial.holes)
      (GlobalAddressReuseContents.ensure generation.reusePool info.align.pow2 _ initial.bounded)
      (GlobalAddressReusePairwise.ensure generation.reusePool info.align.pow2 initial.pairwise)
  let choices:AddressRandomChoices:=⟨true,cross,0,slack⟩
  have completed:=fresh_complete machine.memory newAddresses newGen newInitial id info metadata uncached
    (UInt32.ofNat machine.threads.activeThread.toNat) choices pool taken valid room
  have assigned:=assign_from_complete hooks (addressMachine machine newAddresses afterTape) id info choices _
    (base generation.generator info.align slack) uncached metadata nondead nontype live newInitial.managed race completed
  have first:=reuseData.read actualTape actual_tape_laws machine rfl
  have second:=crossData.read actualTape actual_tape_laws (actualTape.put machine firstTape) (actual_tape_laws.getPut _ _)
  have third:=actual_slack newMachine index afterTape (by exact slackData)
  have prepared:=prepare_reuse generation.reusePool info.size info.align
    (UInt32.ofNat machine.threads.activeThread.toNat) cross valid allowed crossAllowed
  rw [empty] at prepared
  have deadFlag : (info.kind==AllocationKind.dead)=false:=by simpa using nondead
  have typeFlag : (info.kind==AllocationKind.typeId)=false:=by simpa using nontype
  unfold MachineAddress.addrFromAllocId
  unfold_internal ".MachineAddress.rate"
  unfold_internal ".MachineAddress.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    uncached,metadata,live,deadFlag,typeFlag,initial.managed,initial.generationEq,beq_iff_eq,reduceCtorEq,
    bne_self_eq_false,Bool.not_true,Bool.false_eq_true,Bool.false_or,↓reduceIte,first,second,actual_tape_laws.putPut,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  have threadEq : (actualTape.put machine secondTape).threads=machine.threads:=rfl
  simp only [threadEq,prepared]
  have reset : {actualTape.put machine secondTape with
      threads:=machine.threads
      user:={(actualTape.put machine secondTape).user with addresses:={machine.user.addresses with addressMode:=.managed,generation:=some newGen}}}=newMachine := by
    dsimp only [newMachine,addressMachine,withAddresses,newAddresses]
    rw [←initial.managed]
    rfl
  rw [reset]
  simp only [EStateM.bind,EStateM.pure,third]
  have finishMachine : actualTape.put newMachine afterTape=addressMachine machine newAddresses afterTape := by
    dsimp only [newMachine,addressMachine]
    rw [tape_addresses,actual_tape_laws.putPut]
  rw [finishMachine]
  simpa only [choices,slack,newMachine,addressMachine,withAddresses,actual_tape_laws.putPut,
    fresh_data,newAddresses,newGen,pool] using assigned

private theorem managed_address (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (info : AllocationInfo) (generation : AddressGenerationState)
    (initial : ManagedRows machine.memory machine.user.addresses generation)
    (uncached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : machine.memory.getAllocInfo id=.ok info) (nondead : info.kind≠.dead) (nontype : info.kind≠.typeId)
    (live : machine.memory.isAllocLive id=true) (race : machine.dataRace=none) (valid : info.align.pow2≤29)
    (aligned : CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align
      (UInt32.ofNat machine.threads.activeThread.toNat) (actualTape.get machine))
    (room : ∀slack,Room generation.generator info.size info.align slack) :
    ∃address,MachineAddress.addrFromAllocId actualTape hooks id (some .other) machine=
      .ok address (addressMachine machine (CurrentCallConversionChoiceProtocol.advance machine.user.addresses generation id info
        (UInt32.ofNat machine.threads.activeThread.toNat) (actualTape.get machine) block) block.afterIndex) := by
  cases reuseEq : block.reuse with
  | false =>
    have crosses : block.cross=false ∧block.afterCross=block.afterReuse := by
      simpa only [reuseEq,Bool.false_eq_true,↓reduceIte] using block.crossInput
    have data : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 block.afterReuse block.index block.afterIndex := by
      simpa only [CurrentCallConversionChoiceProtocol.poolRange,reuseEq,Bool.false_eq_true,↓reduceIte,crosses.2] using block.indexInput
    have reuseData : CurrentCallConversionChoiceProtocol.BoolInput .addressReuse generation.reusePool.addressReuseRate.toBits
        (actualTape.get machine) false block.afterReuse := by simpa only [reuseEq] using block.reuseInput
    have actual:=no_reuse_address hooks machine id info generation initial uncached metadata nondead nontype live race valid
      block.afterReuse block.afterIndex block.index reuseData data (room _)
    have cache:=fresh_cache machine.memory machine.user.addresses generation initial id info uncached generation.reusePool
      ⟨block.index,data.bound⟩ valid (room _)
    dsimp only [GlobalAddressAlignedManagedFormation.ready,fresh_data] at cache actual
    rw [cache] at actual
    refine ⟨base generation.generator info.align ⟨block.index,data.bound⟩,?_⟩
    have advanceEq : CurrentCallConversionChoiceProtocol.advance machine.user.addresses generation id info
        (UInt32.ofNat machine.threads.activeThread.toNat) (actualTape.get machine) block=
        CurrentCallConversionChoiceProtocol.cacheData
          (fresh_data machine.user.addresses generation generation.reusePool info.size info.align ⟨block.index,data.bound⟩)
          id (base generation.generator info.align ⟨block.index,data.bound⟩) := by
      simp only [CurrentCallConversionChoiceProtocol.advance,CurrentCallConversionChoiceProtocol.poolRange,reuseEq,
        Bool.false_eq_true,↓reduceIte,Nat.mod_eq_of_lt data.bound]
      rfl
    rw [advanceEq]
    exact actual
  | true =>
    have reuseData : CurrentCallConversionChoiceProtocol.BoolInput .addressReuse generation.reusePool.addressReuseRate.toBits
        (actualTape.get machine) true block.afterReuse := by simpa only [reuseEq] using block.reuseInput
    have crossData : CurrentCallConversionChoiceProtocol.BoolInput .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits
        block.afterReuse block.cross block.afterCross := by simpa only [reuseEq,↓reduceIte] using block.crossInput
    cases intervalEq : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align
        (UInt32.ofNat machine.threads.activeThread.toNat) true block.cross with
    | none =>
      have data : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 block.afterCross block.index block.afterIndex := by
        simpa only [reuseEq,intervalEq] using block.indexInput
      have actual:=empty_reuse_address hooks machine id info generation initial uncached metadata nondead nontype live race valid
        block.cross block.afterReuse block.afterCross block.afterIndex block.index reuseData crossData data intervalEq (room _)
      have cache:=fresh_cache machine.memory machine.user.addresses generation initial id info uncached
        (source_reuse_ensure generation.reusePool info.align.pow2) ⟨block.index,data.bound⟩ valid (room _)
      dsimp only [GlobalAddressAlignedManagedFormation.ready,fresh_data] at cache actual
      rw [cache] at actual
      refine ⟨base generation.generator info.align ⟨block.index,data.bound⟩,?_⟩
      have advanceEq : CurrentCallConversionChoiceProtocol.advance machine.user.addresses generation id info
          (UInt32.ofNat machine.threads.activeThread.toNat) (actualTape.get machine) block=
          CurrentCallConversionChoiceProtocol.cacheData
            (fresh_data machine.user.addresses generation (source_reuse_ensure generation.reusePool info.align.pow2) info.size info.align ⟨block.index,data.bound⟩)
            id (base generation.generator info.align ⟨block.index,data.bound⟩) := by
        simp only [CurrentCallConversionChoiceProtocol.advance,reuseEq,intervalEq,↓reduceIte,Nat.mod_eq_of_lt data.bound]
        rfl
      rw [advanceEq]
      exact actual
    | some interval =>
      rcases interval with ⟨begin,stop⟩
      have data : CurrentCallConversionChoiceProtocol.IndexInput .addressPool (stop-begin) block.afterCross block.index block.afterIndex := by
        simpa only [reuseEq,intervalEq] using block.indexInput
      obtain ⟨raw,selected⟩:=selected_raw generation.reusePool info.size info.align
        (UInt32.ofNat machine.threads.activeThread.toNat) block.cross valid aligned begin stop block.index intervalEq data.bound
      have rangeEq : GlobalAddressReuseRawSelection.range raw.bucket info.size (UInt32.ofNat machine.threads.activeThread.toNat) block.cross=(begin,stop) := by
        unfold CurrentCallConversionChoiceProtocol.poolRange at intervalEq
        simp only [↓reduceIte,raw.present,Option.getD_some] at intervalEq
        split at intervalEq
        · cases intervalEq
        · exact Option.some.inj intervalEq
      have actual:=reused_address hooks machine id info generation initial uncached metadata nondead nontype live race valid
        block.cross raw block.afterReuse block.afterCross block.afterIndex block.index reuseData crossData
        (by simpa only [rangeEq] using data) (by simpa only [rangeEq] using selected)
      have allowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseRate true reuseData.legal
      have crossAllowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseCrossThreadRate block.cross crossData.legal
      have cache:=reused_cache machine.memory machine.user.addresses generation initial id info metadata uncached
        (UInt32.ofNat machine.threads.activeThread.toNat) block.cross raw valid allowed crossAllowed
      dsimp only [GlobalAddressAlignedManagedFormation.ready,fresh_data] at cache actual
      rw [cache] at actual
      refine ⟨(raw.bucket[raw.selected]'raw.valid).address,?_⟩
      have poolEq:=GlobalAddressReuseRawSelection.ensure generation.reusePool info.align.pow2
        (GlobalAddressReuseRawSelection.bucket_bound generation.reusePool info.size info.align _ block.cross raw)
      have advanceEq : CurrentCallConversionChoiceProtocol.advance machine.user.addresses generation id info
          (UInt32.ofNat machine.threads.activeThread.toNat) (actualTape.get machine) block=
          CurrentCallConversionChoiceProtocol.cacheData
            {machine.user.addresses with generation:=some {generation with reusePool:=GlobalAddressReuseRawSelection.output generation.reusePool info.size info.align (UInt32.ofNat machine.threads.activeThread.toNat) block.cross raw}}
            id (raw.bucket[raw.selected]'raw.valid).address := by
        simp only [CurrentCallConversionChoiceProtocol.advance,reuseEq,intervalEq,↓reduceIte,poolEq,raw.present,Option.getD_some,
          ←selected,Array.getElem?_eq_getElem raw.valid,GlobalAddressReuseRawSelection.output,
          Array.eraseIdxIfInBounds,raw.valid,↓reduceDIte,
          (Array.getElem?_eq_some_iff.mp raw.present).1]
      rw [advanceEq]
      exact actual

private theorem cacheData_base (addresses : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (CurrentCallConversionChoiceProtocol.cacheData addresses id address).baseAddr=
      (addresses.baseAddr.filter (fun row=>row.allocId != id)).push ⟨id,address⟩ := by
  unfold CurrentCallConversionChoiceProtocol.cacheData
  split <;> rfl

private theorem cacheData_hit (addresses : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (CurrentCallConversionChoiceProtocol.cacheData addresses id address).baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,address⟩ := by
  rw [cacheData_base]
  exact GlobalAddressBaseCacheFormation.base_insert_same _ _ _

private theorem cacheData_old (addresses : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none) (query : AllocId) (base : BaseAddressEntry)
    (hit : addresses.baseAddr.find? (fun row=>row.allocId==query)=some base) :
    (CurrentCallConversionChoiceProtocol.cacheData addresses id address).baseAddr.find? (fun row=>row.allocId==query)=some base := by
  have different : query≠id := by intro equal;subst query;rw [uncached] at hit;cases hit
  rw [cacheData_base,GlobalAddressBaseCacheFormation.base_insert_other _ _ _ _ different]
  exact hit

private theorem cacheData_generation (addresses : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (CurrentCallConversionChoiceProtocol.cacheData addresses id address).generation=addresses.generation := by
  unfold CurrentCallConversionChoiceProtocol.cacheData
  split <;> rfl

private theorem advance_fresh_eq (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationInfo) (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape)
    (empty : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread block.reuse block.cross=none)
    (bounded : block.index<16) :
    CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block=
      CurrentCallConversionChoiceProtocol.cacheData (fresh_data addresses generation
        (if block.reuse then source_reuse_ensure generation.reusePool info.align.pow2 else generation.reusePool)
        info.size info.align ⟨block.index,bounded⟩) id (base generation.generator info.align ⟨block.index,bounded⟩) := by
  simp only [CurrentCallConversionChoiceProtocol.advance,empty,Nat.mod_eq_of_lt bounded]
  rfl

private theorem advance_reused_eq (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationInfo) (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape)
    (reuseEq : block.reuse=true) (begin stop : Nat)
    (intervalEq : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread true block.cross=some (begin,stop))
    (raw : GlobalAddressReuseRawSelection.Input generation.reusePool info.size info.align thread block.cross)
    (selected : raw.selected=begin+block.index) :
    CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block=
      CurrentCallConversionChoiceProtocol.cacheData
        {addresses with generation:=some {generation with reusePool:=GlobalAddressReuseRawSelection.output generation.reusePool info.size info.align thread block.cross raw}}
        id (raw.bucket[raw.selected]'raw.valid).address := by
  have poolEq:=GlobalAddressReuseRawSelection.ensure generation.reusePool info.align.pow2
    (GlobalAddressReuseRawSelection.bucket_bound generation.reusePool info.size info.align thread block.cross raw)
  simp only [CurrentCallConversionChoiceProtocol.advance,reuseEq,intervalEq,↓reduceIte,poolEq,raw.present,Option.getD_some,
    ←selected,Array.getElem?_eq_getElem raw.valid,GlobalAddressReuseRawSelection.output,
    Array.eraseIdxIfInBounds,raw.valid,↓reduceDIte,(Array.getElem?_eq_some_iff.mp raw.present).1]

private theorem advance_rows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (initial : ManagedRows memory addresses generation) (id : AllocId)
    (target : GlobalAddressLiveErrorExclusion.Supplier memory id) (info : AllocationInfo)
    (metadata : memory.getAllocInfo id=.ok info)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (valid : info.align.pow2≤29) (aligned : CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool)
    (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape)
    (room : ∀slack,Room generation.generator info.size info.align slack) :
    ManagedPost memory (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block) := by
  have sizeEq:=CurrentCallConversionInfoRows.queried_size metadata
  cases reuseEq : block.reuse with
  | false =>
    have crosses : block.cross=false ∧block.afterCross=block.afterReuse := by
      simpa only [reuseEq,Bool.false_eq_true,↓reduceIte] using block.crossInput
    have empty : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread block.reuse block.cross=none := by
      simp only [CurrentCallConversionChoiceProtocol.poolRange,reuseEq,Bool.false_eq_true,↓reduceIte]
    have data : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 block.afterCross block.index block.afterIndex := by
      simpa only [empty] using block.indexInput
    let slack:Fin 16:=⟨block.index,data.bound⟩
    let choices:=GlobalAddressAlignedManagedFormation.choices slack
    have allowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseRate false
      (by simpa only [reuseEq] using block.reuseInput.legal)
    have taken:=GlobalAddressAlignedManagedFormation.no_reuse generation.reusePool info.size info.align .other thread allowed
    have completed:=fresh_complete memory addresses generation initial id info metadata uncached thread choices generation.reusePool taken valid (room slack)
    have good:=managed_rows memory addresses generation initial id target uncached info.align valid .other thread choices
      (by rw [sizeEq];exact room slack) (.ok ())
    rw [sizeEq,completed] at good
    have cache:=fresh_cache memory addresses generation initial id info uncached generation.reusePool slack valid (room slack)
    dsimp only at cache completed good
    dsimp only [choices,GlobalAddressAlignedManagedFormation.choices] at good
    rw [cache] at good
    rw [advance_fresh_eq addresses generation id info thread tape block empty data.bound]
    simpa only [reuseEq,Bool.false_eq_true,↓reduceIte,slack] using good
  | true =>
    have allowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseRate true
      (by simpa only [reuseEq] using block.reuseInput.legal)
    have crossData : CurrentCallConversionChoiceProtocol.BoolInput .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits
        block.afterReuse block.cross block.afterCross := by simpa only [reuseEq,↓reduceIte] using block.crossInput
    have crossAllowed:=CurrentCallConversionProbability.allowed generation.reusePool.addressReuseCrossThreadRate block.cross crossData.legal
    cases intervalEq : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread true block.cross with
    | none =>
      have empty : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread block.reuse block.cross=none := by
        simpa only [reuseEq] using intervalEq
      have data : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 block.afterCross block.index block.afterIndex := by
        simpa only [empty] using block.indexInput
      let slack:Fin 16:=⟨block.index,data.bound⟩
      let choices:AddressRandomChoices:=⟨true,block.cross,0,slack⟩
      let pool:=source_reuse_ensure generation.reusePool info.align.pow2
      have taken:=take_empty_reuse generation.reusePool info.size info.align thread block.cross valid allowed crossAllowed intervalEq 0
      have completed:=fresh_complete memory addresses generation initial id info metadata uncached thread choices pool taken valid (room slack)
      have good:=managed_rows memory addresses generation initial id target uncached info.align valid .other thread choices
        (by rw [sizeEq];exact room slack) (.ok ())
      rw [sizeEq,completed] at good
      have cache:=fresh_cache memory addresses generation initial id info uncached pool slack valid (room slack)
      dsimp only at cache completed good
      rw [cache] at good
      rw [advance_fresh_eq addresses generation id info thread tape block empty data.bound]
      simpa only [reuseEq,↓reduceIte,pool,slack] using good
    | some interval =>
      rcases interval with ⟨begin,stop⟩
      have data : CurrentCallConversionChoiceProtocol.IndexInput .addressPool (stop-begin) block.afterCross block.index block.afterIndex := by
        simpa only [reuseEq,intervalEq] using block.indexInput
      obtain ⟨raw,selected⟩:=selected_raw generation.reusePool info.size info.align thread block.cross valid aligned begin stop block.index intervalEq data.bound
      let choices:AddressRandomChoices:=⟨true,block.cross,raw.selected,⟨0,by decide⟩⟩
      have completed:=reused_complete memory addresses generation initial id info thread metadata uncached block.cross raw valid allowed crossAllowed choices.slack
      have good:=managed_rows memory addresses generation initial id target uncached info.align valid .other thread choices
        (by rw [sizeEq];exact room choices.slack) (.ok ())
      rw [sizeEq,completed] at good
      have cache:=reused_cache memory addresses generation initial id info metadata uncached thread block.cross raw valid allowed crossAllowed
      dsimp only at cache completed good
      rw [cache] at good
      rw [advance_reused_eq addresses generation id info thread tape block reuseEq begin stop intervalEq raw selected]
      exact good

private theorem advance_cache (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationInfo) (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape)
    (valid : info.align.pow2≤29) (aligned : CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool) :
    ∃staged address,CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block=
      CurrentCallConversionChoiceProtocol.cacheData staged id address ∧staged.baseAddr=addresses.baseAddr ∧staged.intToPtrMap=addresses.intToPtrMap := by
  cases reuseEq : block.reuse with
  | false =>
    have empty : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread block.reuse block.cross=none := by
      simp only [CurrentCallConversionChoiceProtocol.poolRange,reuseEq,Bool.false_eq_true,↓reduceIte]
    have data : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 block.afterCross block.index block.afterIndex := by
      simpa only [empty] using block.indexInput
    refine ⟨_,_,advance_fresh_eq addresses generation id info thread tape block empty data.bound,?_⟩
    constructor <;> rfl
  | true =>
    cases intervalEq : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread true block.cross with
    | none =>
      have empty : CurrentCallConversionChoiceProtocol.poolRange generation.reusePool info.size info.align thread block.reuse block.cross=none := by
        simpa only [reuseEq] using intervalEq
      have data : CurrentCallConversionChoiceProtocol.IndexInput .addressSlack 16 block.afterCross block.index block.afterIndex := by
        simpa only [empty] using block.indexInput
      refine ⟨_,_,advance_fresh_eq addresses generation id info thread tape block empty data.bound,?_⟩
      constructor <;> rfl
    | some interval =>
      rcases interval with ⟨begin,stop⟩
      have data : CurrentCallConversionChoiceProtocol.IndexInput .addressPool (stop-begin) block.afterCross block.index block.afterIndex := by
        simpa only [reuseEq,intervalEq] using block.indexInput
      obtain ⟨raw,selected⟩:=selected_raw generation.reusePool info.size info.align thread block.cross valid aligned begin stop block.index intervalEq data.bound
      refine ⟨_,_,advance_reused_eq addresses generation id info thread tape block reuseEq begin stop intervalEq raw selected,?_⟩
      constructor <;> rfl

private theorem advance_hits (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationInfo) (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape)
    (valid : info.align.pow2≤29) (aligned : CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none) :
    (∃entry,(CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block).baseAddr.find? (fun row=>row.allocId==id)=some entry) ∧
    ∀query entry,addresses.baseAddr.find? (fun row=>row.allocId==query)=some entry→
      (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block).baseAddr.find? (fun row=>row.allocId==query)=some entry := by
  obtain ⟨staged,address,equal,baseEq,_⟩:=advance_cache addresses generation id info thread tape block valid aligned
  rw [equal]
  refine ⟨⟨_,cacheData_hit staged id address⟩,?_⟩
  intro query entry hit
  exact cacheData_old staged id address (by rw [baseEq];exact uncached) query entry (by rw [baseEq];exact hit)

/-- The pool is relevant only for a selected uncached non-type-ID query. -/
def NeedsAlignment {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (ids : List AllocId) : Prop :=
  ∃id,id∈ids ∧addresses.baseAddr.find? (fun row=>row.allocId==id)=none ∧
    ∃info,memory.getAllocInfo id=.ok info ∧info.kind≠.typeId

private theorem needs_transfer {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (before after : GlobalAddressState) (oldIds nextIds : List AllocId)
    (preserved : ∀id entry,before.baseAddr.find? (fun row=>row.allocId==id)=some entry→
      after.baseAddr.find? (fun row=>row.allocId==id)=some entry)
    (included : ∀id∈nextIds,id∈oldIds) (needed : NeedsAlignment memory after nextIds) :
    NeedsAlignment memory before oldIds := by
  obtain ⟨id,member,missing,info,metadata,kind⟩:=needed
  have oldNone : before.baseAddr.find? (fun row=>row.allocId==id)=none := by
    cases old : before.baseAddr.find? (fun row=>row.allocId==id) with
    | none=>rfl
    | some entry=>have hit:=preserved id entry old;rw [missing] at hit;cases hit
  exact ⟨id,included id member,oldNone,info,metadata,kind⟩

private def GeometryFrame {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (before after : GlobalAddressState) : Prop :=
  ∀address base id size,CurrentCallConversionInfoRows.sizes memory id=size→
    WildcardGeneralHitReborrow.Geometry before.intToPtrMap address base id size→
      WildcardGeneralHitReborrow.Geometry after.intToPtrMap address base id size

private theorem advance_geometry {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState) (id : AllocId) (info : AllocationInfo)
    (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape)
    (valid : info.align.pow2≤29) (aligned : CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool)
    (good : ManagedPost memory (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block)) :
    GeometryFrame memory addresses (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block) := by
  obtain ⟨nextGeneration,good⟩:=good
  obtain ⟨staged,address,equal,_,inverseEq⟩:=advance_cache addresses generation id info thread tape block valid aligned
  intro query base boolId size sizeEq geometry
  have ordered : WildcardInteriorHitAddress.Ordered (CurrentCallConversionChoiceProtocol.cacheData staged id address).intToPtrMap := by
    rw [←equal];exact good.ordered
  have apart : Apart (CurrentCallConversionChoiceProtocol.cacheData staged id address).intToPtrMap (CurrentCallConversionInfoRows.sizes memory) := by
    rw [←equal];exact good.apart
  rw [equal]
  exact CurrentCallConversionBoolQueryFrame.cacheData_geometry staged id address (CurrentCallConversionInfoRows.sizes memory)
    ordered apart query base boolId size (by rw [inverseEq];exact geometry) sizeEq

private theorem cacheData_static (addresses : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (CurrentCallConversionChoiceProtocol.cacheData addresses id address).addressMode=addresses.addressMode ∧
    (CurrentCallConversionChoiceProtocol.cacheData addresses id address).provenanceMode=addresses.provenanceMode ∧
    (CurrentCallConversionChoiceProtocol.cacheData addresses id address).exposed=addresses.exposed := by
  unfold CurrentCallConversionChoiceProtocol.cacheData
  split <;> exact ⟨rfl,rfl,rfl⟩

private theorem advance_static (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationInfo) (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape) :
    (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block).addressMode=addresses.addressMode ∧
    (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block).provenanceMode=addresses.provenanceMode ∧
    (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block).exposed=addresses.exposed := by
  cases reuseEq : block.reuse
  all_goals
    unfold CurrentCallConversionChoiceProtocol.advance
    simp only [reuseEq,Bool.false_eq_true,↓reduceIte]
    try dsimp only
    split
  all_goals first | exact cacheData_static _ _ _ | skip
  all_goals split
  all_goals first | exact ⟨rfl,rfl,rfl⟩ | exact cacheData_static _ _ _

private def AddressBudget {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (ids : List AllocId) (charge : Nat) : Prop :=
  (∀id∈ids,∃entry,addresses.baseAddr.find? (fun row=>row.allocId==id)=some entry) ∨
  ∃generation,ManagedRows memory addresses generation ∧(NeedsAlignment memory addresses ids→CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool) ∧
    generation.generator.nextBaseAddr.toNat+CurrentCallConversionBudgetPotential.misses addresses ids*charge<2^64 ∧
    generation.generator.nextBaseAddr.toNat+CurrentCallConversionBudgetPotential.misses addresses ids*charge≤generation.generator.endAddr.toNat

private theorem cached_budget {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (id : AllocId) (rest : List AllocId) (charge : Nat)
    (budget : AddressBudget memory addresses (id::rest) charge) (entry : BaseAddressEntry)
    (hit : addresses.baseAddr.find? (fun row=>row.allocId==id)=some entry) :
    AddressBudget memory addresses rest charge := by
  rcases budget with all | ⟨generation,good,aligned,limit,ending⟩
  · exact Or.inl (fun query member=>all query (List.mem_cons_of_mem id member))
  · have equal : CurrentCallConversionBudgetPotential.misses addresses (id::rest)=CurrentCallConversionBudgetPotential.misses addresses rest := by
      simp only [CurrentCallConversionBudgetPotential.misses,List.filter_cons,hit,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
    rw [equal] at limit ending
    exact Or.inr ⟨generation,good,(fun needed=>aligned (needs_transfer memory addresses addresses (id::rest) rest
      (fun _ _ hit=>hit) (fun _ member=>List.mem_cons_of_mem id member) needed)),limit,ending⟩

private theorem managed_budget {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (id : AllocId) (rest : List AllocId) (charge : Nat)
    (budget : AddressBudget memory addresses (id::rest) charge)
    (target : GlobalAddressLiveErrorExclusion.Supplier memory id) (info : AllocationInfo)
    (metadata : memory.getAllocInfo id=.ok info) (nonType : info.kind≠.typeId)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (generation : AddressGenerationState) (generationEq : addresses.generation=some generation)
    (valid : info.align.pow2≤29)
    (charged : 15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤charge)
    (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape) :
    ∃initial : ManagedRows memory addresses generation,
      CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool ∧
      (∀slack,Room generation.generator info.size info.align slack) ∧
      AddressBudget memory (CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block) rest charge := by
  rcases budget with all | ⟨oldGeneration,initial,aligned,limit,ending⟩
  · obtain ⟨entry,hit⟩:=all id (by simp)
    rw [uncached] at hit
    cases hit
  · have same : oldGeneration=generation:=Option.some.inj (initial.generationEq.symm.trans generationEq)
    subst oldGeneration
    have fullAligned:=aligned ⟨id,by simp,uncached,info,metadata,nonType⟩
    have one : 1≤CurrentCallConversionBudgetPotential.misses addresses (id::rest) := by
      simp only [CurrentCallConversionBudgetPotential.misses,List.filter_cons,uncached,Option.isNone_none,↓reduceIte,List.length_cons]
      omega
    have weighted : charge≤CurrentCallConversionBudgetPotential.misses addresses (id::rest)*charge := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right charge one
    have room : ∀slack,Room generation.generator info.size info.align slack := by
      intro slack
      have small:=slack.isLt
      unfold Room
      constructor <;> omega
    let advanced:=CurrentCallConversionChoiceProtocol.advance addresses generation id info thread tape block
    obtain ⟨nextGeneration,good⟩:=advance_rows memory addresses generation initial id target info metadata uncached valid fullAligned thread tape block room
    obtain ⟨numericGeneration,numericEq,endEq,_,grows,nextAligned⟩:=CurrentCallConversionAdvanceNumeric.bounds
      addresses generation id info thread tape block generationEq fullAligned valid room charge charged
    have same : nextGeneration=numericGeneration:=Option.some.inj (good.generationEq.symm.trans numericEq)
    subst numericGeneration
    obtain ⟨⟨entry,hit⟩,preserved⟩:=advance_hits addresses generation id info thread tape block valid fullAligned uncached
    have paid:=CurrentCallConversionBudgetPotential.charge addresses advanced (id::rest) id (by simp) uncached
      preserved entry hit generation.generator.nextBaseAddr.toNat nextGeneration.generator.nextBaseAddr.toNat charge grows
    have equal : CurrentCallConversionBudgetPotential.misses advanced (id::rest)=CurrentCallConversionBudgetPotential.misses advanced rest := by
      dsimp only [advanced]
      simp only [CurrentCallConversionBudgetPotential.misses,List.filter_cons,hit,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
    rw [equal] at paid
    refine ⟨initial,fullAligned,room,Or.inr ⟨nextGeneration,good,(fun _=>nextAligned),?_,?_⟩⟩
    · exact Nat.lt_of_le_of_lt paid limit
    · rw [endEq]
      exact Nat.le_trans paid ending

private theorem zero_rows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (initial : ManagedRows memory addresses generation) (id : AllocId) :
    ManagedRows memory (CurrentCallConversionChoiceProtocol.cacheData addresses id 0) generation := by
  change ManagedRows memory {addresses with baseAddr:=(addresses.baseAddr.filter (fun row=>row.allocId != id)).push ⟨id,0⟩} generation
  exact ⟨initial.ordered,initial.apart,initial.rows,initial.generationEq,initial.managed,
    initial.cursor,initial.frontier,initial.holes,initial.bounded,initial.pairwise⟩

private theorem zero_budget {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (id : AllocId) (rest : List AllocId) (charge : Nat)
    (budget : AddressBudget memory addresses (id::rest) charge)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none) :
    AddressBudget memory (CurrentCallConversionChoiceProtocol.cacheData addresses id 0) rest charge := by
  rcases budget with all | ⟨generation,initial,aligned,limit,ending⟩
  · obtain ⟨entry,hit⟩:=all id (by simp)
    rw [uncached] at hit
    cases hit
  · let advanced:=CurrentCallConversionChoiceProtocol.cacheData addresses id 0
    have paid:=CurrentCallConversionBudgetPotential.uncharged addresses advanced (id::rest)
      (cacheData_old addresses id 0 uncached) generation.generator.nextBaseAddr.toNat
      generation.generator.nextBaseAddr.toNat charge (Nat.le_refl _)
    have equal : CurrentCallConversionBudgetPotential.misses advanced (id::rest)=CurrentCallConversionBudgetPotential.misses advanced rest := by
      dsimp only [advanced]
      simp only [CurrentCallConversionBudgetPotential.misses,List.filter_cons,cacheData_hit,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
    rw [equal] at paid
    exact Or.inr ⟨generation,zero_rows memory addresses generation initial id,
      (fun needed=>aligned (needs_transfer memory addresses advanced (id::rest) rest
        (cacheData_old addresses id 0 uncached) (fun _ member=>List.mem_cons_of_mem id member) needed)),
      Nat.lt_of_le_of_lt paid limit,Nat.le_trans paid ending⟩

private theorem actual_tape_putGet (machine : ActualMachine) : actualTape.put machine (actualTape.get machine)=machine := rfl

private theorem addressMachine_current (machine : ActualMachine) (addresses : GlobalAddressState) :
    addressMachine machine addresses (actualTape.get machine)=withAddresses machine addresses := by
  unfold addressMachine
  rw [actual_tape_putGet]

private theorem replay_head (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl)
    (machine : ActualMachine) (id : AllocId) (rest : List AllocId) (finalAddresses : GlobalAddressState)
    (finalTape : ExecutionChoices.Tape) (charge : Nat)
    (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol machine.memory
      (UInt32.ofNat machine.threads.activeThread.toNat) machine.user.addresses (actualTape.get machine) (id::rest) finalAddresses finalTape)
    (budget : AddressBudget machine.memory machine.user.addresses (id::rest) charge)
    (target : GlobalAddressLiveErrorExclusion.Supplier machine.memory id)
    (formation : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none→
      ∀info,machine.memory.getAllocInfo id=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤charge)
    (race : machine.dataRace=none) :
    ∃base addresses tape,MachineAddress.addrFromAllocId actualTape hooks id (some .other) machine=
      .ok base (addressMachine machine addresses tape) ∧
      CurrentCallConversionChoiceProtocol.AddressProtocol machine.memory (UInt32.ofNat machine.threads.activeThread.toNat)
        addresses tape rest finalAddresses finalTape ∧AddressBudget machine.memory addresses rest charge ∧
      (∀query entry,machine.user.addresses.baseAddr.find? (fun row=>row.allocId==query)=some entry→
        addresses.baseAddr.find? (fun row=>row.allocId==query)=some entry) ∧
      GeometryFrame machine.memory machine.user.addresses addresses ∧
      addresses.addressMode=machine.user.addresses.addressMode ∧addresses.provenanceMode=machine.user.addresses.provenanceMode ∧
      addresses.exposed=machine.user.addresses.exposed := by
  cases protocol with
  | cached addresses tape id rest base hit finalAddresses finalTape tail =>
    refine ⟨base.address,machine.user.addresses,(actualTape.get machine),?_,tail,cached_budget machine.memory machine.user.addresses id rest charge budget base hit,?_,?_,rfl,rfl,rfl⟩
    · have actual:=cached_address hooks machine id base hit
      simpa only [addressMachine_current,withAddresses] using actual
    · intro query entry hit
      exact hit
    · intro _ _ _ _ _ geometry;exact geometry
  | typeId addresses tape id rest info uncached metadata kind finalAddresses finalTape tail =>
    refine ⟨0,CurrentCallConversionChoiceProtocol.cacheData machine.user.addresses id 0,(actualTape.get machine),?_,tail,
      zero_budget machine.memory machine.user.addresses id rest charge budget uncached,cacheData_old machine.user.addresses id 0 uncached,?_,(cacheData_static machine.user.addresses id 0).1,
      (cacheData_static machine.user.addresses id 0).2.1,(cacheData_static machine.user.addresses id 0).2.2⟩
    · have actual:=type_id_address hooks machine id info uncached metadata kind (supplier_live machine.memory id target)
      simpa only [addressMachine_current] using actual
    · intro _ _ _ _ _ geometry;exact geometry
  | managed addresses tape id rest info uncached metadata kind generation generationEq block finalAddresses finalTape tail =>
    obtain ⟨nondead,valid,charged⟩:=formation uncached info metadata
    obtain ⟨initial,aligned,room,budgetTail⟩:=managed_budget machine.memory machine.user.addresses id rest charge budget target info metadata kind
      uncached generation generationEq valid charged _ (actualTape.get machine) block
    obtain ⟨base,actual⟩:=managed_address hooks machine id info generation initial uncached metadata nondead kind
      (supplier_live machine.memory id target) race valid aligned block room
    exact ⟨base,_,_,actual,tail,budgetTail,(advance_hits machine.user.addresses generation id info _ (actualTape.get machine) block valid aligned uncached).2,
      advance_geometry machine.memory machine.user.addresses generation id info _ (actualTape.get machine) block valid aligned
        (advance_rows machine.memory machine.user.addresses generation initial id target info metadata uncached valid aligned _ (actualTape.get machine) block room),
      (advance_static machine.user.addresses generation id info _ (actualTape.get machine) block).1,
      (advance_static machine.user.addresses generation id info _ (actualTape.get machine) block).2.1,
      (advance_static machine.user.addresses generation id info _ (actualTape.get machine) block).2.2⟩

private def conversionMachine (initial : ActualMachine) (tracker : MachineHooks.BorrowState)
    (global : GlobalState) (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) : ActualMachine :=
  addressMachine {initial with borrowTracker:=some {tracker with global:=global}} addresses tape

private theorem conversionMachine_initial (initial : ActualMachine) (tracker : MachineHooks.BorrowState)
    (enabled : initial.borrowTracker=some tracker) :
    conversionMachine initial tracker tracker.global initial.user.addresses (actualTape.get initial)=initial := by
  unfold conversionMachine
  change addressMachine {initial with borrowTracker:=some tracker} initial.user.addresses (actualTape.get initial)=initial
  rw [←enabled]
  change addressMachine initial initial.user.addresses (actualTape.get initial)=initial
  rw [addressMachine_current]
  rfl

private theorem conversionMachine_address (initial : ActualMachine) (tracker : MachineHooks.BorrowState)
    (global : GlobalState) (addresses nextAddresses : GlobalAddressState) (tape nextTape : ExecutionChoices.Tape) :
    addressMachine (conversionMachine initial tracker global addresses tape) nextAddresses nextTape=
      conversionMachine initial tracker global nextAddresses nextTape := by
  dsimp only [conversionMachine,addressMachine]
  rw [tape_addresses,actual_tape_laws.putPut]
  rfl

private theorem conversionMachine_root (initial : ActualMachine) (tracker : MachineHooks.BorrowState)
    (global : GlobalState) (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) (id : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615) :
    CurrentCallConversionRootPointer.machine (conversionMachine initial tracker global addresses tape)
      {tracker with global:=global} id room=
      conversionMachine initial tracker (CurrentCallConversionRootPointer.global global id room) addresses tape := rfl

private theorem metadata_frame (initial current : ActualMachine) (id : AllocId)
    (metadata : CurrentCallOrdinaryInput.RelocationTargetMetadata initial id)
    (memoryEq : current.memory=initial.memory)
    (bases : ∀query entry,initial.user.addresses.baseAddr.find? (fun row=>row.allocId==query)=some entry→
      current.user.addresses.baseAddr.find? (fun row=>row.allocId==query)=some entry) :
    CurrentCallOrdinaryInput.RelocationTargetMetadata current id := by
  unfold CurrentCallOrdinaryInput.RelocationTargetMetadata at metadata ⊢
  rw [memoryEq]
  refine ⟨metadata.1,metadata.2.1,?_⟩
  intro uncached
  have oldNone : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none := by
    cases old : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id) with
    | none=>rfl
    | some entry=>have hit:=bases id entry old;rw [uncached] at hit;cases hit
  exact metadata.2.2 oldNone

private theorem formation_frame (initial current : ActualMachine) (id : AllocId)
    (metadata : CurrentCallOrdinaryInput.RelocationTargetMetadata initial id)
    (memoryEq : current.memory=initial.memory)
    (bases : ∀query entry,initial.user.addresses.baseAddr.find? (fun row=>row.allocId==query)=some entry→
      current.user.addresses.baseAddr.find? (fun row=>row.allocId==query)=some entry)
    (uncached : current.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (info : AllocationInfo) (actual : current.memory.getAllocInfo id=.ok info) :
    info.kind≠.dead ∧info.align.pow2≤29 ∧
      15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤CurrentCallOrdinaryInput.addressCharge initial := by
  have oldActual : initial.memory.getAllocInfo id=.ok info := by rw [←memoryEq];exact actual
  have oldNone : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none := by
    cases old : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id) with
    | none=>rfl
    | some entry=>have hit:=bases id entry old;rw [uncached] at hit;cases hit
  obtain ⟨other,found,nondead,_,_⟩:=CurrentCallConversionMetadataBounds.metadata metadata
  have same : other=info:=Except.ok.inj (found.symm.trans oldActual)
  subst other
  have valid:=CurrentCallConversionMetadataBounds.valid_alignment metadata oldNone info oldActual
  have charged:=CurrentCallConversionMetadataBounds.charge metadata.1 info oldActual
  have alignNat:=(reuse_source ".CurrentCallConversionMetadataBounds.alignment_nat") info.align valid
  rw [←alignNat,←GlobalAddressBumpRangeFormation.length_nat] at charged
  exact ⟨nondead,valid,charged⟩

private theorem root_flags (global : GlobalState) (id : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615) :
    (CurrentCallConversionRootPointer.global global id room).protectedTags=global.protectedTags := by
  cases cached : global.rootTag? id <;> simp only [CurrentCallConversionRootPointer.global,cached] <;> rfl

private theorem root_mono (global : GlobalState) (id : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615) :
    global.nextPointerTag.value.toNat≤(CurrentCallConversionRootPointer.global global id room).nextPointerTag.value.toNat := by
  cases cached : global.rootTag? id with
  | some tag=>simp only [CurrentCallConversionRootPointer.global,cached];exact Nat.le_refl _
  | none=>
    simp only [CurrentCallConversionRootPointer.global,cached,GeneralBorrowFnEntryRegistration.advanced]
    rw [GenericFunctionEntryNumerics.successor_value global.nextPointerTag room]
    omega

private def rowIds (rows : List Row) : List AllocId := rows.map (fun row=>row.provenance.allocId)
private def rootMisses (global : GlobalState) (ids : List AllocId) : Nat :=
  (ids.filter (fun id=>(global.rootTag? id).isNone)).length

private def Run (initial : ActualMachine) (tracker : MachineHooks.BorrowState)
    (tailIds : List AllocId) (charge reserve : Nat) (finalAddresses : GlobalAddressState)
    (finalTape : ExecutionChoices.Tape) (rows : List Row) (current : ActualMachine) : Prop :=
  ∃global addresses tape,current=conversionMachine initial tracker global addresses tape ∧
    CurrentCallConversionChoiceProtocol.AddressProtocol initial.memory (UInt32.ofNat initial.threads.activeThread.toNat)
      addresses tape (rowIds rows++tailIds) finalAddresses finalTape ∧
    AddressBudget initial.memory addresses (rowIds rows++tailIds) charge ∧
    global.nextPointerTag.value.toNat+rootMisses global (rowIds rows++tailIds)+reserve<2^64 ∧
    (∀row∈rows,CurrentCallOrdinaryInput.RelocationTargetMetadata initial row.provenance.allocId) ∧
    (∀row∈rows,addresses.baseAddr.find? (fun base=>base.allocId==row.provenance.allocId)=none→
      ∀info,initial.memory.getAllocInfo row.provenance.allocId=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤charge) ∧
    (∀id entry,initial.user.addresses.baseAddr.find? (fun base=>base.allocId==id)=some entry→
      addresses.baseAddr.find? (fun base=>base.allocId==id)=some entry) ∧
    (∀id tag,tracker.global.rootTag? id=some tag→global.rootTag? id=some tag) ∧
    global.protectedTags=tracker.global.protectedTags ∧(tracker.global.nextPointerTag.value.toNat≤global.nextPointerTag.value.toNat) ∧
    GeometryFrame initial.memory initial.user.addresses addresses ∧addresses.addressMode=initial.user.addresses.addressMode ∧
    addresses.provenanceMode=initial.user.addresses.provenanceMode ∧addresses.exposed=initial.user.addresses.exposed

private theorem resolve_run (initial : ActualMachine) (tracker : MachineHooks.BorrowState)
    (tailIds : List AllocId) (charge reserve : Nat) (positiveReserve : 0<reserve)
    (finalAddresses : GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl) (width : hooks.arithmetic=⟨Size.ofBytes 8⟩)
    (layout : TargetDataLayout)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind ActualControl (Pointer Provenance))
    (race : initial.dataRace=none) (row : Row) (rest : List Row) (current : ActualMachine)
    (run : Run initial tracker tailIds charge reserve finalAddresses finalTape (row::rest) current) :
    ∃adjusted next,PointerSource.globalRootPointer actualTape hooks externStatic
      (Pointer.new row.provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout row.word))) current=
        .ok adjusted next ∧Run initial tracker tailIds charge reserve finalAddresses finalTape rest next := by
  obtain ⟨global,addresses,tape,machineEq,protocol,budget,bounded,metadata,formation,bases,roots,flags,monotone,geometries,modeEq,provEq,exposedEq⟩:=run
  subst current
  let current:=conversionMachine initial tracker global addresses tape
  have room : global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change global.nextPointerTag.value.toNat<18446744073709551615
    omega
  let nextGlobal:=CurrentCallConversionRootPointer.global global row.provenance.allocId room
  let rooted:=CurrentCallConversionRootPointer.machine current {tracker with global:=global} row.provenance.allocId room
  have currentMetadata:=metadata_frame initial current row.provenance.allocId (metadata row (by simp)) rfl bases
  have rootedMetadata:=metadata_frame initial rooted row.provenance.allocId (metadata row (by simp)) rfl bases
  have formed : rooted.user.addresses.baseAddr.find? (fun base=>base.allocId==row.provenance.allocId)=none→
      ∀info,rooted.memory.getAllocInfo row.provenance.allocId=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤charge :=
    formation row (by simp)
  obtain ⟨base,nextAddresses,nextTape,address,tail,tailBudget,preserved,geometryStep,newMode,newProv,newExposed⟩:=replay_head hooks rooted row.provenance.allocId
    (rowIds rest++tailIds) finalAddresses finalTape charge protocol budget rootedMetadata.1 formed race
  let after:=conversionMachine initial tracker nextGlobal nextAddresses nextTape
  have afterEq : addressMachine rooted nextAddresses nextTape=after := by
    dsimp only [rooted,current,after,nextGlobal]
    rw [conversionMachine_root,conversionMachine_address]
  have actual:=CurrentCallConversionRootPointer.from_address current {tracker with global:=global} rfl row.provenance
    (GlobalRelocationWordDecode.value layout row.word) currentMetadata room hooks width externStatic base _ address
  rw [afterEq] at actual
  refine ⟨_,after,actual,?_⟩
  obtain ⟨_,hit,kept,potential⟩:=CurrentCallConversionRootPointer.facts global (row.provenance.allocId::(rowIds rest++tailIds))
    row.provenance.allocId (by simp) room
  have rootBound : nextGlobal.nextPointerTag.value.toNat+rootMisses nextGlobal (rowIds rest++tailIds)+reserve<2^64 := by
    have equal : rootMisses nextGlobal (row.provenance.allocId::(rowIds rest++tailIds))=rootMisses nextGlobal (rowIds rest++tailIds) := by
      dsimp only [nextGlobal]
      simp only [rootMisses,List.filter_cons,hit,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
    change nextGlobal.nextPointerTag.value.toNat+rootMisses nextGlobal (row.provenance.allocId::(rowIds rest++tailIds))≤
      global.nextPointerTag.value.toNat+rootMisses global (row.provenance.allocId::(rowIds rest++tailIds)) at potential
    rw [equal] at potential
    change global.nextPointerTag.value.toNat+rootMisses global (row.provenance.allocId::(rowIds rest++tailIds))+reserve<2^64 at bounded
    omega
  refine ⟨nextGlobal,nextAddresses,nextTape,rfl,tail,tailBudget,rootBound,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro old member;exact metadata old (List.mem_cons_of_mem row member)
  · intro old member missing info queried
    have oldMissing : addresses.baseAddr.find? (fun base=>base.allocId==old.provenance.allocId)=none := by
      cases previous : addresses.baseAddr.find? (fun base=>base.allocId==old.provenance.allocId) with
      | none=>rfl
      | some entry=>have hit:=preserved old.provenance.allocId entry previous;rw [missing] at hit;cases hit
    exact formation old (List.mem_cons_of_mem row member) oldMissing info queried
  · intro id entry old;exact preserved id entry (bases id entry old)
  · intro id tag old;exact kept id tag (roots id tag old)
  · exact (root_flags global row.provenance.allocId room).trans flags
  · exact Nat.le_trans monotone (root_mono global row.provenance.allocId room)
  · intro address base id size sizeEq geometry
    exact geometryStep address base id size sizeEq (geometries address base id size sizeEq geometry)
  · exact newMode.trans modeEq
  · exact newProv.trans provEq
  · exact newExposed.trans exposedEq

private theorem strict_tape_exhausted {State : Type}
    (access : ExecutionChoices.Access State) (state : State)
    (empty : access.get state=⟨#[],0,.strict,0,0,#[]⟩) :
    ExecutionChoices.index access .addressSlack 16 state=
      .error (.callback "choice input unknown: tape exhausted") state := by
  unfold ExecutionChoices.index
  unfold_internal ".ExecutionChoices.demand"
  unfold_internal ".ExecutionChoices.unknown"
  simp [empty,pure,Pure.pure,bind,Bind.bind,get,getThe,MonadStateOf.get,EStateM.get,
    EStateM.bind,throw,MonadExcept.throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  rfl

private theorem one {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (initial current next : State) (row : Row) (adjusted : Pointer Provenance)
    (bytes : Array UInt8) (provenance : Array (Size × Provenance))
    (width : layout.pointerWidth = .w64)
    (window : bytes.extract row.position.bytes.toNat (row.position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes row.word)
    (bounds : row.position.bytes.toNat+8≤bytes.size)
    (resolved : pointer (Pointer.new row.provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout row.word))) current =
      .ok adjusted next) :
    ∃ encoded : Array UInt8, encoded.size=8 ∧
      action source layout pointer initial (input row) (none,bytes,current,provenance) =
        ForInStep.yield (none,GlobalRelocationSplice.patch bytes encoded row.position.bytes.toNat,next,
          provenance.push (row.position,adjusted.provenance)) := by
  obtain ⟨encoded,encoding,size⟩ := PhysicalScalarReturn.target_word_exists layout
    (BitVec.ofNat 128 adjusted.offset.bytes.toNat)
  refine ⟨encoded,size,?_⟩
  unfold action GlobalRelocationActualStep.step
  unfold_global_data ".Miri.Memory.pointerSize"
  unfold_global_data ".Miri.Memory.maxU64Nat"
  have offsetBound := UInt64.toNat_lt (GlobalRelocationWordDecode.value layout row.word)
  have offset128 : (GlobalRelocationWordDecode.value layout row.word).toNat < 340282366920938463463374607431768211456 := by omega
  simp only [Pointer.new,Size.ofBytes] at resolved
  simp only [Size.ofBytes] at encoding
  simp [-Array.extract_append,-Array.extract_extract,input,width,Pointer.new,Size.fromBits,PointerWidth.bits,
    window,GlobalRelocationWordDecode.read,resolved,encoding,Size.ofBytes,
    show ¬(row.position.bytes.toNat+8>bytes.size) from by omega,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt offset128,
    show ¬((GlobalRelocationWordDecode.value layout row.word).toNat>18446744073709551615) from by omega,
    GlobalRelocationSplice.patch,Array.append_assoc,bind,Bind.bind,pure,Pure.pure]

/-- Internal induction over the actual source loop. The callback invariant is
instantiated with converter resources, not supplied by an ordinary caller. -/
private theorem fold {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (initial : State) (invariant : List Row→State→Prop)
    (width : layout.pointerWidth = .w64) (rows : List Row)
    (separate : rows.Pairwise Separate)
    (resolve : ∀row rest current,invariant (row::rest) current→∃adjusted next,
      pointer (Pointer.new row.provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout row.word))) current=
        .ok adjusted next ∧invariant rest next)
    (current : State) (good : invariant rows current) (bytes : Array UInt8)
    (provenance : Array (Size × Provenance))
    (windows : ∀row∈rows,bytes.extract row.position.bytes.toNat (row.position.bytes.toNat+8)=GlobalRelocationWordDecode.bytes row.word)
    (bounds : ∀row∈rows,row.position.bytes.toNat+8≤bytes.size) :
    ∃(finalBytes : Array UInt8) (next : State) (outputs : List (Size × Provenance)), finalBytes.size=bytes.size ∧invariant [] next ∧
      outputs.map Prod.fst=rows.map (fun row=>row.position) ∧
      forIn (rows.map input) (none,bytes,current,provenance) (action source layout pointer initial)=
        (none,finalBytes,next,provenance++outputs.toArray) := by
  induction rows generalizing current bytes provenance with
  | nil => exact ⟨bytes,current,[],rfl,good,rfl,by simp [pure,Pure.pure]⟩
  | cons row rest ih =>
    obtain ⟨adjusted,after,resolved,afterGood⟩:=resolve row rest current good
    obtain ⟨encoded,encodedSize,step⟩:=one source layout pointer initial current after row adjusted bytes provenance
      width (windows row (by simp)) (bounds row (by simp)) resolved
    have patchedSize:=GlobalRelocationSplice.size bytes encoded row.position.bytes.toNat (bounds row (by simp)) encodedSize
    have windowsRest : ∀next∈rest,
        (GlobalRelocationSplice.patch bytes encoded row.position.bytes.toNat).extract next.position.bytes.toNat
          (next.position.bytes.toNat+8)=GlobalRelocationWordDecode.bytes next.word := by
      intro next member
      exact (GlobalRelocationSplice.later_window bytes encoded row.position.bytes.toNat next.position.bytes.toNat
        ((List.pairwise_cons.mp separate).1 next member) (bounds next (by simp [member])) encodedSize).trans
        (windows next (by simp [member]))
    obtain ⟨finalBytes,next,outputs,size,nextGood,positions,loop⟩:=ih (List.pairwise_cons.mp separate).2
      after afterGood
      (GlobalRelocationSplice.patch bytes encoded row.position.bytes.toNat)
      (provenance.push (row.position,adjusted.provenance)) windowsRest
      (fun next member=>by rw [patchedSize];exact bounds next (by simp [member]))
    refine ⟨finalBytes,next,(row.position,adjusted.provenance)::outputs,size.trans patchedSize,nextGood,?_,?_⟩
    · simp only [List.map_cons,positions]
    · simp only [List.map_cons,List.forIn_cons,step,bind,Bind.bind]
      rw [loop]
      rw [List.toArray_cons,Array.push_eq_append,Array.append_assoc]

private theorem sorted (outputs : List (Size × Provenance))
    (separate : outputs.Pairwise (fun a b=>a.1.bytes.toNat+8≤b.1.bytes.toNat)) :
    source_sorted_keys outputs=true := by
  induction outputs with
  | nil =>
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    rfl
  | cons row rest ih =>
    cases rest with
    | nil =>
      unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
      rfl
    | cons next tail =>
      have bounded := (List.pairwise_cons.mp separate).1 next (by simp)
      have ordered : row.1.bytes<next.1.bytes := by
        change row.1.bytes.toNat<next.1.bytes.toNat
        omega
      have orderedTail:=ih (List.pairwise_cons.mp separate).2
      unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
      simpa only [ordered,decide_true,Bool.true_and] using orderedTail

private theorem output_geometry (rows : List Row) (outputs : List (Size × Provenance))
    (positions : outputs.map Prod.fst=rows.map (fun row=>row.position))
    (separate : rows.Pairwise Separate) (capacity : Nat)
    (bounds : ∀row∈rows,row.position.bytes.toNat+8≤capacity) :
    outputs.Pairwise (fun a b=>a.1.bytes.toNat+8≤b.1.bytes.toNat) ∧
      (∀entry∈outputs,entry.1.bytes.toNat+8≤capacity) := by
  constructor
  · have source : (rows.map (fun row=>row.position)).Pairwise (fun a b=>a.bytes.toNat+8≤b.bytes.toNat):=
      List.pairwise_map.mpr separate
    rw [←positions] at source
    exact List.pairwise_map.mp source
  · intro entry member
    have target : entry.1∈rows.map (fun row=>row.position):=by rw [←positions];exact List.mem_map.mpr ⟨entry,member,rfl⟩
    obtain ⟨row,member,equal⟩:=List.mem_map.mp target
    rw [←equal]
    exact bounds row member

private theorem finish {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance)) (initial next : State)
    (bytes : Array UInt8) (outputs : List (Size × Provenance))
    (separate : outputs.Pairwise (fun a b=>a.1.bytes.toNat+8≤b.1.bytes.toNat))
    (size : bytes.size=(AllocationCopy.snapshot source).size)
    (bounds : ∀entry∈outputs,entry.1.bytes.toNat+8≤bytes.size) :
    ∃converted : Allocation Provenance Unit,
      GlobalRelocationActualStep.finish source layout (fun _ _ state=>.ok (AllocationCopy.snapshot source) state)
        pointer initial (none,bytes,next,outputs.toArray)=.ok converted next ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      converted.provenanceMap.ptrs=outputs.toArray ∧converted.provenanceMap.byteFragments=none ∧
      ProvenanceCopy.WellFormed converted.provenanceMap converted.len := by
  have ordered:=sorted outputs separate
  have convertedProvenance : ∃provenance : ProvenanceMap Provenance,
      ProvenanceMap.fromPresortedPtrs outputs.toArray=.ok provenance ∧
      provenance.ptrs=outputs.toArray ∧provenance.byteFragments=none := by
    simp only [ProvenanceMap.fromPresortedPtrs,ordered,ite_true]
    exact ⟨_,rfl,rfl,rfl⟩
  obtain ⟨provenance,conversion,ptrs,fragments⟩:=convertedProvenance
  unfold GlobalRelocationActualStep.finish
  cases source
  rename_i raw allocationSize sourceProvenance mask align mutability extra native
  simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,pure,Pure.pure,Except.pure,Except.toOption] at size
  simp [conversion,pure,Pure.pure,bind,Bind.bind]
  refine ⟨_,rfl,⟨rfl,size,rfl,rfl,rfl,rfl⟩,ptrs,fragments,?_⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [Allocation.provenanceMap,ptrs,List.toList_toArray]
    exact separate
  · simp [Allocation.provenanceMap,fragments]
  · intro entry member
    have hit : entry∈outputs:=by simpa only [Allocation.provenanceMap,ptrs,List.mem_toArray] using member
    exact bounds entry hit
  · simp [Allocation.provenanceMap,fragments]
  · simp [ProvenanceCopy.FragmentsAvoidPointers,Allocation.provenanceMap,fragments]

private theorem convert {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (initial : State) (invariant : List Row→State→Prop) (rows : List Row) (good : invariant rows initial)
    (width : layout.pointerWidth=.w64)
    (separate : rows.Pairwise Separate)
    (resolve : ∀row rest current,invariant (row::rest) current→∃adjusted next,
      pointer (Pointer.new row.provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout row.word))) current=
        .ok adjusted next ∧invariant rest next)
    (windows : ∀row∈rows,(AllocationCopy.snapshot source).extract row.position.bytes.toNat
      (row.position.bytes.toNat+8)=GlobalRelocationWordDecode.bytes row.word)
    (bounds : ∀row∈rows,row.position.bytes.toNat+8≤(AllocationCopy.snapshot source).size)
    (relocations : source.provenanceMap.ptrs=(rows.map input).toArray)
    (noFragments : source.provenanceMap.byteFragments=none) :
    ∃(converted : Allocation Provenance Unit) (next : State),
      Allocation.adjustFromTcx source layout
        (fun _ _ state=>.ok (AllocationCopy.snapshot source) state) pointer initial=.ok converted next ∧
      invariant [] next ∧GlobalAllocationAttributes.Attributes source converted ∧
      ProvenanceCopy.WellFormed converted.provenanceMap converted.len ∧
      converted.provenanceMap.byteFragments=none := by
  obtain ⟨bytes,next,outputs,size,nextGood,positions,loop⟩:=fold source layout pointer initial invariant width rows
    separate resolve initial good (AllocationCopy.snapshot source) #[] windows bounds
  have loopArray : forIn (rows.map input).toArray (none,AllocationCopy.snapshot source,initial,#[])
      (action source layout pointer initial)=(none,bytes,next,outputs.toArray) := by
    rw [←Array.forIn_toList]
    simpa only [List.toList_toArray,Array.empty_append] using loop
  obtain ⟨ordered,contained⟩:=output_geometry rows outputs positions separate bytes.size
    (fun row member=>by rw [size];exact bounds row member)
  obtain ⟨converted,finished,attributes,_,fragments,well⟩:=finish source layout pointer initial next bytes outputs ordered size contained
  refine ⟨converted,next,?_,nextGood,attributes,well,fragments⟩
  rw [GlobalRelocationActualStep.adjust_eq_loop source layout pointer initial noFragments,relocations]
  dsimp only [action] at loopArray
  rw [loopArray]
  exact finished

private theorem complete_run (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (hooks : MachineAddress.Hooks MiriMemoryKind ActualControl) (width : hooks.arithmetic=⟨Size.ofBytes 8⟩)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind ActualControl (Pointer Provenance))
    (initial : ActualMachine) (tracker : MachineHooks.BorrowState) (enabled : initial.borrowTracker=some tracker)
    (tailIds : List AllocId) (charge reserve : Nat) (positiveReserve : 0<reserve)
    (finalAddresses : GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol initial.memory (UInt32.ofNat initial.threads.activeThread.toNat)
      initial.user.addresses (actualTape.get initial) (rowIds (CurrentCallConversionRows.rows source)++tailIds) finalAddresses finalTape)
    (budget : AddressBudget initial.memory initial.user.addresses (rowIds (CurrentCallConversionRows.rows source)++tailIds) charge)
    (bounded : tracker.global.nextPointerTag.value.toNat+rootMisses tracker.global (rowIds (CurrentCallConversionRows.rows source)++tailIds)+reserve<2^64)
    (metadata : ∀row∈CurrentCallConversionRows.rows source,CurrentCallOrdinaryInput.RelocationTargetMetadata initial row.provenance.allocId)
    (formation : ∀row∈CurrentCallConversionRows.rows source,initial.user.addresses.baseAddr.find? (fun base=>base.allocId==row.provenance.allocId)=none→
      ∀info,initial.memory.getAllocInfo row.provenance.allocId=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤charge)
    (race : initial.dataRace=none) (storage : CurrentCallOrdinaryInput.Storage source)
    (format : CurrentCallOrdinaryInput.CompilerFormat source) (layoutWidth : layout.pointerWidth=.w64) :
    ∃(converted : Allocation Provenance Unit) (next : ActualMachine),
      Allocation.adjustFromTcx source layout (fun _ _ state=>.ok (AllocationCopy.snapshot source) state)
        (PointerSource.globalRootPointer actualTape hooks externStatic) initial=.ok converted next ∧
      Run initial tracker tailIds charge reserve finalAddresses finalTape [] next ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      ProvenanceCopy.WellFormed converted.provenanceMap converted.len ∧converted.provenanceMap.byteFragments=none := by
  obtain ⟨inputEq,separate,bounds,windows⟩:=CurrentCallConversionRows.of_storage source storage
  have initialRun : Run initial tracker tailIds charge reserve finalAddresses finalTape (CurrentCallConversionRows.rows source) initial :=
    ⟨tracker.global,initial.user.addresses,actualTape.get initial,(conversionMachine_initial initial tracker enabled).symm,
      protocol,budget,bounded,metadata,formation,(fun _ _ hit=>hit),(fun _ _ hit=>hit),rfl,Nat.le_refl _,
      (fun _ _ _ _ _ geometry=>geometry),rfl,rfl,rfl⟩
  have relocations : source.provenanceMap.ptrs=((CurrentCallConversionRows.rows source).map input).toArray := by
    rw [inputEq,Array.toArray_toList]
  exact convert source layout (PointerSource.globalRootPointer actualTape hooks externStatic) initial
    (Run initial tracker tailIds charge reserve finalAddresses finalTape) (CurrentCallConversionRows.rows source) initialRun
    layoutWidth separate (resolve_run initial tracker tailIds charge reserve positiveReserve finalAddresses finalTape hooks width layout externStatic race)
    windows bounds relocations format

/-- The converter's actual machine/control shape. -/
abbrev Machine := ActualMachine
abbrev Control := ActualControl

def targets (source : Allocation CtfeProvenance Unit) : List AllocId :=
  rowIds (CurrentCallConversionRows.rows source)

/-- Only converter-local allocator resources are carried between selected
payloads. This admits cached function/va-list rows through canonical metadata. -/
def Resources (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (addresses : GlobalAddressState) (ids : List AllocId) (charge : Nat) : Prop :=
  AddressBudget memory addresses ids charge

theorem resources_cached (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (addresses : GlobalAddressState) (ids : List AllocId) (charge : Nat)
    (cached : ∀id∈ids,∃entry,addresses.baseAddr.find? (fun row=>row.allocId==id)=some entry) :
    Resources memory addresses ids charge := Or.inl cached

theorem resources_of_initial (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (addresses : GlobalAddressState) (ids : List AllocId) (charge : Nat)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State memory addresses generation sizes)
    (aligned : NeedsAlignment memory addresses ids→CurrentCallConversionChoiceProtocol.BucketsAligned generation.reusePool)
    (limit : generation.generator.nextBaseAddr.toNat+CurrentCallConversionBudgetPotential.misses addresses ids*charge<2^64)
    (ending : generation.generator.nextBaseAddr.toNat+CurrentCallConversionBudgetPotential.misses addresses ids*charge≤generation.generator.endAddr.toNat) :
    Resources memory addresses ids charge :=
  Or.inr ⟨generation,initial_rows memory addresses generation sizes initial,aligned,limit,ending⟩

/-- A single precise frame for all real relocation callback effects. -/
def state (initial : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) : Machine :=
  conversionMachine initial tracker global addresses tape

theorem targets_eq (source : Allocation CtfeProvenance Unit) :
    targets source=source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId) := by
  simp only [targets,rowIds,CurrentCallConversionRows.rows,List.map_map,Function.comp_def,CurrentCallConversionRows.row]

theorem state_eq (initial : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) :
    state initial tracker global addresses tape=
      {initial with
        borrowTracker:=some {tracker with global:=global}
        user:={initial.user with addresses:=addresses,payload:={initial.user.payload with
          payload:={initial.user.payload.payload with user:={initial.user.payload.payload.user with choices:=tape}}}}} := rfl

theorem state_memory (initial : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) :
    (state initial tracker global addresses tape).memory=initial.memory := rfl

theorem state_tracker (initial : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) :
    (state initial tracker global addresses tape).borrowTracker=some {tracker with global:=global} := rfl

theorem state_addresses (initial : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) :
    (state initial tracker global addresses tape).user.addresses=addresses := rfl

theorem state_tape (initial : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState)
    (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape) :
    Miri.Input.EvalPointerSource.tape.get (state initial tracker global addresses tape)=tape := rfl

/-- The static queried metadata bound is derived from the original declared
numeric reserve, rather than supplied as any callback-success certificate. -/
theorem formation_initial (initial : Machine) (id : AllocId)
    (metadata : CurrentCallOrdinaryInput.RelocationTargetMetadata initial id)
    (uncached : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (info : AllocationInfo) (actual : initial.memory.getAllocInfo id=.ok info) :
    info.kind≠.dead ∧info.align.pow2≤29 ∧
      15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤CurrentCallOrdinaryInput.addressCharge initial :=
  formation_frame initial initial id metadata rfl (fun _ _ hit=>hit) uncached info actual

structure Result (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (hooks : MachineAddress.Hooks MiriMemoryKind Control)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind Control (Pointer Provenance))
    (initial : Machine) (tracker : MachineHooks.BorrowState) (tailIds : List AllocId) (charge reserve : Nat)
    (finalAddresses : GlobalAddressState) (finalTape : ExecutionChoices.Tape) where
  converted : Allocation Provenance Unit
  machine : Machine
  global : GlobalState
  addresses : GlobalAddressState
  tape : ExecutionChoices.Tape
  completed : Allocation.adjustFromTcx source layout (fun _ _ state=>.ok (AllocationCopy.snapshot source) state)
    (PointerSource.globalRootPointer Miri.Input.EvalPointerSource.tape hooks externStatic) initial=.ok converted machine
  frame : machine=state initial tracker global addresses tape
  attributes : GlobalAllocationAttributes.Attributes source converted
  wellFormed : ProvenanceCopy.WellFormed converted.provenanceMap converted.len
  fragments : converted.provenanceMap.byteFragments=none
  protocol : CurrentCallConversionChoiceProtocol.AddressProtocol initial.memory (UInt32.ofNat initial.threads.activeThread.toNat)
    addresses tape tailIds finalAddresses finalTape
  resources : Resources initial.memory addresses tailIds charge
  rootBudget : global.nextPointerTag.value.toNat+(tailIds.filter (fun id=>(global.rootTag? id).isNone)).length+reserve<2^64
  roots : ∀id tag,tracker.global.rootTag? id=some tag→global.rootTag? id=some tag
  bases : ∀id entry,initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some entry→
    addresses.baseAddr.find? (fun row=>row.allocId==id)=some entry
  flags : global.protectedTags=tracker.global.protectedTags
  counter : tracker.global.nextPointerTag.value.toNat≤global.nextPointerTag.value.toNat

  geometry : ∀address base id size,CurrentCallConversionInfoRows.sizes initial.memory id=size→
    WildcardGeneralHitReborrow.Geometry initial.user.addresses.intToPtrMap address base id size→
      WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id size
  addressMode : addresses.addressMode=initial.user.addresses.addressMode
  provenanceMode : addresses.provenanceMode=initial.user.addresses.provenanceMode
  exposed : addresses.exposed=initial.user.addresses.exposed

/-- Actual finite conversion from initial pure choice/allocator/metadata
resources. Every callback and interpreter success is proved internally. -/
theorem invoke (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (hooks : MachineAddress.Hooks MiriMemoryKind Control) (width : hooks.arithmetic=⟨Size.ofBytes 8⟩)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind Control (Pointer Provenance))
    (initial : Machine) (tracker : MachineHooks.BorrowState) (enabled : initial.borrowTracker=some tracker)
    (tailIds : List AllocId) (charge reserve : Nat) (positiveReserve : 0<reserve)
    (finalAddresses : GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol initial.memory (UInt32.ofNat initial.threads.activeThread.toNat)
      initial.user.addresses (Miri.Input.EvalPointerSource.tape.get initial) (targets source++tailIds) finalAddresses finalTape)
    (resources : Resources initial.memory initial.user.addresses (targets source++tailIds) charge)
    (rootBudget : tracker.global.nextPointerTag.value.toNat+((targets source++tailIds).filter (fun id=>(tracker.global.rootTag? id).isNone)).length+reserve<2^64)
    (metadata : ∀id∈targets source,CurrentCallOrdinaryInput.RelocationTargetMetadata initial id)
    (formation : ∀id∈targets source,initial.user.addresses.baseAddr.find? (fun base=>base.allocId==id)=none→
      ∀info,initial.memory.getAllocInfo id=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(alignment info.align).toNat+(GlobalAddressBumpRangeFormation.length info.size).toNat≤charge)
    (race : initial.dataRace=none) (storage : CurrentCallOrdinaryInput.Storage source)
    (format : CurrentCallOrdinaryInput.CompilerFormat source) (layoutWidth : layout.pointerWidth=.w64) :
    Nonempty (Result source layout hooks externStatic initial tracker tailIds charge reserve finalAddresses finalTape) := by
  have member : ∀row∈CurrentCallConversionRows.rows source,row.provenance.allocId∈targets source := by
    intro row present
    exact List.mem_map.mpr ⟨row,present,rfl⟩
  obtain ⟨converted,next,completed,run,attributes,well,fragments⟩:=complete_run source layout hooks width externStatic
    initial tracker enabled tailIds charge reserve positiveReserve finalAddresses finalTape protocol resources rootBudget
    (fun row present=>metadata _ (member row present)) (fun row present=>formation _ (member row present)) race storage format layoutWidth
  obtain ⟨global,addresses,tape,frame,tail,budget,bounded,_,_,bases,roots,flags,counter,geometry,mode,provenance,exposed⟩:=run
  exact ⟨⟨converted,next,global,addresses,tape,completed,frame,attributes,well,fragments,tail,budget,bounded,roots,bases,flags,counter,geometry,mode,provenance,exposed⟩⟩

end DuplicatePrefix.CurrentCallConversionFiniteFold
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionFiniteFold" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved finite converter dependency {dependency} in {name}"
