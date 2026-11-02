import duplicate_prefix.GlobalAddressPhysicalRowHistory
namespace DuplicatePrefix.GlobalAddressBaseCacheFormation
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

def Cached (state : GlobalAddressState) : Prop :=
  ∀ row∈state.intToPtrMap,state.baseAddr.find? (fun base=>base.allocId==row.allocId)=some ⟨row.allocId,row.address⟩

theorem base_insert_other (entries : Array BaseAddressEntry) (id query : AllocId) (address : UInt64)
    (different : query≠id) :
    ((entries.filter (fun row=>row.allocId != id)).push ⟨id,address⟩).find? (fun row=>row.allocId==query)=
      entries.find? (fun row=>row.allocId==query) := by
  rw [Array.find?_push]
  simp only [show (id==query)=false from by simpa using Ne.symm different,Bool.false_eq_true,↓reduceIte,Option.or_none]
  rw [Array.find?_filter]
  congr 1
  funext row
  by_cases same : row.allocId=query
  · simp [same,different]
  · simp [same]

theorem base_insert_same (entries : Array BaseAddressEntry) (id : AllocId) (address : UInt64) :
    ((entries.filter (fun row=>row.allocId != id)).push ⟨id,address⟩).find? (fun row=>row.allocId==id)=some ⟨id,address⟩ := by
  have noMatch : entries.find? (fun _=>false)=none := by simp [Array.find?_eq_none]
  simp [Array.find?_push,Array.find?_filter,noMatch]

theorem cache (state : GlobalAddressState) (id : AllocId) (address : UInt64) (initial : Cached state) :
    Cached (state.cacheAddress id address).state := by
  have old : ∀ row∈state.intToPtrMap, row.allocId≠id →
      ((state.baseAddr.filter (fun row=>row.allocId != id)).push ⟨id,address⟩).find? (fun base=>base.allocId==row.allocId)=some ⟨row.allocId,row.address⟩ := by
    intro row member different
    exact (base_insert_other _ _ _ _ different).trans (initial row member)
  cases found : state.baseAddr.find? (fun row=>row.allocId==id) with
  | some known =>
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [found,Option.map_some]
    exact initial
  | none =>
    have different : ∀ row∈state.intToPtrMap,row.allocId≠id := by
      intro row member same
      have known:=initial row member
      rw [same,found] at known
      cases known
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    unfold_internal ".GlobalAddressState.insertBase"
    simp only [found,Option.map_none]
    split
    · exact fun row member=>old row member (different row member)
    · split
      · split <;> exact fun row member=>old row member (different row member)
      · split
        · rename_i bounded
          change ∀row∈state.intToPtrMap.insertIdx _ ⟨address,id⟩ bounded,
            ((state.baseAddr.filter (fun row=>row.allocId != id)).push ⟨id,address⟩).find? (fun base=>base.allocId==row.allocId)=some ⟨row.allocId,row.address⟩
          intro row member
          rcases Array.mem_insertIdx.mp member with same | prior
          · subst row
            exact base_insert_same _ _ _
          · exact old row prior (different row prior)
        · exact fun row member=>old row member (different row member)

theorem free (state : GlobalAddressState) (id : AllocId) (size : Size) (align : Align)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (choice : Bool) (clock : Unit→VClock)
    (initial : Cached state) : Cached (state.freeAllocId id size align kind thread choice clock).state := by
  have subset:=GlobalAddressFreeHistoryFormation.free_subsets state id size align kind thread choice clock
  have base : (state.freeAllocId id size align kind thread choice clock).state.baseAddr=state.baseAddr := by
    unfold GlobalAddressState.freeAllocId
    dsimp only
    split
    · split
      · rfl
      · split
        · split
          · rfl
          · split
            · rfl
            · split <;> rfl
        · rfl
    · rfl
  intro row member
  rw [base]
  exact initial row (subset.1 row member)

theorem expose (state : GlobalAddressState) (p : Provenance) (live : Option Bool) (tracking : Bool)
    (hook : Option (Except String Unit)) (initial : Cached state) : Cached (state.exposeProvenance p live tracking hook).state := by
  have inverse:=GlobalAddressExposureFormation.expose_inverse state p live tracking hook
  have base : (state.exposeProvenance p live tracking hook).state.baseAddr=state.baseAddr := by
    cases p with
    | wildcard=>rfl
    | concrete id tag =>
      unfold GlobalAddressState.exposeProvenance
      dsimp only
      split
      · rfl
      · cases live with
        | none=>rfl
        | some live=>
          cases live with
          | false=>rfl
          | true=>
            cases tracking with
            | false=>rfl
            | true=>cases hook with
              | none=>rfl
              | some h=>cases h <;>rfl
  intro row member
  rw [base]
  exact initial row (by simpa only [inverse] using member)
theorem returned (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (initial : Cached state) :
    Cached (match (state.cacheAddress id address).outcome with
      | .ok _ => (show AddressStateResult AddressAssignment from ⟨(state.cacheAddress id address).state,.ok (.ready address)⟩)
      | .error error => (show AddressStateResult AddressAssignment from ⟨(state.cacheAddress id address).state,.error error⟩)).state := by
  cases (state.cacheAddress id address).outcome <;> exact cache state id address initial

theorem assign (state : GlobalAddressState) (generation : AddressGenerationState)
    (managed : state.addressMode=.managed) (generationEq : state.generation=some generation)
    (id : AllocId) (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (choices : AddressRandomChoices)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) (initial : Cached state) :
    Cached (state.addrFromAllocId id (some (GlobalAddressAlignedManagedFormation.info size align kind thread)) choices).state := by
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,managed,generationEq,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  cases outcome : (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread).outcome with
  | error error => exact initial
  | ok optional =>
    try dsimp only
    cases optional with
    | some used =>
      try dsimp only
      cases used.clockToAcquire with
      | some clock => exact initial
      | none => exact returned _ id used.address initial
    | none =>
      try dsimp only
      cases generated : (generation.generator.generate size align choices.slack).outcome with
      | error error => exact initial
      | ok address =>
        try dsimp only
        exact returned _ id address initial

theorem complete (pending : AddressStateResult AddressAssignment) (clock : Except String Unit)
    (initial : Cached pending.state) : Cached (GlobalAddressState.completeAcquire pending clock).state := by
  unfold GlobalAddressState.completeAcquire
  cases pending.outcome with
  | error error=>exact initial
  | ok assignment=>
    cases assignment with
    | ready address=>exact initial
    | acquireRequired id address vc=>
      cases clock with
      | error error=>exact initial
      | ok unit=>cases unit;exact returned pending.state id address initial
end DuplicatePrefix.GlobalAddressBaseCacheFormation
