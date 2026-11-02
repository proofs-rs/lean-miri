import duplicate_prefix.WildcardOrderedHitAddress

namespace DuplicatePrefix.GlobalAddressFreeHistoryFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Coherence against the actual current allocation domain. -/
def LiveRows (state : GlobalAddressState) (live : AllocId → Prop) : Prop :=
  (∀ row ∈ state.intToPtrMap, live row.allocId) ∧ (∀ id ∈ state.exposed, live id)

/-- Even error paths of real free introduce no inverse or exposed entries.
In particular an error is not silently counted as successful deallocation. -/
theorem free_subsets (state : GlobalAddressState) (id : AllocId) (size : Size)
    (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    let next := (state.freeAllocId id size align kind thread reuseChoice clock).state
    (∀ row ∈ next.intToPtrMap, row ∈ state.intToPtrMap) ∧
    (∀ tag ∈ next.exposed, tag ∈ state.exposed) := by
  unfold GlobalAddressState.freeAllocId
  dsimp only
  split
  · try dsimp only
    split
    · exact ⟨fun _ member => member,fun _ member => member⟩
    · split
      · split
        · constructor
          · intro row member;exact Array.mem_of_mem_eraseIdx member
          · intro tag member;exact (Array.mem_filter.mp member).1
        · split
          · constructor
            · intro row member;exact Array.mem_of_mem_eraseIdx member
            · intro tag member;exact (Array.mem_filter.mp member).1
          · split <;> constructor
            all_goals intro entry member
            all_goals first | exact Array.mem_of_mem_eraseIdx member | exact (Array.mem_filter.mp member).1
      · exact ⟨fun _ member => member,fun _ member => member⟩
  · exact ⟨fun _ member => member,fun _ member => member⟩

/-- Real free preserves inverse/exposed liveness for every outcome when the
allocation domain is retained. Removing the freed id from that domain needs
successful structural lookup and uniqueness, and is a separate obligation. -/
theorem free_preserves (state : GlobalAddressState) (live : AllocId → Prop)
    (initial : LiveRows state live) (id : AllocId) (size : Size)
    (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    LiveRows (state.freeAllocId id size align kind thread reuseChoice clock).state live := by
  have subsets := free_subsets state id size align kind thread reuseChoice clock
  exact ⟨fun row member => initial.1 row (subsets.1 row member),
    fun tag member => initial.2 tag (subsets.2 tag member)⟩
/-- Ordered, exact initial address rows force actual free to erase the selected
inverse row and every occurrence of the exposed id, independently of reuse-pool
success. These are lookup/geometry premises, never operation-success premises. -/
theorem free_erases (state : GlobalAddressState) (id : AllocId) (base : UInt64)
    (position : Nat) (valid : position < state.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered state.intToPtrMap)
    (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (cached : state.baseAddr.find? (fun entry => entry.allocId == id) = some ⟨id,base⟩)
    (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    let next := (state.freeAllocId id size align kind thread reuseChoice clock).state
    next.intToPtrMap = state.intToPtrMap.eraseIdx position valid ∧
      next.exposed = state.exposed.filter (fun tag => tag != id) := by
  have search := WildcardOrderedHitAddress.inverse_hit state.intToPtrMap base id position valid ordered row
  have actual : state.intToPtrMap[position] = ⟨base,id⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  unfold GlobalAddressState.freeAllocId
  unfold_internal ".GlobalAddressState.findBase"
  simp only [cached,Option.map_some,search,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    valid,↓reduceDIte,actual,Bool.not_true]
  simp only [bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  split <;> first | exact ⟨rfl,rfl⟩ | (split <;> exact ⟨rfl,rfl⟩)

/-- Actual free preserves coherence against the allocation domain with the freed
id removed. Identifier uniqueness excludes a stale second row for that id.
This covers every reuse-pool outcome; errors remain errors. -/
theorem free_shrinks_live (state : GlobalAddressState) (live : AllocId → Prop)
    (initial : LiveRows state live) (id : AllocId) (base : UInt64)
    (position : Nat) (valid : position < state.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered state.intToPtrMap)
    (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (cached : state.baseAddr.find? (fun entry => entry.allocId == id) = some ⟨id,base⟩)
    (unique : ∀ i (hi : i < state.intToPtrMap.size) j (hj : j < state.intToPtrMap.size),
      state.intToPtrMap[i].allocId = state.intToPtrMap[j].allocId → i = j)
    (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    LiveRows (state.freeAllocId id size align kind thread reuseChoice clock).state
      (fun allocId => live allocId ∧ allocId ≠ id) := by
  have frame := free_erases state id base position valid ordered row cached size align kind thread reuseChoice clock
  have actual : state.intToPtrMap[position] = ⟨base,id⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  constructor
  · intro entry member
    rw [frame.1] at member
    obtain ⟨i,hi,different,equal⟩ := Array.mem_eraseIdx_iff_getElem.mp member
    refine ⟨initial.1 entry (Array.mem_of_mem_eraseIdx member),?_⟩
    intro same
    apply different
    apply unique i hi position valid
    rw [equal,actual]
    exact same
  · intro tag member
    rw [frame.2] at member
    obtain ⟨old,unequal⟩ := Array.mem_filter.mp member
    exact ⟨initial.2 tag old,by simpa only [bne_iff_ne] using unequal⟩

/-- Stack free completes from raw coherent lookup geometry, for any address
reuse configuration and Bernoulli value. Stack ranges bypass reuse insertion. -/
theorem free_stack_completed (state : GlobalAddressState) (id : AllocId) (base : UInt64)
    (position : Nat) (valid : position < state.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered state.intToPtrMap)
    (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (cached : state.baseAddr.find? (fun entry => entry.allocId == id) = some ⟨id,base⟩)
    (size : Size) (align : Align) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    (state.freeAllocId id size align .stack thread reuseChoice clock).outcome = .ok () := by
  have search := WildcardOrderedHitAddress.inverse_hit state.intToPtrMap base id position valid ordered row
  have actual : state.intToPtrMap[position] = ⟨base,id⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  unfold GlobalAddressState.freeAllocId
  unfold_internal ".GlobalAddressState.findBase"
  simp only [cached,Option.map_some,search,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    valid,↓reduceDIte,actual,bne_self_eq_false]
  split
  · simp
  · rfl

end DuplicatePrefix.GlobalAddressFreeHistoryFormation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GlobalAddressFreeHistoryFormation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved free-history dependency {dependency}"
