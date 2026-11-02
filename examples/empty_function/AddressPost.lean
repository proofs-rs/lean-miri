import empty_function.RawResources
import empty_function.AddressChoicePlan
import empty_function.ReuseTake
import empty_function.ReuseEnsure
import empty_function.RawAddressCache
import empty_function.InputDraft
namespace EmptyFunction.AddressPost
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

elab "unfold_source_insert_base" : tactic => do
  let found := (←Lean.getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GlobalAddressState.insertBase" then some name else none
  let [name] := found | throwError "expected unique insertBase"
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))

/-- Current sorted addresses determine the actual binary-search cut. -/
theorem ordered_cut (entries : Array InverseAddressEntry) (address : UInt64)
    (ordered : entries.toList.Pairwise (fun l r => l.address < r.address))
    (distinct : ∀ row ∈ entries, row.address ≠ address) :
    ∃ cut, RawAddressCache.Cut entries address cut := by
  let cut := entries.findIdx (fun row => !(row.address < address))
  refine ⟨cut,Array.findIdx_le_size,?_,?_⟩
  · intro i valid before
    have found := Array.not_of_lt_findIdx before
    simpa only [Bool.not_eq_false',decide_eq_true_eq] using found
  · intro i valid after
    have cutValid : cut < entries.size := by omega
    have boundary := @Array.findIdx_getElem _ (fun row => !(row.address < address)) entries cutValid
    have notLess : ¬ entries[cut].address < address := by simpa only [Bool.not_eq_true',decide_eq_false_iff_not] using boundary
    have unequal := distinct entries[cut] (Array.getElem_mem cutValid)
    have greater : address < entries[cut].address := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have ne : entries[cut].address.toNat ≠ address.toNat := fun eq => unequal (UInt64.toNat_inj.mp eq)
      simp only [UInt64.lt_iff_toNat_lt] at notLess
      omega
    by_cases equal : cut = i
    · simpa only [equal] using greater
    · have sorted := ordered.rel_getElem_of_lt (by simpa using cutValid) (by simpa using valid) (by omega)
      change entries[cut].address < entries[i].address at sorted
      apply UInt64.lt_iff_toNat_lt.mpr
      have := UInt64.lt_iff_toNat_lt.mp greater
      have := UInt64.lt_iff_toNat_lt.mp sorted
      omega

/-- Exact successful source insertion, including retained cache entries. -/
theorem cache_at_cut (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (cut : Nat) (geometry : RawAddressCache.Cut state.intToPtrMap address cut)
    (uncached : state.baseAddr.find? (fun row => row.allocId == id) = none)
    (nonzero : address ≠ 0) :
    state.cacheAddress id address =
      ⟨{ state with
          baseAddr := state.baseAddr.push ⟨id,address⟩
          intToPtrMap := state.intToPtrMap.insertIdx cut ⟨address,id⟩ geometry.1 },.ok ()⟩ := by
  have noFilter : state.baseAddr.filter (fun row => row.allocId != id) = state.baseAddr := by
    apply Array.filter_eq_self.mpr
    intro row member
    have fresh := Array.find?_eq_none.mp uncached row member
    simp only [bne, fresh,Bool.not_false]
  have search := RawAddressCache.inverse_cut state.intToPtrMap address cut geometry
  unfold GlobalAddressState.cacheAddress
  unfold_source_base
  unfold_source_insert_base
  simp only [uncached,Option.map_none,noFilter,
    show (address == 0) = false from by simpa using nonzero,
    Bool.false_eq_true,↓reduceIte]
  simp only [RawAddressCache.sourceSearch] at search
  simp only [search,Bool.false_eq_true,↓reduceIte,geometry.1,↓reduceDIte]
  rfl

private theorem pairwise_insert (entries : List InverseAddressEntry)
    (row : InverseAddressEntry) (cut : Nat) (bound : cut ≤ entries.length)
    (ordered : entries.Pairwise (fun l r => l.address < r.address))
    (lower : ∀ i (valid : i < entries.length), i < cut → entries[i].address < row.address)
    (upper : ∀ i (valid : i < entries.length), cut ≤ i → row.address < entries[i].address) :
    (entries.insertIdx cut row).Pairwise (fun l r => l.address < r.address) := by
  induction entries generalizing cut with
  | nil =>
    have : cut = 0 := by simpa using bound
    subst cut
    simp
  | cons head tail ih =>
    cases cut with
    | zero =>
      change (row :: head :: tail).Pairwise _
      apply List.Pairwise.cons
      · intro other member
        obtain ⟨i,valid,equal⟩ := List.getElem_of_mem member
        subst other
        exact upper i valid (Nat.zero_le _)
      · exact ordered

    | succ cut =>
      simp only [List.insertIdx_succ_cons,List.pairwise_cons]
      refine ⟨?_,ih cut (by simpa using bound) ordered.of_cons ?_ ?_⟩
      · intro other member
        rcases (List.mem_insertIdx (by simpa using bound)).mp member with equal | prior
        · subst other; exact lower 0 (by simp) (by omega)
        · exact (List.pairwise_cons.mp ordered).1 other prior
      · intro i valid below
        exact lower (i+1) (by simpa using valid) (by omega)
      · intro i valid above
        exact upper (i+1) (by simpa using valid) (by omega)

private theorem nodup_ids_insert (entries : List InverseAddressEntry)
    (row : InverseAddressEntry) (cut : Nat) (bound : cut ≤ entries.length)
    (unique : (entries.map (·.allocId)).Nodup)
    (fresh : ∀ old ∈ entries, old.allocId ≠ row.allocId) :
    ((entries.insertIdx cut row).map (·.allocId)).Nodup := by
  induction entries generalizing cut with
  | nil =>
    have : cut = 0 := by simpa using bound
    subst cut
    simp
  | cons head tail ih =>
    have prior := List.nodup_cons.mp unique
    cases cut with
    | zero =>
      change (row.allocId :: (head :: tail).map (·.allocId)).Nodup
      apply List.nodup_cons.mpr
      refine ⟨?_,unique⟩
      intro member
      obtain ⟨old,member,equal⟩ := List.mem_map.mp member
      exact fresh old member equal
    | succ cut =>
      simp only [List.insertIdx_succ_cons,List.map_cons,List.nodup_cons]
      refine ⟨?_,ih cut (by simpa using bound) prior.2 (fun old member => fresh old (by simp [member]))⟩
      intro member
      obtain ⟨old,member,equal⟩ := List.mem_map.mp member
      rcases (List.mem_insertIdx (by simpa using bound)).mp member with same | oldMember
      · subst old; exact fresh head (by simp) equal.symm
      · exact prior.1 (List.mem_map.mpr ⟨old,oldMember,equal⟩)

def withAddresses (before : WholeCall.State) (addresses : GlobalAddressState) : WholeCall.State :=
  { before with machine := { before.machine with user := { before.machine.user with addresses } } }

private theorem backing_withAddresses (before : WholeCall.State) (addresses : GlobalAddressState)
    (id : AllocId) (backing : InputDraft.MetadataBacking before id) :
    InputDraft.MetadataBacking (withAddresses before addresses) id := by
  cases backing with
  | live entry row => exact .live entry row
  | global entry row identity => exact .global entry row identity
  | extraFunction row => exact .extraFunction row
  | vaList row => exact .vaList row
  | dead entry row => exact .dead entry row

/-- Freshness of the base key implies freshness in the coherent live index. -/
theorem inverse_fresh (before : WholeCall.State) (tables : InputDraft.AddressTables before)
    (id : AllocId)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none) :
    ∀ row ∈ before.machine.user.addresses.intToPtrMap, row.allocId ≠ id := by
  intro row member equal
  have cached := tables.bases row member
  rw [equal,uncached] at cached
  contradiction

/-- Every current address-table field is preserved by actual nonzero source
cache insertion. Extent disjointness and backing/liveness describe current
metadata and the candidate range; no operation-success premise is used. -/
theorem cache_tables (before : WholeCall.State) (tables : InputDraft.AddressTables before)
    (id : AllocId) (address : UInt64)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (nonzero : address ≠ 0)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (distinct : ∀ row ∈ before.machine.user.addresses.intToPtrMap, row.address ≠ address)
    (separated : ∀ row ∈ before.machine.user.addresses.intToPtrMap,
      ∀ oldInfo newInfo,
      before.machine.memory.getAllocInfo row.allocId = .ok oldInfo →
      before.machine.memory.getAllocInfo id = .ok newInfo →
      row.address.toNat + max oldInfo.size.bytes.toNat 1 ≤ address.toNat ∨
        address.toNat + max newInfo.size.bytes.toNat 1 ≤ row.address.toNat) :
    InputDraft.AddressTables
      (withAddresses before (before.machine.user.addresses.cacheAddress id address).state) := by
  obtain ⟨cut,geometry⟩ := ordered_cut before.machine.user.addresses.intToPtrMap address tables.ordered distinct
  rw [cache_at_cut _ id address cut geometry uncached nonzero]
  let addresses := before.machine.user.addresses
  let inserted := addresses.intToPtrMap.insertIdx cut (⟨address,id⟩ : InverseAddressEntry) geometry.1
  let after := withAddresses before { addresses with
    baseAddr := addresses.baseAddr.push ⟨id,address⟩
    intToPtrMap := inserted }
  change InputDraft.AddressTables after
  have fresh := inverse_fresh before tables id uncached
  have newBase : (addresses.baseAddr.push ⟨id,address⟩).find? (fun row => row.allocId == id) =
      some ⟨id,address⟩ := by simp [Array.find?_push,addresses,uncached]
  have oldBase : ∀ row ∈ addresses.intToPtrMap,
      (addresses.baseAddr.push ⟨id,address⟩).find? (fun entry => entry.allocId == row.allocId) =
        some ⟨row.allocId,row.address⟩ := by
    intro row member
    simp only [addresses,Array.find?_push,tables.bases row member,Option.or]
  have members : ∀ row, row ∈ inserted ↔ row = ⟨address,id⟩ ∨ row ∈ addresses.intToPtrMap :=
    fun _ => Array.mem_insertIdx
  constructor
  · change ((addresses.baseAddr.push ⟨id,address⟩).toList.map (·.allocId)).Nodup
    simp only [Array.toList_push,List.map_append,List.map_cons,List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨tables.baseIds,by simp,?_⟩
    intro old member new newMember
    have newEq : new = id := by simpa using newMember
    subst new
    obtain ⟨row,member,equal⟩ := List.mem_map.mp member
    intro same
    have absent := Array.find?_eq_none.mp uncached row (by simpa using member)
    exact absent (by simp only [equal,same,beq_self_eq_true])
  · change (inserted.toList.map (·.allocId)).Nodup
    rw [Array.toList_insertIdx]
    exact nodup_ids_insert _ _ cut (by simpa using geometry.1) tables.inverseIds
      (fun row member => fresh row (by simpa using member))
  · intro row member
    change row ∈ inserted at member
    rcases (members row).mp member with equal | prior
    · subst row; exact backing_withAddresses before _ id backing
    · exact backing_withAddresses before _ row.allocId (tables.suppliers row prior)
  · intro row member
    change row ∈ inserted at member
    rcases (members row).mp member with equal | prior
    · subst row; exact live
    · exact tables.inverseLive row prior
  · intro row member
    change row ∈ inserted at member
    rcases (members row).mp member with equal | prior
    · subst row; exact nonzero
    · exact tables.nonzero row prior
  · intro row member
    change row ∈ inserted at member
    change (addresses.baseAddr.push ⟨id,address⟩).find? _ = _
    rcases (members row).mp member with equal | prior
    · subst row; exact newBase
    · exact oldBase row prior
  · intro row member rowLive rowNonzero
    change row ∈ addresses.baseAddr.push ⟨id,address⟩ at member
    change ∃ inverse ∈ inserted, inverse.allocId = row.allocId ∧ inverse.address = row.address
    rcases Array.mem_push.mp member with prior | equal
    · obtain ⟨inverse,stored,sameId,sameBase⟩ := tables.liveBases row prior rowLive rowNonzero
      exact ⟨inverse,(members inverse).mpr (Or.inr stored),sameId,sameBase⟩
    · subst row
      exact ⟨⟨address,id⟩,(members _).mpr (Or.inl rfl),rfl,rfl⟩
  · change inserted.toList.Pairwise _
    rw [Array.toList_insertIdx]
    apply pairwise_insert _ _ cut (by simpa using geometry.1) tables.ordered
    · intro i valid earlier
      exact geometry.2.1 i (by simpa using valid) earlier
    · intro i valid later
      exact geometry.2.2 i (by simpa using valid) later
  · intro left leftMember right rightMember different leftInfo rightInfo leftQuery rightQuery
    change left ∈ inserted at leftMember
    change right ∈ inserted at rightMember
    rcases (members left).mp leftMember with leftEq | leftOld <;>
      rcases (members right).mp rightMember with rightEq | rightOld
    · subst left; subst right; exact False.elim (different rfl)
    · subst left
      exact (separated right rightOld rightInfo leftInfo rightQuery leftQuery).symm
    · subst right
      exact separated left leftOld leftInfo rightInfo leftQuery rightQuery
    · exact tables.separated left leftOld right rightOld different leftInfo rightInfo leftQuery rightQuery
  · exact tables.exposedLive
  · intro exposed member
    obtain ⟨base,present⟩ := tables.exposedBases exposed member
    refine ⟨base,?_⟩
    change (addresses.baseAddr.push ⟨id,address⟩).find? _ = _
    simp only [addresses,Array.find?_push,present,Option.or]

/-- The source erase/set removes exactly one entry from the flattened pool,
regardless of the chosen alignment bucket or its preceding bucket lengths. -/
private theorem flatten_erase (buckets : List (Array ReusableAddress))
    (index : Nat) (valid : index < buckets.length)
    (selection : Nat) (selected : selection < buckets[index].size) :
    ∃ (offset : Nat) (bounded : offset < (buckets.flatMap Array.toList).length),
      (buckets.flatMap Array.toList)[offset] = buckets[index][selection] ∧
      ((buckets.set index (buckets[index].eraseIdx selection selected)).flatMap Array.toList) =
        (buckets.flatMap Array.toList).eraseIdx offset := by
  induction buckets generalizing index with
  | nil => simp at valid
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem_cons_zero] at selected ⊢
      refine ⟨selection,by simp only [List.flatMap_cons,List.length_append,Array.length_toList]; omega,?_,?_⟩
      · simp only [List.flatMap_cons]
        rw [List.getElem_append_left (by simpa using selected)]
        rfl
      · simp only [List.set_cons_zero,List.flatMap_cons,Array.toList_eraseIdx]
        exact (List.eraseIdx_append_of_lt_length (by simpa using selected) _).symm
    | succ index =>
      simp only [List.getElem_cons_succ] at selected ⊢
      obtain ⟨offset,bounded,lookup,shape⟩ := ih index (by simpa using valid) selected
      refine ⟨head.size+offset,by simp only [List.flatMap_cons,List.length_append,Array.length_toList]; omega,?_,?_⟩
      · simp only [List.flatMap_cons]
        rw [List.getElem_append_right (by simp)]
        simpa only [Array.length_toList,Nat.add_sub_cancel_left] using lookup
      · simp only [List.set_cons_succ,List.flatMap_cons]
        rw [shape,List.eraseIdx_append_of_length_le (by simp)]
        simp

/-- Pure geometry exposed by the actual pool removal. Remaining holes retain
order and uniqueness; the removed hole is absent and separated from each one. -/
theorem remaining_pool (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (index : Nat) (valid : index < generation.reusePool.pool.size)
    (selection : Nat) (selected : selection < generation.reusePool.pool[index].size) :
    let buckets := generation.reusePool.pool
    let row := buckets[index][selection]
    let remaining := buckets.set index (buckets[index].eraseIdx selection selected) valid
    (remaining.toList.flatMap Array.toList).Sublist (buckets.toList.flatMap Array.toList) ∧
    ((remaining.toList.flatMap Array.toList).map (·.address)).Nodup ∧
    (remaining.toList.flatMap Array.toList).Pairwise (fun l r =>
      l.address.toNat + max l.size.bytes.toNat 1 ≤ r.address.toNat ∨
        r.address.toNat + max r.size.bytes.toNat 1 ≤ l.address.toNat) ∧
    (∀ other ∈ remaining.toList.flatMap Array.toList, other.address ≠ row.address) ∧
    (∀ other ∈ remaining.toList.flatMap Array.toList,
      other.address.toNat + max other.size.bytes.toNat 1 ≤ row.address.toNat ∨
        row.address.toNat + max row.size.bytes.toNat 1 ≤ other.address.toNat) := by
  dsimp only
  obtain ⟨offset,bounded,lookup,shape⟩ := flatten_erase generation.reusePool.pool.toList index
    (by simpa using valid) selection selected
  simp only [Array.toList_set,Array.getElem_toList] at *
  rw [shape]
  have sub := List.eraseIdx_sublist (generation.reusePool.pool.toList.flatMap Array.toList) offset
  refine ⟨sub,List.Pairwise.sublist (sub.map (·.address)) representation.poolUnique,
    List.Pairwise.sublist sub representation.poolSeparatedPairwise,?_,?_⟩
  · intro other member equal
    obtain ⟨i,validI,different,atI⟩ := List.mem_eraseIdx_iff_getElem.mp member
    have same : i = offset := representation.poolUnique.eq_of_getElem_eq
      (by simpa using validI) (by simpa using bounded) (by simp only [List.getElem_map,atI,lookup]; exact equal)
    exact different same
  · intro other member
    obtain ⟨i,validI,different,atI⟩ := List.mem_eraseIdx_iff_getElem.mp member
    by_cases before : i < offset
    · have separated := representation.poolSeparatedPairwise.rel_getElem_of_lt validI bounded before
      simpa only [atI,lookup] using separated
    · have separated := representation.poolSeparatedPairwise.rel_getElem_of_lt bounded validI (by omega)
      simpa only [atI,lookup] using separated.symm

theorem take_bucket_exact (pool : ReusePool) (bucket : Array ReusableAddress)
    (size : Size) (align : Align) (bytes : UInt64) (thread : AddressThreadId)
    (cross : Bool) (selection : Nat)
    (present : pool.pool[align.pow2]? = some bucket)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true)
    (lower : (ReuseCandidate.candidate bucket size thread cross).1 ≤ selection)
    (upper : selection < (ReuseCandidate.candidate bucket size thread cross).2)
    (aligned : ∀ row ∈ bucket, row.address % bytes = 0) :
    ∃ (valid : selection < bucket.size),
      pool.takeAddr true cross selection size align .other thread =
        ⟨{ pool with pool := (pool.pool.set align.pow2 (bucket.eraseIdx selection valid)
          (Array.getElem?_eq_some_iff.mp present).1) },
          .ok (some ⟨bucket[selection].address,
            if bucket[selection].thread == thread then none else some bucket[selection].clock⟩)⟩ ∧
      bucket[selection].size.bytes = size.bytes := by
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
  refine ⟨valid,?_,sizeMatch⟩
  unfold ReusePool.takeAddr
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,
    ReuseTake.checked_alignment align bytes metadata normalized,bind,pure,
    ReuseTake.ensure_present pool align.pow2 bounded]
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

private theorem tables_generation (before : WholeCall.State) (tables : InputDraft.AddressTables before)
    (generation : AddressGenerationState) :
    InputDraft.AddressTables (withAddresses before {before.machine.user.addresses with generation := some generation}) := by
  constructor
  · exact tables.baseIds
  · exact tables.inverseIds
  · intro row member
    exact backing_withAddresses before _ row.allocId (tables.suppliers row member)
  · exact tables.inverseLive
  · exact tables.nonzero
  · exact tables.bases
  · exact tables.liveBases
  · exact tables.ordered
  · exact tables.separated
  · exact tables.exposedLive
  · exact tables.exposedBases

/-- Representation survives the exact source pool erase/set transition.
This prefix changes generation only; insertion of the selected address into
live tables is handled separately by cache_representation. -/
theorem erase_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (index : Nat) (valid : index < generation.reusePool.pool.size)
    (selection : Nat) (selected : selection < generation.reusePool.pool[index].size) :
    let remaining := generation.reusePool.pool.set index
      (generation.reusePool.pool[index].eraseIdx selection selected) valid
    let next := {generation with reusePool := {generation.reusePool with pool := remaining}}
    InputDraft.GenerationRepresentation
      (withAddresses before {before.machine.user.addresses with generation := some next}) next := by
  dsimp only
  let buckets := generation.reusePool.pool
  let remaining := buckets.set index (buckets[index].eraseIdx selection selected) valid
  let next := {generation with reusePool := {generation.reusePool with pool := remaining}}
  change InputDraft.GenerationRepresentation (withAddresses before {before.machine.user.addresses with generation := some next}) next
  have geometry := remaining_pool before generation representation index valid selection selected
  have original : ∀ bucket ∈ remaining, ∀ row ∈ bucket,
      ∃ old ∈ buckets, row ∈ old := by
    intro bucket member row stored
    have flat : row ∈ remaining.toList.flatMap Array.toList :=
      List.mem_flatMap.mpr ⟨bucket,by simpa using member,by simpa using stored⟩
    have prior := geometry.1.subset flat
    obtain ⟨old,member,stored⟩ := List.mem_flatMap.mp prior
    exact ⟨old,by simpa using member,by simpa using stored⟩
  constructor
  · rfl
  · exact representation.managed
  · exact tables_generation before representation.tables next
  · exact representation.reuseRateLower
  · exact representation.reuseRateUpper
  · exact representation.crossRateLower
  · exact representation.crossRateUpper
  · intro bucket member
    change bucket ∈ remaining at member
    rcases Array.mem_or_eq_of_mem_set member with prior | equal
    · exact representation.poolKeys bucket prior
    · subst bucket
      simp only [Array.toList_eraseIdx]
      exact List.Pairwise.eraseIdx selection (representation.poolKeys buckets[index] (Array.getElem_mem valid))
  · intro bucket member
    change bucket ∈ remaining at member
    rcases Array.mem_or_eq_of_mem_set member with prior | equal
    · exact representation.poolSize bucket prior
    · subst bucket
      have bound := representation.poolSize buckets[index] (Array.getElem_mem valid)
      simp only [Array.size_eraseIdx]
      omega
  · intro bucket member row stored
    obtain ⟨old,member,stored⟩ := original bucket member row stored
    exact representation.poolAddresses old member row stored
  · intro i bounded row stored
    change i < remaining.size at bounded
    change row ∈ remaining[i] at stored
    by_cases equal : index = i
    · subst i
      simp only [remaining,Array.getElem_set_self] at stored
      exact representation.poolAlignment index valid row (Array.mem_of_mem_eraseIdx stored)
    · simp only [remaining,buckets,Array.getElem_set_ne valid (by simpa only [remaining,Array.size_set] using bounded) equal] at stored
      exact representation.poolAlignment i (by simpa only [remaining,Array.size_set] using bounded) row stored
  · exact geometry.2.1
  · exact geometry.2.2.1
  · intro bucket member row stored inverse indexed
    obtain ⟨old,member,stored⟩ := original bucket member row stored
    exact representation.poolAbsent old member row stored inverse indexed
  · intro bucket member row stored inverse indexed info query
    obtain ⟨old,member,stored⟩ := original bucket member row stored
    exact representation.poolSeparated old member row stored inverse indexed info query
  · exact representation.allocatedBeforeCursor

/-- The remaining generation representation after actual source cacheAddress.
Only raw physical range facts for the newly live row are needed. -/
theorem cache_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (address : UInt64)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (nonzero : address ≠ 0) (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (distinct : ∀ row ∈ before.machine.user.addresses.intToPtrMap, row.address ≠ address)
    (separated : ∀ row ∈ before.machine.user.addresses.intToPtrMap,
      ∀ oldInfo newInfo,
      before.machine.memory.getAllocInfo row.allocId = .ok oldInfo →
      before.machine.memory.getAllocInfo id = .ok newInfo →
      row.address.toNat + max oldInfo.size.bytes.toNat 1 ≤ address.toNat ∨
        address.toNat + max newInfo.size.bytes.toNat 1 ≤ row.address.toNat)
    (poolAbsent : ∀ bucket ∈ generation.reusePool.pool, ∀ row ∈ bucket, row.address ≠ address)
    (poolSeparated : ∀ bucket ∈ generation.reusePool.pool, ∀ row ∈ bucket, ∀ info,
      before.machine.memory.getAllocInfo id = .ok info →
      row.address.toNat + max row.size.bytes.toNat 1 ≤ address.toNat ∨
        address.toNat + max info.size.bytes.toNat 1 ≤ row.address.toNat)
    (cursor : ∀ info, before.machine.memory.getAllocInfo id = .ok info →
      address.toNat + max info.size.bytes.toNat 1 ≤ generation.generator.nextBaseAddr.toNat) :
    InputDraft.GenerationRepresentation
      (withAddresses before (before.machine.user.addresses.cacheAddress id address).state) generation := by
  have postTables := cache_tables before representation.tables id address uncached nonzero backing live distinct separated
  obtain ⟨cut,geometry⟩ := ordered_cut before.machine.user.addresses.intToPtrMap address representation.tables.ordered distinct
  rw [cache_at_cut _ id address cut geometry uncached nonzero] at postTables ⊢
  let addresses := before.machine.user.addresses
  let inserted := addresses.intToPtrMap.insertIdx cut (⟨address,id⟩ : InverseAddressEntry) geometry.1
  let after := withAddresses before {addresses with
    baseAddr := addresses.baseAddr.push ⟨id,address⟩
    intToPtrMap := inserted}
  change InputDraft.GenerationRepresentation after generation
  have members : ∀ row, row ∈ inserted ↔ row = ⟨address,id⟩ ∨ row ∈ addresses.intToPtrMap :=
    fun _ => Array.mem_insertIdx
  constructor
  · exact representation.current
  · exact representation.managed
  · exact postTables
  · exact representation.reuseRateLower
  · exact representation.reuseRateUpper
  · exact representation.crossRateLower
  · exact representation.crossRateUpper
  · exact representation.poolKeys
  · exact representation.poolSize
  · exact representation.poolAddresses
  · exact representation.poolAlignment
  · exact representation.poolUnique
  · exact representation.poolSeparatedPairwise
  · intro bucket member row stored inverse indexed
    change inverse ∈ inserted at indexed
    rcases (members inverse).mp indexed with equal | prior
    · subst inverse; exact poolAbsent bucket member row stored
    · exact representation.poolAbsent bucket member row stored inverse prior
  · intro bucket member row stored inverse indexed info query
    change inverse ∈ inserted at indexed
    rcases (members inverse).mp indexed with equal | prior
    · subst inverse; exact poolSeparated bucket member row stored info query
    · exact representation.poolSeparated bucket member row stored inverse prior info query
  · intro row member info query
    change row ∈ inserted at member
    rcases (members row).mp member with equal | prior
    · subst row; exact cursor info query
    · exact representation.allocatedBeforeCursor row prior info query

/-- Every supported reuse choice preserves the complete current address and
generation representation through the actual assign/acquire/cache algorithm. -/
theorem reuse_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (thread : AddressThreadId)
    (bucket : Array ReusableAddress) (bytes : UInt64) (cross : Bool) (selection : Nat) (slack : Fin 16)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (present : generation.reusePool.pool[target.align.pow2]? = some bucket)
    (alignment : Align.bytes target.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok target.align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross = true)
    (lower : (ReuseCandidate.candidate bucket target.size thread cross).1 ≤ selection)
    (upper : selection < (ReuseCandidate.candidate bucket target.size thread cross).2)
    (aligned : ∀ row ∈ bucket, row.address % bytes = 0) :
    ∃ (after : GlobalAddressState) (next : AddressGenerationState),
      AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
        (some ⟨.liveData,true,target.size,target.align,some .other,thread⟩)
        ⟨true,cross,selection,slack⟩) = .ok after ∧
      InputDraft.GenerationRepresentation (withAddresses before after) next := by
  obtain ⟨valid,taken,sizeMatch⟩ := take_bucket_exact generation.reusePool bucket target.size target.align
    bytes thread cross selection present alignment normalized reuseAllowed crossAllowed lower upper aligned
  obtain ⟨bounded,bucketEq⟩ := Array.getElem?_eq_some_iff.mp present
  let row := bucket[selection]
  let pool : ReusePool := {generation.reusePool with pool :=
      (generation.reusePool.pool.set target.align.pow2 (bucket.eraseIdx selection valid) bounded)}
  let next := {generation with reusePool := pool}
  let stageAddr := {before.machine.user.addresses with generation := some next}
  let stage := withAddresses before stageAddr
  have stageRep : InputDraft.GenerationRepresentation stage next := by
    have result := erase_representation before generation representation target.align.pow2 bounded
      selection (by simpa only [bucketEq] using valid)
    simpa only [bucketEq] using result
  have selectedMember : row ∈ bucket := Array.getElem_mem valid
  have bucketMember : bucket ∈ generation.reusePool.pool := Array.mem_of_getElem? present
  have physical := representation.poolAddresses bucket bucketMember row selectedMember
  have newNonzero : row.address ≠ 0 := physical.1
  have oldDistinct : ∀ inverse ∈ before.machine.user.addresses.intToPtrMap, inverse.address ≠ row.address := by
    intro inverse member
    exact (representation.poolAbsent bucket bucketMember row selectedMember inverse member).symm
  have geometry := remaining_pool before generation representation target.align.pow2 bounded selection
    (by simpa only [bucketEq] using valid)
  simp only [bucketEq] at geometry
  have postRep : InputDraft.GenerationRepresentation
      (withAddresses stage (stageAddr.cacheAddress id row.address).state) next := by
    apply cache_representation stage next stageRep id row.address uncached newNonzero
      (backing_withAddresses before stageAddr id backing) live oldDistinct
    · intro inverse member oldInfo newInfo oldQuery newQuery
      have same : newInfo = target := by
        change before.machine.memory.getAllocInfo id = .ok newInfo at newQuery
        rw [metadata] at newQuery
        exact (Except.ok.inj newQuery).symm
      subst newInfo
      have result := representation.poolSeparated bucket bucketMember row selectedMember inverse member oldInfo oldQuery
      simpa only [row,sizeMatch] using result.symm
    · intro remaining member hole stored
      apply geometry.2.2.2.1 hole
      exact List.mem_flatMap.mpr ⟨remaining,by simpa only [next,pool,Array.mem_def,Array.toList_set] using member,by simpa using stored⟩
    · intro remaining member hole stored info query
      have same : info = target := by
        change before.machine.memory.getAllocInfo id = .ok info at query
        rw [metadata] at query
        exact (Except.ok.inj query).symm
      subst info
      have result := geometry.2.2.2.2 hole
        (List.mem_flatMap.mpr ⟨remaining,by simpa only [next,pool,Array.mem_def,Array.toList_set] using member,by simpa using stored⟩)
      simpa only [row,sizeMatch] using result
    · intro info query
      have same : info = target := by
        change before.machine.memory.getAllocInfo id = .ok info at query
        rw [metadata] at query
        exact (Except.ok.inj query).symm
      subst info
      simpa only [next,row,sizeMatch] using physical.2
  have cached : (stageAddr.cacheAddress id row.address).outcome = .ok () :=
    RawAddressCache.cache_fresh stageAddr id row.address uncached oldDistinct
  refine ⟨(stageAddr.cacheAddress id row.address).state,next,?_,postRep⟩
  unfold GlobalAddressState.addrFromAllocId
  unfold_source_base
  unfold_source_generation
  simp only [uncached,Option.map_none,representation.managed,representation.current,
    beq_iff_eq,reduceCtorEq,Bool.not_true,↓reduceIte,Id.run,pure,taken,
    show (AllocationAddressKind.liveData == AllocationAddressKind.dead) = false from rfl,Bool.false_or]
  simp only [← representation.managed]
  change AddressChoicePlan.assignedState
    (match (if row.thread = thread then none else some row.clock) with
    | some clock => ⟨stageAddr,.ok (.acquireRequired id row.address clock)⟩
    | none => match (stageAddr.cacheAddress id row.address).outcome with
      | .ok _ => ⟨(stageAddr.cacheAddress id row.address).state,.ok (.ready row.address)⟩
      | .error error => ⟨(stageAddr.cacheAddress id row.address).state,.error error⟩) = _
  cases clock : (if row.thread = thread then none else some row.clock) <;>
    simp only [AddressChoicePlan.assignedState,cached]

private theorem flatten_append_empty (buckets : Array (Array ReusableAddress)) (count : Nat) :
    ((buckets ++ Array.replicate count #[]).toList.flatMap Array.toList) =
      buckets.toList.flatMap Array.toList := by
  induction count with
  | zero => simp
  | succ count ih => simpa only [Array.replicate_succ,Array.append_push,Array.toList_push,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,Array.toList_empty,List.append_nil] using ih

/-- Appending the source's missing empty buckets preserves every pool and
current-table representation field, including the bucket-index alignment law. -/
theorem append_empty_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation) (count : Nat) :
    let pool := {generation.reusePool with pool := generation.reusePool.pool ++ Array.replicate count #[]}
    let next := {generation with reusePool := pool}
    InputDraft.GenerationRepresentation
      (withAddresses before {before.machine.user.addresses with generation := some next}) next := by
  dsimp only
  let buckets := generation.reusePool.pool
  let expanded := buckets ++ Array.replicate count (#[] : Array ReusableAddress)
  let next := {generation with reusePool := {generation.reusePool with pool := expanded}}
  change InputDraft.GenerationRepresentation (withAddresses before {before.machine.user.addresses with generation := some next}) next
  have original : ∀ bucket ∈ expanded, ∀ row ∈ bucket, bucket ∈ buckets := by
    intro bucket member row stored
    rcases Array.mem_append.mp member with prior | added
    · exact prior
    · have equal : bucket = #[] := (Array.mem_replicate.mp added).2
      subst bucket
      simp at stored
  constructor
  · rfl
  · exact representation.managed
  · exact tables_generation before representation.tables next
  · exact representation.reuseRateLower
  · exact representation.reuseRateUpper
  · exact representation.crossRateLower
  · exact representation.crossRateUpper
  · intro bucket member
    rcases Array.mem_append.mp member with prior | added
    · exact representation.poolKeys bucket prior
    · have equal : bucket = #[] := (Array.mem_replicate.mp added).2
      subst bucket
      simp
  · intro bucket member
    rcases Array.mem_append.mp member with prior | added
    · exact representation.poolSize bucket prior
    · have equal : bucket = #[] := (Array.mem_replicate.mp added).2
      subst bucket
      simp [maxReusePoolSize]
  · intro bucket member row stored
    exact representation.poolAddresses bucket (original bucket member row stored) row stored
  · intro i bounded row stored
    change i < expanded.size at bounded
    change row ∈ expanded[i] at stored
    by_cases old : i < buckets.size
    · simp only [expanded,Array.getElem_append_left old] at stored
      exact representation.poolAlignment i old row stored
    · have empty : expanded[i] = #[] := by
        simp only [expanded,Array.getElem_append_right (i := i) (xs := buckets) (ys := Array.replicate count (#[] : Array ReusableAddress)) (by omega)]
        simp
      rw [empty] at stored
      simp at stored
  · change ((expanded.toList.flatMap Array.toList).map (·.address)).Nodup
    rw [flatten_append_empty]
    exact representation.poolUnique
  · change (expanded.toList.flatMap Array.toList).Pairwise _
    rw [flatten_append_empty]
    exact representation.poolSeparatedPairwise
  · intro bucket member row stored inverse indexed
    exact representation.poolAbsent bucket (original bucket member row stored) row stored inverse indexed
  · intro bucket member row stored inverse indexed info query
    exact representation.poolSeparated bucket (original bucket member row stored) row stored inverse indexed info query
  · exact representation.allocatedBeforeCursor

/-- Representation follows the actual ensureSubpool prefix for every current
pool length; no nonempty or preallocated-bucket restriction is imposed. -/
theorem ensure_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation) (index : Nat) :
    let next := {generation with reusePool := (reuse_actual ".ReusePool.ensureSubpool") generation.reusePool index}
    InputDraft.GenerationRepresentation
      (withAddresses before {before.machine.user.addresses with generation := some next}) next := by
  dsimp only
  by_cases present : index < generation.reusePool.pool.size
  · rw [ReuseTake.ensure_present _ index present]
    constructor
    · rfl
    · exact representation.managed
    · exact tables_generation before representation.tables generation
    · exact representation.reuseRateLower
    · exact representation.reuseRateUpper
    · exact representation.crossRateLower
    · exact representation.crossRateUpper
    · exact representation.poolKeys
    · exact representation.poolSize
    · exact representation.poolAddresses
    · exact representation.poolAlignment
    · exact representation.poolUnique
    · exact representation.poolSeparatedPairwise
    · exact representation.poolAbsent
    · exact representation.poolSeparated
    · exact representation.allocatedBeforeCursor
  · rw [ReuseEnsure.absent _ index (by omega)]
    exact append_empty_representation before generation representation _

/-- Advancing the source generator frontier retains all earlier extents. -/
theorem advance_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (generator : AddressGenerator)
    (advanced : generation.generator.nextBaseAddr.toNat ≤ generator.nextBaseAddr.toNat) :
    let next := {generation with generator}
    InputDraft.GenerationRepresentation
      (withAddresses before {before.machine.user.addresses with generation := some next}) next := by
  dsimp only
  constructor
  · rfl
  · exact representation.managed
  · exact tables_generation before representation.tables _
  · exact representation.reuseRateLower
  · exact representation.reuseRateUpper
  · exact representation.crossRateLower
  · exact representation.crossRateUpper
  · exact representation.poolKeys
  · exact representation.poolSize
  · intro bucket member row stored
    obtain ⟨nonzero,prior⟩ := representation.poolAddresses bucket member row stored
    exact ⟨nonzero,Nat.le_trans prior advanced⟩
  · exact representation.poolAlignment
  · exact representation.poolUnique
  · exact representation.poolSeparatedPairwise
  · exact representation.poolAbsent
  · exact representation.poolSeparated
  · intro row member info query
    exact Nat.le_trans (representation.allocatedBeforeCursor row member info query) advanced

/-- The actual shortage transition either keeps the pool rates or sets the
reuse rate to its supported endpoint 1; pool geometry is unchanged. -/
theorem shortage_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation) :
    let next := {generation with reusePool := generation.reusePool.addressSpaceShortage}
    InputDraft.GenerationRepresentation
      (withAddresses before {before.machine.user.addresses with generation := some next}) next := by
  dsimp only
  unfold ReusePool.addressSpaceShortage
  split
  · constructor
    · rfl
    · exact representation.managed
    · exact tables_generation before representation.tables _
    · change Float.le 0.0 1.0 = true
      decide
    · change Float.le 1.0 1.0 = true
      decide
    · exact representation.crossRateLower
    · exact representation.crossRateUpper
    · exact representation.poolKeys
    · exact representation.poolSize
    · exact representation.poolAddresses
    · exact representation.poolAlignment
    · exact representation.poolUnique
    · exact representation.poolSeparatedPairwise
    · exact representation.poolAbsent
    · exact representation.poolSeparated
    · exact representation.allocatedBeforeCursor
  · constructor
    · rfl
    · exact representation.managed
    · exact tables_generation before representation.tables _
    · exact representation.reuseRateLower
    · exact representation.reuseRateUpper
    · exact representation.crossRateLower
    · exact representation.crossRateUpper
    · exact representation.poolKeys
    · exact representation.poolSize
    · exact representation.poolAddresses
    · exact representation.poolAlignment
    · exact representation.poolUnique
    · exact representation.poolSeparatedPairwise
    · exact representation.poolAbsent
    · exact representation.poolSeparated
    · exact representation.allocatedBeforeCursor

private theorem bump_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (thread : AddressThreadId) (choices : AddressRandomChoices)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (taken : generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex
      target.size target.align .other thread = ⟨generation.reusePool,.ok none⟩)
    (alignment : target.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator target.size target.align choices.slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat) :
    ∃ (after : GlobalAddressState) (next : AddressGenerationState),
      AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
        (some ⟨.liveData,true,target.size,target.align,some .other,thread⟩) choices) = .ok after ∧
      InputDraft.GenerationRepresentation (withAddresses before after) next := by
  let generator := RawGenerator.next generation.generator target.size target.align choices.slack
  let address := RawGenerator.base generation.generator target.align choices.slack
  let generatedGen := {generation with generator}
  let advancedAddr := {before.machine.user.addresses with generation := some generatedGen}
  let advanced := withAddresses before advancedAddr
  let remaining := generator.getRemaining
  let pool := if remaining.start > remaining.stop / 2 then generation.reusePool.addressSpaceShortage
    else generation.reusePool
  let next := {generatedGen with reusePool := pool}
  let stageAddr := {before.machine.user.addresses with generation := some next}
  let stage := withAddresses before stageAddr
  have lower := (RawGenerator.base_bounds generation.generator target.size target.align alignment choices.slack room).1
  have nextNat := RawGenerator.next_nat generation.generator target.size target.align alignment choices.slack room
  have monotone : generation.generator.nextBaseAddr.toNat ≤ generator.nextBaseAddr.toNat := by
    dsimp only [generator]
    rw [nextNat]
    omega
  have advancedRep : InputDraft.GenerationRepresentation advanced generatedGen :=
    advance_representation before generation representation generator monotone
  have stageRep : InputDraft.GenerationRepresentation stage next := by
    by_cases shortage : remaining.start > remaining.stop / 2
    · have post := shortage_representation advanced generatedGen advancedRep
      simpa only [stage,stageAddr,next,pool,ite_eq_left shortage,advanced,advancedAddr,withAddresses,generatedGen] using post
    · simpa only [stage,stageAddr,next,pool,ite_eq_right shortage] using advancedRep
  have nonzero : address ≠ 0 := by
    intro zero
    change _ ≤ address.toNat at lower
    rw [zero] at lower
    change _ ≤ 0 at lower
    omega
  have distinct : ∀ row ∈ before.machine.user.addresses.intToPtrMap, row.address ≠ address := by
    intro row member equal
    have old := RawResources.frontier before generation representation row member
    change _ ≤ address.toNat at lower
    rw [equal] at old
    omega
  have postRep : InputDraft.GenerationRepresentation
      (withAddresses stage (stageAddr.cacheAddress id address).state) next := by
    apply cache_representation stage next stageRep id address uncached nonzero
      (backing_withAddresses before stageAddr id backing) live distinct
    · intro row member oldInfo newInfo oldQuery newQuery
      have prior := representation.allocatedBeforeCursor row member oldInfo oldQuery
      exact Or.inl (by change _ ≤ address.toNat; change _ ≤ address.toNat at lower; omega)
    · intro bucket member row stored equal
      change bucket ∈ pool.pool at member
      have samePool : pool.pool = generation.reusePool.pool := by
        dsimp only [pool,ReusePool.addressSpaceShortage]
        split <;> first | rfl | (split <;> rfl)
      rw [samePool] at member
      have prior := (representation.poolAddresses bucket member row stored).2
      change _ ≤ address.toNat at lower
      rw [equal] at prior
      omega
    · intro bucket member row stored info query
      change bucket ∈ pool.pool at member
      have samePool : pool.pool = generation.reusePool.pool := by
        dsimp only [pool,ReusePool.addressSpaceShortage]
        split <;> first | rfl | (split <;> rfl)
      rw [samePool] at member
      have prior := (representation.poolAddresses bucket member row stored).2
      exact Or.inl (by change _ ≤ address.toNat; change _ ≤ address.toNat at lower; omega)
    · intro info query
      have same : info = target := by
        change before.machine.memory.getAllocInfo id = .ok info at query
        rw [metadata] at query
        exact (Except.ok.inj query).symm
      subst info
      change address.toNat + max target.size.bytes.toNat 1 ≤ generator.nextBaseAddr.toNat
      have nextEq : generator.nextBaseAddr.toNat = address.toNat + max 1 target.size.bytes.toNat := nextNat
      omega
  have cached : (stageAddr.cacheAddress id address).outcome = .ok () :=
    RawAddressCache.cache_fresh stageAddr id address uncached distinct
  refine ⟨(stageAddr.cacheAddress id address).state,next,?_,postRep⟩
  have generated := RawGenerator.generated generation.generator target.size target.align alignment choices.slack room
  unfold GlobalAddressState.addrFromAllocId
  unfold_source_base
  unfold_source_generation
  simp only [uncached,Option.map_none,representation.managed,representation.current,
    Bool.not_true,↓reduceIte,Id.run,pure,taken,generated,
    show (AllocationAddressKind.liveData == AllocationAddressKind.dead) = false from rfl,
    show (AllocationAddressKind.liveData == AllocationAddressKind.typeId) = false from rfl,
    Bool.false_or,Bool.false_eq_true]
  simp only [←representation.managed]
  change AddressChoicePlan.assignedState
    (match (stageAddr.cacheAddress id address).outcome with
    | .ok _ => ⟨(stageAddr.cacheAddress id address).state,.ok (.ready address)⟩
    | .error error => ⟨(stageAddr.cacheAddress id address).state,.error error⟩) = _
  simp only [cached,AddressChoicePlan.assignedState]

/-- Actual no-reuse bump assignment preserves all representation fields for
any legal slack, with the pure no-hole result derived from Bernoulli support. -/
theorem no_reuse_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (thread : AddressThreadId) (slack : Fin 16)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true)
    (alignment : target.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator target.size target.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat) :
    ∃ (after : GlobalAddressState) (next : AddressGenerationState),
      AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
        (some ⟨.liveData,true,target.size,target.align,some .other,thread⟩)
        ⟨false,false,0,slack⟩) = .ok after ∧
      InputDraft.GenerationRepresentation (withAddresses before after) next := by
  exact bump_representation before generation representation id target thread _ uncached backing live metadata
    (ReuseTake.no_reuse generation.reusePool target.size target.align thread false 0 allowed).2
    alignment room positive

/-- Actual reuse=true/current-empty-range bump assignment preserves the full
representation. Absent buckets are admitted via ensure_representation first. -/
theorem empty_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (thread : AddressThreadId)
    (bucket : Array ReusableAddress) (bytes : UInt64) (cross : Bool) (selection : Nat) (slack : Fin 16)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (present : generation.reusePool.pool[target.align.pow2]? = some bucket)
    (alignment : Align.bytes target.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok target.align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross = true)
    (empty : (ReuseCandidate.candidate bucket target.size thread cross).2 =
      (ReuseCandidate.candidate bucket target.size thread cross).1)
    (room : RawGenerator.Room generation.generator target.size target.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat) :
    ∃ (after : GlobalAddressState) (next : AddressGenerationState),
      AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
        (some ⟨.liveData,true,target.size,target.align,some .other,thread⟩)
        ⟨true,cross,selection,slack⟩) = .ok after ∧
      InputDraft.GenerationRepresentation (withAddresses before after) next := by
  exact bump_representation before generation representation id target thread _ uncached backing live metadata
    (ReuseTake.take_empty generation.reusePool bucket target.size target.align bytes thread cross selection
      present alignment normalized reuseAllowed crossAllowed empty)
    (RawGenerator.normalized_exponent target.align bytes normalized) room positive

/-- TypeId caches zero without adding an inverse row. Retained cache keys and
all current inverse-table fields stay coherent. -/
theorem cache_zero (addresses : GlobalAddressState) (id : AllocId)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none) :
    addresses.cacheAddress id 0 =
      ⟨{addresses with baseAddr := addresses.baseAddr.push ⟨id,0⟩},.ok ()⟩ := by
  have noFilter : addresses.baseAddr.filter (fun row => row.allocId != id) = addresses.baseAddr := by
    apply Array.filter_eq_self.mpr
    intro row member
    have fresh := Array.find?_eq_none.mp uncached row member
    simp only [bne,fresh,Bool.not_false]
  unfold GlobalAddressState.cacheAddress
  unfold_source_base
  unfold_source_insert_base
  simp only [uncached,Option.map_none,noFilter,beq_self_eq_true,↓reduceIte]
  rfl

theorem cache_zero_tables (before : WholeCall.State) (tables : InputDraft.AddressTables before)
    (id : AllocId)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none) :
    InputDraft.AddressTables (withAddresses before (before.machine.user.addresses.cacheAddress id 0).state) := by
  rw [cache_zero _ id uncached]
  constructor
  · change ((before.machine.user.addresses.baseAddr.push ⟨id,0⟩).toList.map (·.allocId)).Nodup
    simp only [Array.toList_push,List.map_append,List.map_cons,List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨tables.baseIds,by simp,?_⟩
    intro old member new newMember
    have newEq : new = id := by simpa using newMember
    subst new
    obtain ⟨row,member,equal⟩ := List.mem_map.mp member
    intro same
    have absent := Array.find?_eq_none.mp uncached row (by simpa using member)
    exact absent (by simp only [equal,same,beq_self_eq_true])
  · exact tables.inverseIds
  · intro row member
    exact backing_withAddresses before _ row.allocId (tables.suppliers row member)
  · exact tables.inverseLive
  · exact tables.nonzero
  · intro row member
    change (before.machine.user.addresses.baseAddr.push ⟨id,0⟩).find? _ = _
    simp only [Array.find?_push,tables.bases row member,Option.or]
  · intro row member live nonzero
    change row ∈ before.machine.user.addresses.baseAddr.push ⟨id,0⟩ at member
    rcases Array.mem_push.mp member with prior | equal
    · exact tables.liveBases row prior live nonzero
    · subst row
      exact False.elim (nonzero rfl)
  · exact tables.ordered
  · exact tables.separated
  · exact tables.exposedLive
  · intro id member
    obtain ⟨base,present⟩ := tables.exposedBases id member
    refine ⟨base,?_⟩
    change (before.machine.user.addresses.baseAddr.push _).find? _ = _
    simp only [Array.find?_push,present,Option.or]

theorem cache_zero_representation (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none) :
    InputDraft.GenerationRepresentation
      (withAddresses before (before.machine.user.addresses.cacheAddress id 0).state) generation := by
  have tables := cache_zero_tables before representation.tables id uncached
  rw [cache_zero _ id uncached] at tables ⊢
  constructor
  · exact representation.current
  · exact representation.managed
  · exact tables
  · exact representation.reuseRateLower
  · exact representation.reuseRateUpper
  · exact representation.crossRateLower
  · exact representation.crossRateUpper
  · exact representation.poolKeys
  · exact representation.poolSize
  · exact representation.poolAddresses
  · exact representation.poolAlignment
  · exact representation.poolUnique
  · exact representation.poolSeparatedPairwise
  · exact representation.poolAbsent
  · exact representation.poolSeparated
  · exact representation.allocatedBeforeCursor

end EmptyFunction.AddressPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved address post axiom {dependency} in {name}"
