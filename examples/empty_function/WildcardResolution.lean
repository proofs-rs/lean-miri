import empty_function.WildcardSearch
import empty_function.CanonicalDictionaries
namespace EmptyFunction.WildcardResolution
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.InputDraft EmptyFunction.WildcardSearch
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem metadata_known (before : State) (id : AllocId) (supplier : MetadataBacking before id) :
    ∃ info, before.machine.memory.getAllocInfo id = .ok info := by
  unfold MemoryState.getAllocInfo
  split
  · exact ⟨_,rfl⟩
  · split
    · exact ⟨_,rfl⟩
    · split
      · exact ⟨_,rfl⟩
      · split
        · rename_i global found
          cases global.kind <;> exact ⟨_,rfl⟩
        · split
          · exact ⟨_,rfl⟩
          · cases supplier <;> simp_all [MemoryState.hasExtraFunctionId,MemoryState.hasFunctionPointer,MemoryState.hasVaListId]


def lookup (before : State) : AddressLookupHooks :=
  ⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
    fun id => some (before.machine.memory.isAllocLive id)⟩

theorem ordered (before : State) (tables : AddressTables before) :
    Ordered before.machine.user.addresses.intToPtrMap := by
  intro i j smaller valid
  have h := List.pairwise_iff_getElem.mp tables.ordered i j (by simpa using (show i < before.machine.user.addresses.intToPtrMap.size by omega)) (by simpa using valid) smaller
  simpa using h

open Lean Elab Tactic in
elab "unfold_inverse_wrapper" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (n,_) =>
    if n.toString.endsWith ".GlobalAddressState.inverseSearch" then some n else none
  let [name] := names | throwError "expected source inverse wrapper"
  evalTactic (← `(tactic| unfold $(mkIdent name)))

def Classified (before : State) (pointer : Pointer (Option Provenance)) (answer : Option AllocId) : Prop :=
  match answer with
  | none => True
  | some id => ∃ row ∈ before.machine.user.addresses.intToPtrMap,
    row.allocId = id ∧ before.machine.user.addresses.exposed.contains id = true ∧
    WildcardCandidate before pointer row

private theorem candidate_exact (before : State) (pointer : Pointer (Option Provenance))
    (row : InverseAddressEntry)
    (same : row.address = pointer.offset.bytes) : WildcardCandidate before pointer row := by
  refine ⟨by rw [same];exact UInt64.le_iff_toNat_le.mpr (Nat.le_refl _),?_,Or.inl same.symm⟩
  intro later member larger
  rw [←same]
  exact larger

/-- Every coherent wildcard zero-byte query returns an optional allocation;
all errors are ruled out from raw table/supplier data. Hits retain the actual
nearest-row geometry, rather than assuming resolver success. -/
theorem allocation (before : State) (pointer : Pointer (Option Provenance))
    (tables : AddressTables before) (mode : before.machine.user.addresses.provenanceMode ≠ .strict) :
    ∃ answer, before.machine.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (lookup before) = .ok answer ∧
      Classified before pointer answer := by
  let entries := before.machine.user.addresses.intToPtrMap
  obtain ⟨position,row,valid,found,same,search⟩ | ⟨cut,search,partition⟩ :=
    inverse_partition entries pointer.offset.bytes (ordered before tables)
  all_goals dsimp only [entries] at *
  · have member : row ∈ before.machine.user.addresses.intToPtrMap := Array.mem_of_getElem? found
    have live := tables.inverseLive row member
    cases exposed : before.machine.user.addresses.exposed.contains row.allocId with
    | false =>
      have ep := exposed
      simp [Array.contains_eq_mem] at ep
      refine ⟨none,?_,True.intro⟩
      unfold GlobalAddressState.allocIdFromAddr
      unfold_inverse_wrapper
      simp [pure,Except.pure,bind,Except.bind,Array.contains_eq_mem,mode,search,found,ep,exposed]
    | true =>
      have ep := exposed
      simp [Array.contains_eq_mem] at ep
      refine ⟨some row.allocId,?_,row,member,rfl,exposed,candidate_exact before pointer row same⟩
      unfold GlobalAddressState.allocIdFromAddr
      unfold_inverse_wrapper
      simp [pure,Except.pure,bind,Except.bind,Array.contains_eq_mem,mode,search,found,ep,exposed,lookup,live]
  · by_cases zero : cut=0
    · refine ⟨none,?_,True.intro⟩
      unfold GlobalAddressState.allocIdFromAddr
      unfold_inverse_wrapper
      simp [pure,Except.pure,bind,Except.bind,Array.contains_eq_mem,mode,search,zero]
    · have predecessor : cut-1 < entries.size := by have bound := partition.1;dsimp only [entries];omega
      let row := entries[cut-1]
      have found : entries[cut-1]?=some row := Array.getElem?_eq_getElem predecessor
      dsimp only [entries] at found
      have member : row ∈ before.machine.user.addresses.intToPtrMap := Array.mem_of_getElem? found
      obtain ⟨info,metadata⟩ := metadata_known before row.allocId (tables.suppliers row member)
      have size : (lookup before).sizeOf row.allocId = some info.size := by simp only [lookup,metadata,Except.toOption,Option.map_some]
      by_cases inside : pointer.offset.bytes-row.address < info.size.bytes
      · have earlier : row.address < pointer.offset.bytes := partition.2.1 (cut-1) predecessor (by omega)
        have geometry : WildcardCandidate before pointer row := by
          refine ⟨UInt64.le_iff_toNat_le.mpr (by have a:=UInt64.lt_iff_toNat_lt.mp earlier;omega),?_,Or.inr ⟨info,metadata,?_⟩⟩
          · intro later laterMember larger
            obtain ⟨index,indexValid,equal⟩ := Array.mem_iff_getElem.mp laterMember
            by_cases above : cut ≤ index
            · simpa only [equal] using partition.2.2 index indexValid above
            · have beforeCut : index < cut := by omega
              have prev : index ≤ cut-1 := by omega
              by_cases eq : index=cut-1
              · have leq : later=row := by subst index;exact equal.symm
                rw [leq] at larger
                have impossible := UInt64.lt_iff_toNat_lt.mp larger
                omega
              · have lt : index<cut-1 := by omega
                have small := ordered before tables index (cut-1) lt predecessor
                rw [equal] at small
                have a:=UInt64.lt_iff_toNat_lt.mp small
                have b:=UInt64.lt_iff_toNat_lt.mp larger
                change row.address.toNat < later.address.toNat at b
                change later.address.toNat < row.address.toNat at a
                omega
          · have raw := UInt64.lt_iff_toNat_lt.mp inside
            rw [UInt64.toNat_sub] at raw
            have xb := pointer.offset.bytes.toNat_lt
            have yb := row.address.toNat_lt
            have base := UInt64.lt_iff_toNat_lt.mp earlier
            omega
        cases exposed : before.machine.user.addresses.exposed.contains row.allocId with
        | false =>
          have ep := exposed
          simp [Array.contains_eq_mem] at ep
          refine ⟨none,?_,True.intro⟩
          unfold GlobalAddressState.allocIdFromAddr
          unfold_inverse_wrapper
          simp [pure,Except.pure,bind,Except.bind,Array.contains_eq_mem,mode,search,zero,found,size,inside,ep,exposed]
        | true =>
          have ep := exposed
          simp [Array.contains_eq_mem] at ep
          have live := tables.inverseLive row member
          refine ⟨some row.allocId,?_,row,member,rfl,exposed,geometry⟩
          unfold GlobalAddressState.allocIdFromAddr
          unfold_inverse_wrapper
          simp [pure,Except.pure,bind,Except.bind,Array.contains_eq_mem,mode,search,zero,found,size,inside,ep,exposed,lookup,live,metadata,Except.toOption]
      · refine ⟨none,?_,True.intro⟩
        unfold GlobalAddressState.allocIdFromAddr
        unfold_inverse_wrapper
        simp [pure,Except.pure,bind,Except.bind,Array.contains_eq_mem,mode,search,zero,found,size,inside]

def Encoded (pointer : Pointer (Option Provenance)) :
    Option Miri.TreeBorrows.RetagPipeline.ResolvedLocation → Except UInt64 (ResolvedPointer ProvenanceExtra)
  | none => .error pointer.offset.bytes
  | some result => .ok ⟨result.allocId,result.baseOffset,result.parentProvenance⟩

def Hits (s : Static) (before : State) (pointer : Pointer (Option Provenance)) :
    Option Miri.TreeBorrows.RetagPipeline.ResolvedLocation → Prop
  | none => True
  | some result => ∃ row ∈ before.machine.user.addresses.intToPtrMap,
      result = ⟨row.allocId, Size.ofBytes (pointer.offset.bytes-row.address),.wildcard⟩ ∧
      before.machine.user.addresses.exposed.contains row.allocId = true ∧
      WildcardCandidate before pointer row ∧ Backing s before row.allocId

/-- Actual typed-memory and retag resolvers on every raw wildcard zero-size
input. Misses remain normal unresolved results; hits retain the existing
live/nondata/latent Backing classification and the precise source offset. -/
theorem resolve_at (s : Static) (before current : State)
    (memory : current.machine.memory = before.machine.memory)
    (addresses : current.machine.user.addresses = before.machine.user.addresses) (tracker : MachineHooks.BorrowState)
    (pointers : CanonicalDictionaries.Pointers)
    (pointer : Pointer (Option Provenance))
    (input : PointerInput s before tracker pointer)
    (wild : pointer.provenance = some .wildcard)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value) :
    ∃ answer,
      TypedMemoryProviders.resolvePointer pointers current.machine.memory pointer 0 current.machine =
        .ok (Encoded pointer answer) current.machine ∧
      TypedValidityProviders.resolveAllocation pointers pointer current = .ok answer current ∧
      Hits s before pointer answer := by
  cases input with
  | integer integer => rw [wild] at integer; cases integer
  | concrete id tag base tables encoding cached backing parent latent =>
    rw [wild] at encoding
    cases encoding
  | wildcard encoding mode tables selected =>
    obtain ⟨answer,allocated,classification⟩ := allocation before pointer tables mode
    cases answer with
    | none =>
      have raw : before.machine.user.addresses.ptrGetAlloc
          (Pointer.new Provenance.wildcard pointer.offset) 0 (lookup before) pointers.arithmetic = .ok none := by
        simp [GlobalAddressState.ptrGetAlloc,Pointer.new,allocated,pure,Except.pure,bind,Except.bind]
      dsimp only [lookup] at raw
      refine ⟨none,?_,?_,True.intro⟩
      · simp [TypedMemoryProviders.resolvePointer,wild,raw,lookup,Encoded,memory,addresses,
          get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure,bind,EStateM.bind]
      · simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,
          wild,raw,lookup,Encoded,memory,addresses, get,getThe,MonadStateOf.get,EStateM.get,
          pure,EStateM.pure,bind,EStateM.bind,set,EStateM.set,Id.run]
    | some id =>
      obtain ⟨row,member,same,exposed,geometry⟩ := classification
      subst id
      have cached := tables.bases row member
      have raw : before.machine.user.addresses.ptrGetAlloc
          (Pointer.new Provenance.wildcard pointer.offset) 0 (lookup before) pointers.arithmetic =
          .ok (some (row.allocId, Size.ofBytes (pointer.offset.bytes-row.address))) := by
        unfold GlobalAddressState.ptrGetAlloc
        change (show Except AddressStateError (Option (AllocId × Size)) from do
          let some id ← before.machine.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (lookup before)
            | pure none
          let some base := (before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id)).map BaseAddressEntry.address
            | throw (.missingBaseAddress id)
          let relative ← (pointers.arithmetic.truncateToTargetUsize (pointer.offset.bytes-base)).mapError AddressStateError.pointerArithmetic
          pure (some (id,Size.ofBytes relative))) = _
        simp only [allocated,bind,Except.bind,pure,Except.pure]
        simp only [cached,Option.map_some,truncate,Except.mapError]
      dsimp only [lookup] at raw
      refine ⟨some ⟨row.allocId,Size.ofBytes (pointer.offset.bytes-row.address),.wildcard⟩,?_,?_,row,member,rfl,exposed,geometry,selected row member exposed geometry⟩
      · simp [TypedMemoryProviders.resolvePointer,wild,raw,lookup,Encoded,memory,addresses,
          get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure,bind,EStateM.bind]
      · simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,
          wild,raw,lookup,Encoded,memory,addresses, get,getThe,MonadStateOf.get,EStateM.get,
          pure,EStateM.pure,bind,EStateM.bind,set,EStateM.set,Id.run]
end EmptyFunction.WildcardResolution
