import empty_function.CanonicalLatentPreflight
namespace EmptyFunction.WildcardCandidateExact
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.MIR Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.InputDraft EmptyFunction.WildcardSearch
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- Raw nearest-row geometry determines the existing binary-search consumer,
including latent data: no live allocation or positive byte demand is needed. -/
theorem allocation (before : State) (pointer : Pointer (Option Provenance))
    (row : InverseAddressEntry) (member : row ∈ before.machine.user.addresses.intToPtrMap)
    (tables : AddressTables before) (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.machine.user.addresses.exposed.contains row.allocId = true)
    (candidate : WildcardCandidate before pointer row) :
    before.machine.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (WildcardResolution.lookup before) =
      .ok (some row.allocId) := by
  obtain ⟨position,valid,actual⟩ := Array.mem_iff_getElem.mp member
  have shape : row = ⟨row.address,row.allocId⟩ := by cases row;rfl
  have atRow : before.machine.user.addresses.intToPtrMap[position]? = some ⟨row.address,row.allocId⟩ :=
    (Array.getElem?_eq_getElem valid).trans (congrArg some (actual.trans shape))
  have atAddress : before.machine.user.addresses.intToPtrMap[position].address = row.address := by rw [actual]
  have ordered := WildcardResolution.ordered before tables
  have live : (WildcardResolution.lookup before).isLive row.allocId = some true :=
    congrArg some (tables.inverseLive row member)
  by_cases base : pointer.offset.bytes = row.address
  · have search := inverse_hit before.machine.user.addresses.intToPtrMap row.address row.allocId position valid ordered atRow
    rw [base]
    exact GlobalAddressState.allocation_base_zero before.machine.user.addresses row.address row.allocId
      (WildcardResolution.lookup before) position mode search atRow exposed live
  · obtain ⟨info,known,extent⟩ := candidate.2.2.resolve_left base
    have size : (WildcardResolution.lookup before).sizeOf row.allocId = some info.size := by
      simp only [WildcardResolution.lookup,known,Except.toOption,Option.map_some]
    have inside : pointer.offset.bytes-row.address < info.size.bytes := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [UInt64.toNat_sub_of_le _ _ candidate.1]
      have lower := UInt64.le_iff_toNat_le.mp candidate.1
      omega
    have afterBase : row.address < pointer.offset.bytes := UInt64.lt_iff_toNat_lt.mpr (by
      have le := UInt64.le_iff_toNat_le.mp candidate.1
      have ne : pointer.offset.bytes.toNat ≠ row.address.toNat := by intro eq;exact base (UInt64.toNat_inj.mp eq)
      omega)
    have geometry : Cut before.machine.user.addresses.intToPtrMap pointer.offset.bytes (position+1) := by
      refine ⟨by omega,?_,?_⟩
      · intro i bounded beforeCut
        by_cases same : i = position
        · subst i;rw [atAddress];exact afterBase
        · have earlier := ordered i position (by omega) valid
          rw [atAddress] at earlier
          apply UInt64.lt_iff_toNat_lt.mpr
          have a := UInt64.lt_iff_toNat_lt.mp earlier
          have b := UInt64.lt_iff_toNat_lt.mp afterBase
          omega
      · intro i bounded afterCut
        have later := ordered position i (by omega) bounded
        rw [atAddress] at later
        exact candidate.2.1 _ (Array.getElem_mem bounded) later
    have different : ∀ other ∈ before.machine.user.addresses.intToPtrMap, other.address ≠ pointer.offset.bytes := by
      intro other member same
      obtain ⟨i,bounded,atElement⟩ := Array.mem_iff_getElem.mp member
      by_cases beforeCut : i < position+1
      · have below := geometry.2.1 i bounded beforeCut
        rw [atElement,same] at below
        exact UInt64.lt_irrefl _ below
      · have above := geometry.2.2 i bounded (by omega)
        rw [atElement,same] at above
        exact UInt64.lt_irrefl _ above
    obtain ⟨cut,search,partition⟩ := inverse_cut before.machine.user.addresses.intToPtrMap pointer.offset.bytes ordered different
    have equalCut : cut = position+1 := by
      rcases Nat.lt_trichotomy cut (position+1) with earlier | same | later
      · have bounded : cut < before.machine.user.addresses.intToPtrMap.size := by have h := geometry.1;omega
        have a := UInt64.lt_iff_toNat_lt.mp (geometry.2.1 cut bounded earlier)
        have b := UInt64.lt_iff_toNat_lt.mp (partition.2.2 cut bounded (Nat.le_refl _))
        omega
      · exact same
      · have bounded : position+1 < before.machine.user.addresses.intToPtrMap.size := by have h := partition.1;omega
        have a := UInt64.lt_iff_toNat_lt.mp (partition.2.1 (position+1) bounded later)
        have b := UInt64.lt_iff_toNat_lt.mp (geometry.2.2 (position+1) bounded (Nat.le_refl _))
        omega
    rw [equalCut] at search
    exact GlobalAddressState.allocation_interior_zero before.machine.user.addresses pointer.offset.bytes row.address row.allocId
      (WildcardResolution.lookup before) info.size position mode search atRow size inside exposed live

theorem resolve (s : Static) (metadata : Specification.Metadata s) (positive : 0 < s.capacity)
    (before current : State) (memory : current.machine.memory = before.machine.memory)
    (addresses : current.machine.user.addresses = before.machine.user.addresses)
    (pointer : Pointer (Option Provenance)) (wild : pointer.provenance = some .wildcard)
    (row : InverseAddressEntry) (member : row ∈ before.machine.user.addresses.intToPtrMap)
    (tables : AddressTables before) (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.machine.user.addresses.exposed.contains row.allocId = true)
    (candidate : WildcardCandidate before pointer row) :
    s.cfg.retag.resolveAllocation pointer current =
      .ok (some ⟨row.allocId,Size.ofBytes (pointer.offset.bytes-row.address),.wildcard⟩) current := by
  have allocated := allocation before pointer row member tables mode exposed candidate
  have raw := GlobalAddressState.pointer_from_selection before.machine.user.addresses
    (Pointer.new .wildcard pointer.offset) 0 (WildcardResolution.lookup before)
    (ConcreteProtection.source s).pointers.arithmetic row.allocId row.address (pointer.offset.bytes-row.address)
    allocated (tables.bases row member) (ConcreteProtection.source_truncate s metadata.pointerSize _)
  dsimp only [WildcardResolution.lookup] at raw
  rw [(ConcreteProtection.bindings s metadata positive).1]
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,wild,raw,WildcardResolution.lookup,
    memory,addresses,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure,bind,EStateM.bind,set,EStateM.set,Id.run]
end EmptyFunction.WildcardCandidateExact
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.WildcardCandidateExact." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved raw candidate axiom {dependency} in {name}"
