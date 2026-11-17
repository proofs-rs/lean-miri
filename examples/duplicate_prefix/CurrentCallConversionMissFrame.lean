import duplicate_prefix.CurrentCallConversionChoiceProtocol
import duplicate_prefix.GlobalAddressBaseCacheFormation
import duplicate_prefix.WildcardGeneralHitReborrow
import duplicate_prefix.WildcardEmptyAddressClassification
import duplicate_prefix.GlobalAddressRangeFormation

namespace DuplicatePrefix.CurrentCallConversionMissFrame
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open WildcardInteriorHitAddress WildcardEmptyFamilyFormation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Current address-assignment coherence; it is not a property established by
calling the bare exposure primitive on an arbitrary provenance. -/
def ExposedCached (state : GlobalAddressState) : Prop :=
  ∀id,state.exposed.contains id=true→∃base,state.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩

private theorem cache_base (state : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (CurrentCallConversionChoiceProtocol.cacheData state id address).baseAddr=
      (state.baseAddr.filter (fun row=>row.allocId != id)).push ⟨id,address⟩ := by
  unfold CurrentCallConversionChoiceProtocol.cacheData
  split <;> rfl

private theorem cache_exposed (state : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (CurrentCallConversionChoiceProtocol.cacheData state id address).exposed=state.exposed := by
  unfold CurrentCallConversionChoiceProtocol.cacheData
  split <;> rfl

theorem uncached_not_exposed (state : GlobalAddressState) (id : AllocId) (coherent : ExposedCached state)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) : state.exposed.contains id=false := by
  cases exposed : state.exposed.contains id with
  | false=>rfl
  | true=>obtain ⟨base,hit⟩:=coherent id exposed;rw [uncached] at hit;cases hit

private theorem cache_members (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (row : InverseAddressEntry)
    (member : row∈(CurrentCallConversionChoiceProtocol.cacheData state id address).intToPtrMap) :
    row=⟨address,id⟩ ∨row∈state.intToPtrMap := by
  unfold CurrentCallConversionChoiceProtocol.cacheData at member
  split at member
  · exact Or.inr member
  · dsimp only at member
    unfold Array.insertIdxIfInBounds at member
    split at member
    · exact Array.mem_insertIdx.mp member
    · exact Or.inr member

private def Frame (before after : GlobalAddressState) : Prop :=
  ExposedCached after ∧after.exposed=before.exposed ∧
    ∀row∈after.intToPtrMap,after.exposed.contains row.allocId=true→row∈before.intToPtrMap

private theorem frame_self (state : GlobalAddressState) (coherent : ExposedCached state) : Frame state state :=
  ⟨coherent,rfl,fun _ member _=>member⟩

private theorem frame_trans (first middle last : GlobalAddressState) (one : Frame first middle) (two : Frame middle last) :
    Frame first last := by
  refine ⟨two.1,two.2.1.trans one.2.1,?_⟩
  intro row member exposed
  exact one.2.2 row (two.2.2 row member exposed) (by rw [←two.2.1];exact exposed)

private theorem cache_frame (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (coherent : ExposedCached state) (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) :
    Frame state (CurrentCallConversionChoiceProtocol.cacheData state id address) := by
  have fresh:=uncached_not_exposed state id coherent uncached
  refine ⟨?_,cache_exposed state id address,?_⟩
  · intro query exposed
    rw [cache_exposed] at exposed
    obtain ⟨base,hit⟩:=coherent query exposed
    have different : query≠id:=by intro same;subst query;rw [fresh] at exposed;cases exposed
    refine ⟨base,?_⟩
    rw [cache_base,GlobalAddressBaseCacheFormation.base_insert_other _ _ _ _ different]
    exact hit
  · intro row member exposed
    rw [cache_exposed] at exposed
    rcases cache_members state id address row member with equal | old
    · subst row;rw [fresh] at exposed;cases exposed
    · exact old

private theorem advance_frame (state : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationInfo) (thread : AddressThreadId) (tape : ExecutionChoices.Tape)
    (block : CurrentCallConversionChoiceProtocol.ManagedBlock generation.reusePool info.size info.align thread tape)
    (coherent : ExposedCached state) (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) :
    Frame state (CurrentCallConversionChoiceProtocol.advance state generation id info thread tape block) := by
  cases reuseEq : block.reuse
  all_goals
    unfold CurrentCallConversionChoiceProtocol.advance
    simp only [reuseEq,Bool.false_eq_true,↓reduceIte]
    split
  all_goals first | exact cache_frame _ _ _ coherent uncached | skip
  all_goals split
  all_goals first | exact frame_self state coherent | exact cache_frame _ _ _ coherent uncached

/-- Newly assigned inverse rows are unexposed. Thus a finite selected protocol
cannot add any candidate for a previously unresolved wildcard source. -/
theorem protocol_rows {K : Type} (memory : MemoryState Provenance TreeBorrows.BorrowTree K)
    (thread : AddressThreadId) (before after : GlobalAddressState) (tape nextTape : ExecutionChoices.Tape)
    (ids : List AllocId) (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol memory thread before tape ids after nextTape)
    (coherent : ExposedCached before) :
    ExposedCached after ∧after.exposed=before.exposed ∧
      ∀row∈after.intToPtrMap,after.exposed.contains row.allocId=true→row∈before.intToPtrMap := by
  induction protocol with
  | nil state tape=>exact frame_self state coherent
  | cached state tape id rest base hit final after tail ih=>exact ih coherent
  | typeId state tape id rest info uncached metadata kind final after tail ih=>
    have first:=cache_frame state id 0 coherent uncached
    exact frame_trans state _ final first (ih first.1)
  | managed state tape id rest info uncached metadata kind generation generationEq block final after tail ih=>
    have first:=advance_frame state generation id info thread tape block coherent uncached
    exact frame_trans state _ final first (ih first.1)

private theorem geometry_member (entries : Array InverseAddressEntry) (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry entries address base id size) :
    (⟨base,id⟩ : InverseAddressEntry)∈entries := by
  rcases geometry with ⟨_,position,valid,_,present⟩ | ⟨position,cut,present,_⟩
  · have actual:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
    rw [←actual];exact Array.getElem_mem valid
  · have valid : position<entries.size:=by have bounded:=cut.1;omega
    have actual:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
    rw [←actual];exact Array.getElem_mem valid

private theorem geometry_back (old next : Array InverseAddressEntry) (sizes : AllocId→Size)
    (ordered : Ordered old) (apart : Apart old sizes) (address base : UInt64) (id : AllocId) (size : Size)
    (member : (⟨base,id⟩ : InverseAddressEntry)∈old) (sizeEq : sizes id=size)
    (geometry : WildcardGeneralHitReborrow.Geometry next address base id size) :
    WildcardGeneralHitReborrow.Geometry old address base id size := by
  obtain ⟨index,valid,actual⟩:=Array.mem_iff_getElem.mp member
  have present:= (Array.getElem?_eq_getElem valid).trans (congrArg some actual)
  rcases geometry with ⟨equal,_,_,_,_⟩ | ⟨position,cut,row,inside⟩
  · exact Or.inl ⟨equal,index,valid,ordered,present⟩
  · have nextValid : position<next.size:=by have bounded:=cut.1;omega
    have nextActual:=Option.some.inj ((Array.getElem?_eq_getElem nextValid).symm.trans row)
    have lower : base<address:=by
      have before:=cut.2.1 position nextValid (Nat.lt_succ_self _)
      rw [nextActual] at before
      exact before
    have insideNat : address.toNat<base.toNat+size.bytes.toNat:=by
      have raw:=UInt64.lt_iff_toNat_lt.mp inside
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lower)] at raw
      omega
    have beforeNext : ∀bounded:index+1<old.size,address<old[index+1].address:=by
      intro bounded
      have separation:=apart index (index+1) bounded (Nat.lt_succ_self _)
      rw [actual,sizeEq] at separation
      exact UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le insideNat separation)
    exact Or.inr ⟨index,cut_of_ordered old address base id index valid ordered present lower beforeNext,present,inside⟩

private theorem geometry_not_miss (state : GlobalAddressState) (hooks : AddressLookupHooks)
    (address base : UInt64) (id : AllocId) (size : Size)
    (mode : state.provenanceMode≠.strict) (exposed : state.exposed.contains id=true)
    (known : hooks.sizeOf id=some size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id size)
    (miss : state.allocIdFromAddr address 0 hooks=.ok none) : False := by
  have member : id∈state.exposed := by simpa using exposed
  rcases geometry with ⟨equal,position,valid,ordered,present⟩ | ⟨position,cut,present,inside⟩
  · have search:=WildcardOrderedHitAddress.inverse_hit state.intToPtrMap base id position valid ordered present
    rw [equal] at miss
    unfold GlobalAddressState.allocIdFromAddr at miss
    unfold_internal_at ".GlobalAddressState.inverseSearch" at miss
    cases live : hooks.isLive id with
    | none=>simp [mode,search,present,exposed,member,live,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at miss
    | some alive=>cases alive <;> simp [mode,search,present,exposed,member,live,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at miss
  · have search:=WildcardInteriorHitAddress.inverse_cut state.intToPtrMap address (position+1) cut
    unfold GlobalAddressState.allocIdFromAddr at miss
    unfold_internal_at ".GlobalAddressState.inverseSearch" at miss
    cases live : hooks.isLive id with
    | none=>simp [mode,search,present,known,inside,exposed,member,live,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at miss
    | some alive=>cases alive <;> simp [mode,search,present,known,inside,exposed,member,live,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at miss

/-- An old successful MISS cannot acquire any exposed exact/interior hit from
rows inserted by the selected protocol. Inverse-ID uniqueness is unnecessary. -/
theorem no_activated_hit (before after : GlobalAddressState) (sizes : AllocId→Size)
    (ordered : Ordered before.intToPtrMap) (apart : Apart before.intToPtrMap sizes)
    (exposedEq : after.exposed=before.exposed)
    (rows : ∀row∈after.intToPtrMap,after.exposed.contains row.allocId=true→row∈before.intToPtrMap)
    (hooks : AddressLookupHooks) (address : UInt64) (mode : before.provenanceMode≠.strict)
    (metadata : ∀row∈before.intToPtrMap,hooks.sizeOf row.allocId=some (sizes row.allocId))
    (miss : before.allocIdFromAddr address 0 hooks=.ok none)
    (base : UInt64) (id : AllocId)
    (geometry : WildcardGeneralHitReborrow.Geometry after.intToPtrMap address base id (sizes id))
    (exposed : after.exposed.contains id=true) : False := by
  have member:=rows ⟨base,id⟩ (geometry_member _ _ _ _ _ geometry) exposed
  have oldGeometry:=geometry_back before.intToPtrMap after.intToPtrMap sizes ordered apart address base id _ member rfl geometry
  exact geometry_not_miss before hooks address base id _ mode (by rw [←exposedEq];exact exposed)
    (metadata ⟨base,id⟩ member) oldGeometry miss

/-- Literal zero-width address lookup retains an old successful MISS. -/
theorem lookup_miss (before after : GlobalAddressState) (sizes : AllocId→Size)
    (ordered : Ordered before.intToPtrMap) (apart : Apart before.intToPtrMap sizes)
    (nextOrdered : Ordered after.intToPtrMap)
    (exposedEq : after.exposed=before.exposed)
    (rows : ∀row∈after.intToPtrMap,after.exposed.contains row.allocId=true→row∈before.intToPtrMap)
    (oldHooks nextHooks : AddressLookupHooks) (address : UInt64)
    (mode : before.provenanceMode≠.strict) (modeEq : after.provenanceMode=before.provenanceMode)
    (oldMetadata : ∀row∈before.intToPtrMap,oldHooks.sizeOf row.allocId=some (sizes row.allocId))
    (nextMetadata : ∀row∈after.intToPtrMap,nextHooks.sizeOf row.allocId=some (sizes row.allocId))
    (miss : before.allocIdFromAddr address 0 oldHooks=.ok none) :
    after.allocIdFromAddr address 0 nextHooks=.ok none := by
  have nextMode : after.provenanceMode≠.strict := by rw [modeEq];exact mode
  rcases WildcardEmptyAddressClassification.inverse_partition after.intToPtrMap address nextOrdered with
    ⟨position,row,valid,present,equal,search⟩ | ⟨cut,search,partition⟩
  · have shape : row=⟨row.address,row.allocId⟩ := by cases row;rfl
    by_cases exposed : after.exposed.contains row.allocId=true
    · have geometry : WildcardGeneralHitReborrow.Geometry after.intToPtrMap address row.address row.allocId (sizes row.allocId) :=
        Or.inl ⟨equal.symm,position,valid,nextOrdered,by simpa only [←shape] using present⟩
      exact False.elim (no_activated_hit before after sizes ordered apart exposedEq rows oldHooks address mode oldMetadata miss _ _ geometry exposed)
    · have notMember : row.allocId∉after.exposed := by simpa using exposed
      unfold GlobalAddressState.allocIdFromAddr
      unfold_internal ".GlobalAddressState.inverseSearch"
      simp [nextMode,search,present,notMember,exposed,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  · by_cases zero : cut=0
    · subst cut
      unfold GlobalAddressState.allocIdFromAddr
      unfold_internal ".GlobalAddressState.inverseSearch"
      simp [nextMode,search,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
    · have valid : cut-1<after.intToPtrMap.size := by have bounded:=partition.1;omega
      let row:=after.intToPtrMap[cut-1]
      have present : after.intToPtrMap[cut-1]?=some row := Array.getElem?_eq_getElem valid
      have member : row∈after.intToPtrMap := Array.getElem_mem valid
      have known:=nextMetadata row member
      by_cases inside : address-row.address<(sizes row.allocId).bytes
      · by_cases exposed : after.exposed.contains row.allocId=true
        · have shape : row=⟨row.address,row.allocId⟩ := by cases row;rfl
          have geometry : WildcardGeneralHitReborrow.Geometry after.intToPtrMap address row.address row.allocId (sizes row.allocId) :=
            Or.inr ⟨cut-1,by simpa only [Nat.sub_add_cancel (by omega : 1≤cut)] using partition,by simpa only [←shape] using present,inside⟩
          exact False.elim (no_activated_hit before after sizes ordered apart exposedEq rows oldHooks address mode oldMetadata miss _ _ geometry exposed)
        · have notMember : row.allocId∉after.exposed := by simpa using exposed
          unfold GlobalAddressState.allocIdFromAddr
          unfold_internal ".GlobalAddressState.inverseSearch"
          simp [nextMode,search,zero,present,known,inside,notMember,exposed,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
      · unfold GlobalAddressState.allocIdFromAddr
        unfold_internal ".GlobalAddressState.inverseSearch"
        simp [nextMode,search,zero,present,known,inside,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

end DuplicatePrefix.CurrentCallConversionMissFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionMissFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "{name}: {dependency}"
