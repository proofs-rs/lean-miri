import duplicate_prefix.CurrentCallConversionMetadataBounds
import duplicate_prefix.GlobalAddressBaseCacheFormation

namespace DuplicatePrefix.CurrentCallConversionCacheFrames
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem filter_mono (ids : List AllocId) (old next : AllocId→Bool)
    (preserved : ∀id∈ids,next id=true→old id=true) : (ids.filter next).length≤(ids.filter old).length := by
  induction ids with
  | nil => exact Nat.le_refl _
  | cons id rest ih =>
    have tail:=ih (fun q member=>preserved q (by simp [member]))
    have head:=preserved id (by simp)
    cases a : old id <;> cases b : next id <;> simp [a,b] at * <;> omega

private theorem filter_drop (ids : List AllocId) (old next : AllocId→Bool)
    (preserved : ∀id∈ids,next id=true→old id=true)
    (id : AllocId) (member : id∈ids) (was : old id=true) (now : next id=false) :
    (ids.filter next).length+1≤(ids.filter old).length := by
  induction ids with
  | nil => simp at member
  | cons first rest ih =>
    have tailMono : ∀q∈rest,next q=true→old q=true:=fun q hit=>preserved q (by simp [hit])
    rcases List.mem_cons.mp member with equal | member
    · subst first
      have tail:=filter_mono rest old next tailMono
      simp [was,now]
      omega
    · have tail:=ih tailMono member
      have head:=preserved first (by simp)
      cases a : old first <;> cases b : next first <;> simp [a,b] at * <;> omega

/-- One actual root-tag request preserves every cached root. A missing request
costs exactly one tag, while its finite target-list miss potential drops. -/
theorem root (global : GlobalState) (ids : List AllocId) (id : AllocId) (member : id∈ids)
    (room : global.nextPointerTag.value<18446744073709551615) :
    ∃ next tag,global.rootPointerTag id=.ok (next,tag) ∧next.rootTag? id=some tag ∧
      (∀query old,global.rootTag? query=some old→next.rootTag? query=some old) ∧
      next.nextPointerTag.value.toNat+(ids.filter (fun query=>(next.rootTag? query).isNone)).length≤
        global.nextPointerTag.value.toNat+(ids.filter (fun query=>(global.rootTag? query).isNone)).length := by
  cases cached : global.rootTag? id with
  | some tag =>
    exact ⟨global,tag,GlobalState.rootPointerTag_existing global id tag cached,cached,fun _ _ hit=>hit,Nat.le_refl _⟩
  | none =>
    let next : GlobalState:={GeneralBorrowFnEntryRegistration.advanced global room with
      rootPointerTags:=global.rootPointerTags.push (id,global.nextPointerTag)}
    have absent : global.rootPointerTags.find? (fun row=>row.1==id)=none:=by
      cases found : global.rootPointerTags.find? (fun row=>row.1==id) with
      | none => rfl
      | some row => simp only [GlobalState.rootTag?,found,Option.map_some] at cached;contradiction
    have operation : global.rootPointerTag id=.ok (next,global.nextPointerTag):=by
      simp only [GlobalState.rootPointerTag,cached,TypedRetagEmpty.allocate_tag global room,bind,Except.bind,pure,Except.pure]
      rfl
    have present : next.rootTag? id=some global.nextPointerTag:=by
      simp [GlobalState.rootTag?,next,Array.find?_push,absent]
    have preserved : ∀query old,global.rootTag? query=some old→next.rootTag? query=some old:=by
      intro query old hit
      unfold GlobalState.rootTag? at hit ⊢
      cases found : global.rootPointerTags.find? (fun row=>row.1==query) with
      | none => simp [found] at hit
      | some row => simpa only [next,GeneralBorrowFnEntryRegistration.advanced,Array.find?_push,found,Option.some_or,Option.map_some] using hit
    have mono : ∀query∈ids,(next.rootTag? query).isNone=true→(global.rootTag? query).isNone=true:=by
      intro query hit miss
      cases old : global.rootTag? query with
      | none => rfl
      | some tag => rw [preserved query tag old] at miss;contradiction
    have dropped:=filter_drop ids (fun query=>(global.rootTag? query).isNone) (fun query=>(next.rootTag? query).isNone)
      mono id member (by rw [cached];rfl) (by rw [present];rfl)
    have counter : next.nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+1:=
      GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    exact ⟨next,global.nextPointerTag,operation,present,preserved,by omega⟩

/-- Even a cache-insertion error prefix retains every old first-match base
row. This is a frame fact about the real cache operation, not a success gate. -/
theorem base_preserved (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (query : AllocId) (base : BaseAddressEntry)
    (hit : state.baseAddr.find? (fun row=>row.allocId==query)=some base) :
    (state.cacheAddress id address).state.baseAddr.find? (fun row=>row.allocId==query)=some base := by
  cases cached : state.baseAddr.find? (fun row=>row.allocId==id) with
  | some known =>
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [cached,Option.map_some]
    exact hit
  | none =>
    have different : query≠id:=by intro equal;subst query;rw [cached] at hit;contradiction
    have changed:=GlobalAddressBaseCacheFormation.base_insert_other state.baseAddr id query address different
    have preserved:=changed.trans hit
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    unfold_internal ".GlobalAddressState.insertBase"
    simp only [cached,Option.map_none]
    split
    · exact preserved
    · split
      · split <;> exact preserved
      · split <;> exact preserved

/-- An initially uncached target obtains its base row in the actual cache
state, including prefixes that subsequently report an inverse-index error. -/
theorem base_inserted (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) :
    (state.cacheAddress id address).state.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,address⟩ := by
  have inserted:=GlobalAddressBaseCacheFormation.base_insert_same state.baseAddr id address
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.insertBase"
  simp only [uncached,Option.map_none]
  split
  · exact inserted
  · split
    · split <;> exact inserted
    · split <;> exact inserted

end DuplicatePrefix.CurrentCallConversionCacheFrames
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionCacheFrames" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual conversion-cache dependency {dependency}"
