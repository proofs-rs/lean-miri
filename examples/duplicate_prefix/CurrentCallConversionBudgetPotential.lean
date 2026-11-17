import Lean
import Miri.Memory.AllocAddresses.GlobalState
namespace DuplicatePrefix.CurrentCallConversionBudgetPotential
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

def misses (state : GlobalAddressState) (ids : List AllocId) : Nat :=
  (ids.filter (fun id=>(state.baseAddr.find? (fun row=>row.allocId==id)).isNone)).length

private theorem filter_mono (ids : List AllocId) (old next : AllocId→Bool)
    (preserved : ∀id∈ids,next id=true→old id=true) : (ids.filter next).length≤(ids.filter old).length := by
  induction ids with
  | nil=>exact Nat.le_refl _
  | cons id rest ih=>
    have tail:=ih (fun q member=>preserved q (by simp [member]))
    have head:=preserved id (by simp)
    cases a : old id <;> cases b : next id <;> simp [a,b] at * <;> omega

private theorem filter_drop (ids : List AllocId) (old next : AllocId→Bool)
    (preserved : ∀id∈ids,next id=true→old id=true)
    (id : AllocId) (member : id∈ids) (was : old id=true) (now : next id=false) :
    (ids.filter next).length+1≤(ids.filter old).length := by
  induction ids with
  | nil=>simp at member
  | cons first rest ih=>
    have tailMono : ∀q∈rest,next q=true→old q=true:=fun q hit=>preserved q (by simp [hit])
    rcases List.mem_cons.mp member with equal | member
    · subst first
      have tail:=filter_mono rest old next tailMono
      simp [was,now]
      omega
    · have tail:=ih tailMono member
      have head:=preserved first (by simp)
      cases a : old first <;> cases b : next first <;> simp [a,b] at * <;> omega

/-- Preserving existing first-match base hits cannot increase the finite miss
potential. These scalar cache facts are supplied by the actual address step. -/
theorem nonincrease (before after : GlobalAddressState) (ids : List AllocId)
    (preserved : ∀id entry,before.baseAddr.find? (fun row=>row.allocId==id)=some entry→
      after.baseAddr.find? (fun row=>row.allocId==id)=some entry) : misses after ids≤misses before ids := by
  apply filter_mono
  intro id member miss
  cases old : before.baseAddr.find? (fun row=>row.allocId==id) with
  | none=>rfl
  | some entry=>rw [preserved id entry old] at miss;contradiction

/-- A successful previously uncached target pays for at least one finite
list occurrence, even when the target list contains duplicates. -/
theorem drop (before after : GlobalAddressState) (ids : List AllocId) (id : AllocId) (member : id∈ids)
    (uncached : before.baseAddr.find? (fun row=>row.allocId==id)=none)
    (preserved : ∀query entry,before.baseAddr.find? (fun row=>row.allocId==query)=some entry→
      after.baseAddr.find? (fun row=>row.allocId==query)=some entry)
    (entry : BaseAddressEntry) (cached : after.baseAddr.find? (fun row=>row.allocId==id)=some entry) :
    misses after ids+1≤misses before ids := by
  have monotone : ∀query∈ids,(after.baseAddr.find? (fun row=>row.allocId==query)).isNone=true→
      (before.baseAddr.find? (fun row=>row.allocId==query)).isNone=true:=by
    intro query hit miss
    cases old : before.baseAddr.find? (fun row=>row.allocId==query) with
    | none=>rfl
    | some entry=>rw [preserved query entry old] at miss;contradiction
  exact filter_drop ids _ _ monotone id member (by rw [uncached];rfl) (by rw [cached];rfl)

/-- The charged cursor advance is offset by the actual miss-potential drop. -/
theorem charge (before after : GlobalAddressState) (ids : List AllocId) (id : AllocId) (member : id∈ids)
    (uncached : before.baseAddr.find? (fun row=>row.allocId==id)=none)
    (preserved : ∀query entry,before.baseAddr.find? (fun row=>row.allocId==query)=some entry→
      after.baseAddr.find? (fun row=>row.allocId==query)=some entry)
    (entry : BaseAddressEntry) (cached : after.baseAddr.find? (fun row=>row.allocId==id)=some entry)
    (cursor nextCursor charge : Nat) (advance : nextCursor≤cursor+charge) :
    nextCursor+misses after ids*charge≤cursor+misses before ids*charge := by
  have decreased:=drop before after ids id member uncached preserved entry cached
  have weighted : misses after ids*charge+charge≤misses before ids*charge:=by
    simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right charge decreased
  omega

theorem uncharged (before after : GlobalAddressState) (ids : List AllocId)
    (preserved : ∀query entry,before.baseAddr.find? (fun row=>row.allocId==query)=some entry→
      after.baseAddr.find? (fun row=>row.allocId==query)=some entry)
    (cursor nextCursor charge : Nat) (advance : nextCursor≤cursor) :
    nextCursor+misses after ids*charge≤cursor+misses before ids*charge :=
  Nat.add_le_add advance (Nat.mul_le_mul_right charge (nonincrease before after ids preserved))

/-- Any separately retained strict end margin transports along the weighted
bound; no stronger arithmetic reserve is invented. -/
theorem margin (cursor nextCursor oldMisses newMisses charge slack limit : Nat)
    (bounded : nextCursor+newMisses*charge≤cursor+oldMisses*charge)
    (room : cursor+oldMisses*charge+slack<limit) : nextCursor+newMisses*charge+slack<limit :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right bounded slack) room
end DuplicatePrefix.CurrentCallConversionBudgetPotential
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionBudgetPotential" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved conversion budget dependency {dependency}"
