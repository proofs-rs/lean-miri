import duplicate_prefix.CurrentCallConversionPlan
import duplicate_prefix.CurrentCallConversionTargetAdequacy
namespace DuplicatePrefix.CurrentCallConversionSelectedWeight
open Miri Miri.Input Miri.ABI Miri.Memory
open CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

theorem one_weight_le {α : Type} (items : List α) (weight : α→Nat) (a : α) (member : a∈items) :
    weight a≤(items.map weight).sum := by
  induction items with
  | nil=>simp at member
  | cons first rest ih=>
    rcases List.mem_cons.mp member with equal | member
    · subst first;simp only [List.map_cons,List.sum_cons];omega
    · have tail:=ih member;simp only [List.map_cons,List.sum_cons];omega

/-- Distinct rows contribute twice even when their payload weights coincide. -/
theorem two_weights_le {α : Type} (items : List α) (weight : α→Nat) (a b : α)
    (different : a≠b) (firstMember : a∈items) (secondMember : b∈items) :
    weight a+weight b≤(items.map weight).sum := by
  induction items with
  | nil=>simp at firstMember
  | cons first rest ih=>
    rcases List.mem_cons.mp firstMember with firstEq | firstTail
    · subst first
      rcases List.mem_cons.mp secondMember with secondEq | secondTail
      · exact False.elim (different secondEq.symm)
      · have tail:=one_weight_le rest weight b secondTail
        simp only [List.map_cons,List.sum_cons];omega
    · rcases List.mem_cons.mp secondMember with secondEq | secondTail
      · subst first
        have tail:=one_weight_le rest weight a firstTail
        simp only [List.map_cons,List.sum_cons];omega
      · have tail:=ih firstTail secondTail
        simp only [List.map_cons,List.sum_cons];omega

theorem sum_filterMap {α β : Type} (items : List α) (select : α→Option β) (weight : β→Nat) :
    ((items.filterMap select).map weight).sum=(items.map (fun item=>((select item).map weight).getD 0)).sum := by
  induction items with
  | nil=>rfl
  | cons first rest ih=>cases found : select first <;> simp [found,ih]

def payload (descriptor : GlobalAllocation) : Option (Allocation CtfeProvenance Unit) :=
  match descriptor.payload with
  | some (.memory source)=>some source
  | some (.static definition true false false)=>
      (PreparedReflection.actual.image.initializers.find? (·.1==definition)).map Prod.snd
  | _=>none

def descriptorWeight (weight : Allocation CtfeProvenance Unit→Nat) (descriptor : GlobalAllocation) : Nat :=
  ((payload descriptor).map weight).getD 0

theorem sum_descriptors (before : Before) (weight : Allocation CtfeProvenance Unit→Nat) :
    ((currentConversionInputs before).map weight).sum=(before.memory.globals.toList.map (descriptorWeight weight)).sum :=
  sum_filterMap before.memory.globals.toList payload weight

/-- Real current-payload metadata retains the descriptor identity, rather than
identifying rows merely because their allocation payload values are equal. -/
theorem descriptor_of_current {before : Before} {id : AllocId} {source : Allocation CtfeProvenance Unit}
    (current : CurrentPayload before id source) :
    ∃descriptor∈before.memory.globals.toList,descriptor.allocId=id ∧payload descriptor=some source := by
  cases current with
  | memory found=>exact ⟨_,CurrentCallConversionTargetAdequacy.global_member found,rfl,rfl⟩
  | internalStatic definition found initialized=>
    exact ⟨_,CurrentCallConversionTargetAdequacy.global_member found,rfl,by simp only [payload,initialized,Option.map_some]⟩

theorem current_payload_weight_le {before : Before} {id : AllocId} {source : Allocation CtfeProvenance Unit}
    (weight : Allocation CtfeProvenance Unit→Nat) (current : CurrentPayload before id source) :
    weight source≤((currentConversionInputs before).map weight).sum := by
  obtain ⟨descriptor,member,_,found⟩:=descriptor_of_current current
  have bounded:=one_weight_le before.memory.globals.toList (descriptorWeight weight) descriptor member
  rw [sum_descriptors]
  simpa only [descriptorWeight,found,Option.map_some,Option.getD_some] using bounded

theorem two_current_payloads_weight_le {before : Before} {firstId secondId : AllocId}
    {firstSource secondSource : Allocation CtfeProvenance Unit} (weight : Allocation CtfeProvenance Unit→Nat)
    (different : firstId≠secondId) (first : CurrentPayload before firstId firstSource)
    (second : CurrentPayload before secondId secondSource) :
    weight firstSource+weight secondSource≤((currentConversionInputs before).map weight).sum := by
  obtain ⟨a,aMember,aId,aPayload⟩:=descriptor_of_current first
  obtain ⟨b,bMember,bId,bPayload⟩:=descriptor_of_current second
  have rowsDifferent : a≠b:=by intro equal;apply different;exact aId.symm.trans ((congrArg GlobalAllocation.allocId equal).trans bId)
  have bounded:=two_weights_le before.memory.globals.toList (descriptorWeight weight) a b rowsDifferent aMember bMember
  rw [sum_descriptors]
  simpa only [descriptorWeight,aPayload,bPayload,Option.map_some,Option.getD_some] using bounded

/-- The plan suppresses repeated IDs, not equal payload values. Its initial
current-payload evidence comes from the adopted selected-pointer domain. -/
theorem rows_weight_le (before : Before) (sourceId returnId : Option AllocId)
    (weight : Allocation CtfeProvenance Unit→Nat)
    (current : ∀row∈CurrentCallConversionPlan.rowsFromIds before sourceId returnId,CurrentPayload before row.1 row.2) :
    ((CurrentCallConversionPlan.rowsFromIds before sourceId returnId).map (fun row=>weight row.2)).sum≤
      ((currentConversionInputs before).map weight).sum := by
  have empty (eq : CurrentCallConversionPlan.rowsFromIds before sourceId returnId=[]) :
      ((CurrentCallConversionPlan.rowsFromIds before sourceId returnId).map (fun row=>weight row.2)).sum≤((currentConversionInputs before).map weight).sum:=by rw [eq];simp
  have one (id : AllocId) (source : Allocation CtfeProvenance Unit)
      (eq : CurrentCallConversionPlan.rowsFromIds before sourceId returnId=[(id,source)]) :
      ((CurrentCallConversionPlan.rowsFromIds before sourceId returnId).map (fun row=>weight row.2)).sum≤((currentConversionInputs before).map weight).sum:=by
    have bound:=current_payload_weight_le weight (current (id,source) (by rw [eq];simp))
    simpa only [eq,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using bound
  have two (a b : AllocId) (first second : Allocation CtfeProvenance Unit) (different : a≠b)
      (eq : CurrentCallConversionPlan.rowsFromIds before sourceId returnId=[(a,first),(b,second)]) :
      ((CurrentCallConversionPlan.rowsFromIds before sourceId returnId).map (fun row=>weight row.2)).sum≤((currentConversionInputs before).map weight).sum:=by
    have bound:=two_current_payloads_weight_le weight different (current (a,first) (by rw [eq];simp)) (current (b,second) (by rw [eq];simp))
    simpa only [eq,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using bound
  cases sourceId with
  | none=>
    cases returnId with
    | none=>exact empty rfl
    | some id=>
      cases selected : CurrentCallConversionPlan.payload before id with
      | none=>exact empty (by simp [CurrentCallConversionPlan.rowsFromIds,selected])
      | some source=>exact one id source (by simp [CurrentCallConversionPlan.rowsFromIds,selected])
  | some id=>
    cases selected : CurrentCallConversionPlan.payload before id with
    | none=>
      cases returnId with
      | none=>exact empty (by simp [CurrentCallConversionPlan.rowsFromIds,selected])
      | some other=>
        cases ret : CurrentCallConversionPlan.payload before other with
        | none=>exact empty (by simp [CurrentCallConversionPlan.rowsFromIds,selected,ret])
        | some source=>exact one other source (by simp [CurrentCallConversionPlan.rowsFromIds,selected,ret])
    | some source=>
      cases returnId with
      | none=>exact one id source (by simp [CurrentCallConversionPlan.rowsFromIds,selected])
      | some other=>
        by_cases same : id=other
        · subst other;exact one id source (CurrentCallConversionPlan.same_id_once before id source selected)
        · cases ret : CurrentCallConversionPlan.payload before other with
          | none=>exact one id source (by simp [CurrentCallConversionPlan.rowsFromIds,selected,ret])
          | some result=>exact two id other source result same (CurrentCallConversionPlan.distinct_ids before id other source result same selected ret)
/-- Invert only the finite pure selection; this states initial metadata and
option identity, not success of a query or conversion operation. -/
theorem rowsFromIds_member (before : Before) (sourceId returnId : Option AllocId)
    (row : AllocId × Allocation CtfeProvenance Unit)
    (member : row∈CurrentCallConversionPlan.rowsFromIds before sourceId returnId) :
    CurrentCallConversionPlan.payload before row.1=some row.2 ∧(sourceId=some row.1∨returnId=some row.1) := by
  have mapped (id : AllocId)
      (found : (CurrentCallConversionPlan.payload before id).map (fun value=>(id,value))=some row) :
      CurrentCallConversionPlan.payload before row.1=some row.2 ∧id=row.1:=by
    obtain ⟨value,selected,equal⟩:=Option.map_eq_some_iff.mp found
    have idEq : id=row.1:=congrArg Prod.fst equal
    have valueEq : value=row.2:=congrArg Prod.snd equal
    exact ⟨by rw [←idEq,←valueEq];exact selected,idEq⟩
  unfold CurrentCallConversionPlan.rowsFromIds at member
  dsimp only at member
  rcases List.mem_append.mp member with fromSource | fromReturn
  · obtain ⟨id,chosen,selected⟩:=Option.bind_eq_some_iff.mp (Option.mem_toList.mp fromSource)
    obtain ⟨payload,idEq⟩:=mapped id selected
    exact ⟨payload,Or.inl (chosen.trans (congrArg some idEq))⟩
  · obtain ⟨id,chosen,selected⟩:=Option.bind_eq_some_iff.mp (Option.mem_toList.mp fromReturn)
    split at selected
    · contradiction
    · obtain ⟨payload,idEq⟩:=mapped id selected
      exact ⟨payload,Or.inr (chosen.trans (congrArg some idEq))⟩

end DuplicatePrefix.CurrentCallConversionSelectedWeight
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionSelectedWeight" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved selected-descriptor weight dependency {dependency}"
