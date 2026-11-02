import duplicate_prefix.CurrentCallOwnerRenaming

namespace DuplicatePrefix.CurrentCallSourceHandoff
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateFreezeContentResources
open CurrentCallOwnerRenaming
set_option autoImplicit false
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exactly the source window changes owners; every other charge survives. -/
def content (F : Fragment) (source : Nat) (footprint : Byte → Prop) : Fragment :=
  fun byte owner => if footprint byte then
    if owner = 0 then some ⟨.mut,.active⟩
    else if owner = source + 1 then some ⟨.mut,.suspended⟩
    else shiftContent F byte owner
  else shiftContent F byte owner

@[simp] theorem child_content (F : Fragment) (source : Nat) (footprint : Byte → Prop) (byte : Byte) :
    content F source footprint byte 0 = if footprint byte then some ⟨.mut,.active⟩ else none := by
  simp [content]

theorem parent_content (F : Fragment) (source : Nat) (footprint : Byte → Prop) (byte : Byte) :
    content F source footprint byte (source + 1) =
      if footprint byte then some ⟨.mut,.suspended⟩ else F byte source := by
  simp [content]

theorem other_content (F : Fragment) (source : Nat) (footprint : Byte → Prop) (byte : Byte)
    (owner : Nat) (different : owner ≠ source) :
    content F source footprint byte (owner + 1) = F byte owner := by
  simp [content, different]

private theorem mut_compatible {charge : Charge}
    (compatible : Compatible ⟨.mut,.active⟩ charge) : charge.role = .suspended := by
  rcases compatible with impossible | suspended | ⟨impossible,_⟩
  · cases impossible
  · exact suspended
  · cases impossible

/-- Content validity alone needs no finite support and no operation result.
The parent demand comes only from the exact source window. -/
theorem valid {F : Fragment} (valid : Valid F) (source : Nat) (footprint : Byte → Prop)
    (active : ∀ byte, footprint byte → F byte source = some ⟨.mut,.active⟩) :
    Valid (content F source footprint) := by
  intro byte first second fc sc different firstAt secondAt
  by_cases inside : footprint byte
  · by_cases firstZero : first = 0
    · subst first
      have fcEq : fc = ⟨.mut,.active⟩ := Option.some.inj (by simpa [content,inside] using firstAt.symm)
      subst fc
      cases second with
      | zero => exact False.elim (different rfl)
      | succ second =>
        by_cases parent : second = source
        · subst second
          have eq : sc = ⟨.mut,.suspended⟩ := Option.some.inj (by simpa [content,inside] using secondAt.symm)
          subst sc
          exact Or.inr (Or.inl rfl)
        · have oldAt : F byte second = some sc := by simpa [content,inside,Nat.succ.injEq,parent] using secondAt
          exact Or.inr (Or.inl (mut_compatible (valid byte source second _ _ (Ne.symm parent) (active byte inside) oldAt)))
    · by_cases secondZero : second = 0
      · subst second
        have scEq : sc = ⟨.mut,.active⟩ := Option.some.inj (by simpa [content,inside] using secondAt.symm)
        subst sc
        cases first with
        | zero => exact False.elim (firstZero rfl)
        | succ first =>
          by_cases parent : first = source
          · subst first
            have eq : fc = ⟨.mut,.suspended⟩ := Option.some.inj (by simpa [content,inside] using firstAt.symm)
            subst fc
            exact Or.inl rfl
          · have oldAt : F byte first = some fc := by simpa [content,inside,Nat.succ.injEq,parent] using firstAt
            exact Or.inl (mut_compatible (valid byte source first _ _ (Ne.symm parent) (active byte inside) oldAt))
      · by_cases firstParent : first = source + 1
        · subst first
          have eq : fc = ⟨.mut,.suspended⟩ := Option.some.inj (by simpa [content,inside] using firstAt.symm)
          subst fc
          exact Or.inl rfl
        · by_cases secondParent : second = source + 1
          · subst second
            have eq : sc = ⟨.mut,.suspended⟩ := Option.some.inj (by simpa [content,inside] using secondAt.symm)
            subst sc
            exact Or.inr (Or.inl rfl)
          · exact shiftContent_valid valid byte first second fc sc different
              (by simpa [content,inside,firstZero,firstParent] using firstAt)
              (by simpa [content,inside,secondZero,secondParent] using secondAt)
  · exact shiftContent_valid valid byte first second fc sc different
      (by simpa [content,inside] using firstAt) (by simpa [content,inside] using secondAt)

/-- Owner0 names the actual appended child family; old pointer/family indices
and all annotations retain their exact identities. Child creation/embedding is
proved by the operational borrow witness, separately from this bookkeeping. -/
def install (data : Identities) (source : Nat) (parent : Loan) (child : PointerInstance)
    (footprint : Byte → Prop) : Identities :=
  { data with interpretation :=
    { precise := data.interpretation.precise
      pointers := data.interpretation.pointers.push child
      loans := #[⟨data.interpretation.pointers.size,some (source + 1),parent.depth + 1⟩] ++
        data.interpretation.loans.map shiftLoan
      content := content data.interpretation.content source footprint } }

@[simp] theorem child_loan (data : Identities) (source : Nat) (parent : Loan)
    (child : PointerInstance) (footprint : Byte → Prop) :
    (install data source parent child footprint).interpretation.loans[0]? =
      some ⟨data.interpretation.pointers.size,some (source + 1),parent.depth + 1⟩ := by
  simp [install,Array.getElem?_append]

@[simp] theorem old_loan (data : Identities) (source : Nat) (parent : Loan)
    (child : PointerInstance) (footprint : Byte → Prop) (owner : Nat) :
    (install data source parent child footprint).interpretation.loans[owner + 1]? =
      (data.interpretation.loans[owner]?).map shiftLoan := by
  simp [install,Array.getElem?_append]

@[simp] theorem child_pointer (data : Identities) (source : Nat) (parent : Loan)
    (child : PointerInstance) (footprint : Byte → Prop) :
    (install data source parent child footprint).interpretation.pointers[data.interpretation.pointers.size]? = some child := by
  simp [install]

theorem old_pointer {data : Identities} (source : Nat) (parent : Loan)
    (child : PointerInstance) (footprint : Byte → Prop) {slot : Nat} {pointer : PointerInstance}
    (atSlot : data.interpretation.pointers[slot]? = some pointer) :
    (install data source parent child footprint).interpretation.pointers[slot]? = some pointer := by
  have bound := (Array.getElem?_eq_some_iff.mp atSlot).1
  simpa [install,Array.getElem?_push,bound,Nat.ne_of_lt bound] using atSlot

@[simp] theorem occurrences (data : Identities) (source : Nat) (parent : Loan)
    (child : PointerInstance) (footprint : Byte → Prop) :
    (install data source parent child footprint).occurrences = data.occurrences := rfl
@[simp] theorem attachments (data : Identities) (source : Nat) (parent : Loan)
    (child : PointerInstance) (footprint : Byte → Prop) :
    (install data source parent child footprint).attachments = data.attachments := rfl


theorem stableChoices {data : Identities} (choices : StableChoices data)
    (source : Nat) (parent : Loan) (child : PointerInstance) (footprint : Byte → Prop) :
    StableChoices (install data source parent child footprint) := by
  constructor
  · intro occurrence member
    obtain ⟨pointer,pointerAt,bits⟩ := choices.1 occurrence member
    exact ⟨pointer,old_pointer source parent child footprint pointerAt,bits⟩
  · intro attachment member
    obtain ⟨pointer,precise,pointerAt,id,preciseAt,edge⟩ := choices.2 attachment member
    exact ⟨pointer,precise,old_pointer source parent child footprint pointerAt,id,preciseAt,edge⟩

/-- The source call switches to its child owner0; the actual Bool reservation
retains its old shifted owner and its exact content footprint. -/
def childCall (call : CallLoans) : CallLoans :=
  { call with sourceOwner := 0, returnOwner := call.returnOwner + 1 }

theorem call_handoff {data : Identities} {call : CallLoans}
    (resources : Valid data.interpretation.content) (claims : Claims data.interpretation call)
    (parent : Loan) (child : PointerInstance) :
    let installed := install data call.sourceOwner parent child
      (Window call.sourceId call.sourceOffset call.length)
    Valid installed.interpretation.content ∧ Claims installed.interpretation (childCall call) := by
  dsimp only
  refine ⟨valid resources call.sourceOwner _ (fun byte inside => (claims.2.1 byte).mpr inside),?_,?_,?_⟩
  · simp [childCall]
  · intro byte
    change (if Window call.sourceId call.sourceOffset call.length byte then
      some (⟨.mut,.active⟩ : Charge) else none) = some ⟨.mut,.active⟩ ↔ _
    by_cases inside : Window call.sourceId call.sourceOffset call.length byte <;> simp [inside,childCall]
  · intro byte
    change content data.interpretation.content call.sourceOwner _ byte (call.returnOwner + 1) = _ ↔ _
    rw [other_content _ _ _ _ _ (Ne.symm claims.1)]
    exact claims.2.2 byte

/-- The new logical loan is linked to exactly the old parent loan, reindexed;
its pointer field uses the appended family and every old family stays intact. -/
theorem parent_loan {data : Identities} (source : Nat) (parent : Loan)
    (child : PointerInstance) (footprint : Byte → Prop)
    (parentAt : data.interpretation.loans[source]? = some parent) :
    (install data source parent child footprint).interpretation.loans[source + 1]? = some (shiftLoan parent) := by
  simp [parentAt]

end
end DuplicatePrefix.CurrentCallSourceHandoff
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSourceHandoff.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved source handoff dependency {dependency}"
