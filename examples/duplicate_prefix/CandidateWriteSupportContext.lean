import duplicate_prefix.CandidateSixNodeCertificate
import duplicate_prefix.RootCompilerFacts
import duplicate_prefix.GeneralBorrowStructuralHistorySeed

/-! A fully explicit static context for testing the UNADOPTED candidate's
implication to raw Write-support formation. No execution or ordinary-validity
claim is made; actual-machine bindings are supplied in the boundary module. -/
namespace DuplicatePrefix.CandidateWriteSupportContext
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Interpreter CandidateStableCallOwnership
set_option autoImplicit false

def sourceId : AllocId := ⟨1,by decide⟩
def returnId : AllocId := ⟨2,by decide⟩
def sourceAllocation : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[11,22] Align.ONE .Mut).toOption.get (by decide)).withExtra S05DiagnosticFnEntryRead.tree
def returnAllocation : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[0] Align.ONE .Mut).toOption.get (by decide)).withExtra
    (BorrowTree.new (S05DiagnosticFnEntryRead.tag 7) (Size.ofBytes 1))
def sourcePointer : Pointer Provenance :=
  ⟨Size.ofBytes 4096,.concrete sourceId (S05DiagnosticFnEntryRead.tag 6)⟩
def returnPointer : Pointer Provenance :=
  ⟨Size.ofBytes 8192,.concrete returnId (S05DiagnosticFnEntryRead.tag 7)⟩
def returnPrecise : PreciseAllocation := ⟨⟨#[none],#[0]⟩,#[#[⟨.Unique,true,.None⟩]]⟩
def interpretation : Interpretation where
  precise := #[(sourceId,CandidateSixNodeCertificate.precise),(returnId,returnPrecise)]
  pointers := #[⟨sourceId,sourcePointer,S05DiagnosticFnEntryRead.ix 5⟩,
    ⟨returnId,returnPointer,S05DiagnosticFnEntryRead.ix 0⟩]
  loans := #[⟨0,none,0⟩,⟨1,none,0⟩]
  content := fun byte owner =>
    if owner=0 then if byte.1=sourceId ∧ byte.2<2 then some ⟨.mut,.active⟩ else none
    else if owner=1 then if byte.1=returnId ∧ byte.2=0 then some ⟨.ret,.active⟩ else none
    else none

def call : CallLoans := ⟨0,1,sourceId,0,2,returnId,0⟩
def world : World := #[(sourceId,sourceAllocation),(returnId,returnAllocation)]
def argument : DuplicatePrefixSliceArgument.Argument := .pointer sourcePointer
def place : MPlaceTy Provenance :=
  ⟨⟨returnPointer.withOptionalProvenance,.none,none⟩,RootCompilerFacts.boolLayout⟩

private def returnNode : TreeNode := ⟨S05DiagnosticFnEntryRead.tag 7,none,#[],.Disabled,.None,false,none⟩
private def returnLocation : LocationTree := ⟨⟨#[some ⟨.Unique,true,.None⟩]⟩,{}⟩
private theorem return_nodes (index : UniIndex) (node : TreeNode)
    (present : returnAllocation.extra.nodes.get index = some node) :
    index=S05DiagnosticFnEntryRead.ix 0 ∧ node=returnNode := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid returnAllocation.extra.nodes index node present
  change index.toNat < 1 at bound
  have same := GeneralBorrowNodeUpdate.index_injective index (S05DiagnosticFnEntryRead.ix 0) (by change index.toNat=0;omega)
  subst index
  exact ⟨rfl,Option.some.inj present.symm⟩

private theorem return_completes : Completes returnAllocation.extra returnPrecise.completion := by
  refine ⟨rfl,rfl,by decide,?_,?_,?_,?_⟩
  · intro position root listed
    have bound := (Array.getElem?_eq_some_iff.mp listed).1
    change position < 1 at bound
    have zero : position=0 := by omega
    subst position
    have same : root=S05DiagnosticFnEntryRead.ix 0 := Option.some.inj listed.symm
    subst root
    exact ⟨returnNode,rfl,rfl⟩
  · intro index node present
    obtain ⟨rfl,rfl⟩ := return_nodes index node present
    refine ⟨rfl,?_,?_,by decide⟩
    · intro child
      constructor
      · intro member;cases member
      · rintro ⟨childNode,found,edge⟩
        obtain ⟨_,rfl⟩ := return_nodes child childNode found
        cases edge
    · intro parent edge;cases edge
  · intro position root listed
    have bound := (Array.getElem?_eq_some_iff.mp listed).1
    change position < 1 at bound
    have zero : position=0 := by omega
    subst position
    have same : root=S05DiagnosticFnEntryRead.ix 0 := Option.some.inj listed.symm
    subst root
    rfl
  · intro child parent edge
    have bound := (Array.getElem?_eq_some_iff.mp edge).1
    change child.toNat < 1 at bound
    have same := GeneralBorrowNodeUpdate.index_injective child (S05DiagnosticFnEntryRead.ix 0) (by change child.toNat=0;omega)
    subst child
    cases edge

private theorem return_profile : GeneralBorrowLocationSifaConsistency.Profile returnAllocation.extra returnLocation CandidateSixNodeCertificate.held := by
  constructor
  · intro index node present
    obtain ⟨rfl,rfl⟩ := return_nodes index node present
    exact ⟨.None,rfl,by decide⟩
  · intro index absent
    have outside : 1 ≤ index.toNat := by
      by_cases bound : index.toNat < 1
      · have same := GeneralBorrowNodeUpdate.index_injective index (S05DiagnosticFnEntryRead.ix 0) (by change index.toNat=0;omega)
        subst index;cases absent
      · omega
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by change 1 ≤ index.toNat;exact outside)]

private theorem return_coherent : GeneralBorrowExposureCardinality.LocationCoherent returnAllocation.extra returnLocation CandidateSixNodeCertificate.held := by
  intro query kind
  have entries : returnAllocation.extra.nodes.entries.toList = [(S05DiagnosticFnEntryRead.ix 0,returnNode)] := by with_unfolding_all rfl
  have counts : GeneralBorrowExposureCardinality.cardinality returnAllocation.extra.nodes
      (GeneralBorrowExposureCardinality.effective returnLocation CandidateSixNodeCertificate.held) query kind = 0 := by
    unfold GeneralBorrowExposureCardinality.cardinality
    rw [entries]
    simp [GeneralBorrowExposureCardinality.contributes,returnNode]
  rw [counts]
  cases kind <;> rfl

private theorem return_refines : Refines returnAllocation CandidateSixNodeCertificate.held returnPrecise := by
  refine ⟨return_completes,rfl,?_,?_,?_⟩
  · intro entry member
    have same : entry = #[⟨.Unique,true,.None⟩] := by simpa [returnPrecise] using member
    subst entry;rfl
  · intro byte inside
    have zero : byte=0 := by change byte < 1 at inside;omega
    subst byte
    exact ⟨⟨⟨0,1⟩,returnLocation⟩,by decide,by decide,by decide⟩
  · intro segment stored
    have same : segment = ⟨⟨0,1⟩,returnLocation⟩ := by
      change segment ∈ [⟨⟨0,1⟩,returnLocation⟩] at stored
      exact List.mem_singleton.mp stored
    subst segment
    refine ⟨by decide,by decide,return_coherent,return_profile,?_⟩
    intro byte lower upper index node present
    have zero : byte=0 := by change byte < 1 at upper;omega
    subst byte
    obtain ⟨rfl,rfl⟩ := return_nodes index node present
    exact ⟨rfl,rfl,fun _ _ rights => rights⟩

private theorem return_rights : LoanRights returnAllocation CandidateSixNodeCertificate.held returnPrecise
    ⟨returnId,returnPointer,S05DiagnosticFnEntryRead.ix 0⟩ 0 .ret := by
  intro index node present
  obtain ⟨rfl,rfl⟩ := return_nodes index node present
  constructor <;> intro _
  all_goals change Allows ⟨.Unique,true,.None⟩ false .Write _
  all_goals unfold Allows GeneralBorrowExposedConditionalWritePermissions.Compatible
  all_goals decide

private theorem content_cases (byte : CandidateFreezeContentResources.Byte) (owner : Nat)
    (charge : CandidateFreezeContentResources.Charge) (found : interpretation.content byte owner = some charge) :
    (owner=0 ∧ byte.1=sourceId ∧ byte.2<2 ∧ charge=⟨.mut,.active⟩) ∨
    (owner=1 ∧ byte.1=returnId ∧ byte.2=0 ∧ charge=⟨.ret,.active⟩) := by
  by_cases zero : owner=0
  · subst owner
    by_cases inside : byte.1=sourceId ∧ byte.2<2
    · exact Or.inl ⟨rfl,inside.1,inside.2,Option.some.inj (by simpa [interpretation,inside] using found.symm)⟩
    · simp [interpretation,inside] at found
  · by_cases one : owner=1
    · subst owner
      by_cases inside : byte.1=returnId ∧ byte.2=0
      · exact Or.inr ⟨rfl,inside.1,inside.2,Option.some.inj (by simpa [interpretation,inside] using found.symm)⟩
      · simp [interpretation,inside] at found
    · simp [interpretation,zero,one] at found

private theorem content_valid : CandidateFreezeContentResources.Valid interpretation.content := by
  intro byte first second firstCharge secondCharge different firstAt secondAt
  rcases content_cases byte first firstCharge firstAt with ⟨rfl,left,bound,rfl⟩ | ⟨rfl,left,bound,rfl⟩
  all_goals rcases content_cases byte second secondCharge secondAt with ⟨rfl,right,other,rfl⟩ | ⟨rfl,right,other,rfl⟩
  all_goals simp_all [sourceId,returnId]

/-- Every clause of the current UNADOPTED interpretation predicate is certified. -/
theorem interprets : Interprets world CandidateSixNodeCertificate.held interpretation := by
  refine ⟨by decide,by decide,?_,?_,?_,content_valid,?_,?_⟩
  · intro id allocation live
    change (id,allocation) ∈ [(sourceId,sourceAllocation),(returnId,returnAllocation)] at live
    simp only [List.mem_cons,List.not_mem_nil,or_false] at live
    rcases live with same | same
    · cases same
      exact ⟨CandidateSixNodeCertificate.precise,by simp [interpretation],CandidateSixNodeCertificate.refines _ rfl rfl⟩
    · cases same
      exact ⟨returnPrecise,by simp [interpretation],return_refines⟩
  · intro id precise stored
    change (id,precise) ∈ [(sourceId,CandidateSixNodeCertificate.precise),(returnId,returnPrecise)] at stored
    simp only [List.mem_cons,List.not_mem_nil,or_false] at stored
    rcases stored with same | same
    · cases same
      exact ⟨sourceAllocation,by simp [Present,world],CandidateSixNodeCertificate.refines _ rfl rfl⟩
    · cases same
      exact ⟨returnAllocation,by simp [Present,world],return_refines⟩
  · intro pointer member
    change pointer ∈ [⟨sourceId,sourcePointer,S05DiagnosticFnEntryRead.ix 5⟩,⟨returnId,returnPointer,S05DiagnosticFnEntryRead.ix 0⟩] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same
    · subst pointer
      exact ⟨sourceAllocation,by simp [Present,world],S05DiagnosticFnEntryRead.w,rfl,rfl,rfl,rfl⟩
    · subst pointer
      exact ⟨returnAllocation,by simp [Present,world],returnNode,rfl,rfl,rfl,rfl⟩
  · intro owner loan found
    have bound := (Array.getElem?_eq_some_iff.mp found).1
    change owner < 2 at bound
    have choices : owner=0 ∨ owner=1 := by omega
    rcases choices with rfl | rfl
    all_goals have same : loan = _ := Option.some.inj found.symm
    all_goals subst loan
    all_goals refine ⟨⟨_,rfl⟩,?_⟩
    all_goals intro parent edge
    all_goals cases edge
  · intro byte owner charge found
    rcases content_cases byte owner charge found with ⟨rfl,idEq,bound,rfl⟩ | ⟨rfl,idEq,zero,rfl⟩
    · refine ⟨⟨0,none,0⟩,⟨sourceId,sourcePointer,S05DiagnosticFnEntryRead.ix 5⟩,sourceAllocation,CandidateSixNodeCertificate.precise,
        rfl,rfl,idEq.symm,?_,bound,?_,?_,?_⟩
      · rw [idEq];simp [Present,world]
      · rw [idEq];simp [interpretation]
      · intro _;exact CandidateSixNodeCertificate.source_rights sourceAllocation rfl sourceId 4096 byte.2 bound
      · intro parent edge;cases edge
    · refine ⟨⟨1,none,0⟩,⟨returnId,returnPointer,S05DiagnosticFnEntryRead.ix 0⟩,returnAllocation,returnPrecise,
        rfl,rfl,idEq.symm,?_,?_,?_,?_,?_⟩
      · rw [idEq];simp [Present,world]
      · rw [zero];decide
      · rw [idEq];simp [interpretation]
      · intro _;rw [zero];exact return_rights
      · intro parent edge;cases edge

theorem claims : Claims interpretation call := by
  refine ⟨by decide,?_,?_⟩
  · intro byte
    simp [interpretation,call,Window]
  · intro byte
    simp [interpretation,call,Window]

theorem source_graph : GeneralBorrowStructuralHistoryState.GraphState sourceAllocation.extra := CandidateSixNodeCertificate.graph
theorem source_order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceAllocation.extra := CandidateSixNodeCertificate.order
theorem return_graph : GeneralBorrowStructuralHistoryState.GraphState returnAllocation.extra :=
  (GeneralBorrowStructuralHistorySeed.initial (S05DiagnosticFnEntryRead.tag 7) (Size.ofBytes 1)).toGraphState
theorem return_order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder returnAllocation.extra := by
  intro index node present parent parentNode edge parentPresent
  obtain ⟨_,rfl⟩ := return_nodes index node present
  cases edge

end DuplicatePrefix.CandidateWriteSupportContext

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateWriteSupportContext." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved candidate context dependency {dependency}"
