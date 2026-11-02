import duplicate_prefix.CurrentCallOptionalCellRange
import duplicate_prefix.GeneralBorrowForestFnEntry

/-! Exact necessity-packet FnEntry consumption. The actual registered Read
feeds the actual child constructor. No total completion or successful-operation
premise is supplied by a caller. Ordinary coverage and typed/MIR execution are
separate from this finite borrow-layer consumer. -/
namespace DuplicatePrefix.CurrentCallOptionalCellFnEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentGrantResources
open GeneralRangeMapOrigins GeneralRangeMapState
open CurrentCallNeutralCellNecessity
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option cbv.warning false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
noncomputable section

def freshTag : BorTag := ⟨4,by decide⟩
def global : GlobalState := {nextPointerTag := freshTag}
def advanced : GlobalState := {global with nextPointerTag := ⟨5,by decide⟩}
def registration : GlobalState × FrameState :=
  advanced.addProtector {} sourceId freshTag .StrongProtector

def read : BorrowTree.BorrowTreeAccessResult :=
  GeneralBorrowForestProtected.read sourceTree registration.1.protectedTags sourceTag 0 2 .VisitChildrenOfAccessed

def constructed : BorrowTree.ChildInsertResult :=
  read.tree.newChild (Size.ofBytes 0) (.concrete sourceTag) freshTag
    (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true

def output : GeneralBorrowForestFnEntry.Output :=
  ⟨registration.1,registration.2,freshTag,read,constructed⟩

def childIndex : UniIndex := ⟨2⟩
def extended : Completion := ⟨#[none,none,some primary],#[0,0,1]⟩

def readRow : LocationTree := ((read.tree.locations.entries[0]?).map (·.data)).getD row
def childRow : LocationTree := ((constructed.tree.locations.entries[0]?).map (·.data)).getD row

/-- Cell shape is a derived effective-state invariant on EVERY actual stored
row; a missing entry is decoded from the actual node's lazy default. SIFA is
intentionally unconstrained. -/
def EffectiveCell (tree : BorrowTree) : Prop :=
  Every (fun location => (RawState location ambient cellNode).permission = .Cell ∧
    (RawState location ambient cellNode).accessed = false) tree.locations

theorem actual_operation :
    GeneralBorrowForestFnEntry.operation sourceTree global {} sourceId sourceTag 0 2 .VisitChildrenOfAccessed = .ok output := by
  have room : global.nextPointerTag.value < 18446744073709551615 := by decide
  simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag global room,
    Except.pure,pure]
  rfl

private theorem index_inj {left right : UniIndex} (same : left.toNat = right.toNat) : left = right := by
  cases left; cases right; congr; exact UInt32.toNat_inj.mp same

private def source_depth : GeneralBorrowExposure.ParentDepth sourceTree.nodes where
  depth := fun _ => 0
  bounded := by intro index node found; exact Nat.zero_le _
  parent := by
    intro index node found parent edge
    have valid := GeneralBorrowNodeUpdate.lookup_valid sourceTree.nodes index node found
    have bound : index.toNat < 2 := valid
    rcases (show index.toNat = 0 ∨ index.toNat = 1 by omega) with zero | one
    · have same : index = primary := index_inj zero
      subst index
      have nodeEq : node = rootNode sourceTag := Option.some.inj found.symm
      subst node
      cases edge
    · have same : index = ambient := index_inj one
      subst index
      have nodeEq : node = cellNode := Option.some.inj found.symm
      subst node
      cases edge

/-- The derived actual leaf effect supplies the effective Cell invariant and
outside row frame. The exact packet computation only connects this callback
to the actual registered Read; it does not assume callback success. -/
theorem read_callback_preservation :
    (RawState readRow ambient cellNode).permission = .Cell ∧
    (RawState readRow ambient cellNode).accessed = false ∧
    readRow.exposedCache = row.exposedCache ∧
    GeneralBorrowWildcardVirtualLeafFrame.Frame ambient row readRow := by
  have initialOwned : GeneralBorrowPermissions.ForeignOwned
      (GeneralBorrowWildcardVirtualLeaf.effective row ambient cellNode)
      (registration.1.protectedTags.contains cellNode.tag) := by
    unfold GeneralBorrowPermissions.ForeignOwned
    decide_cbv
  obtain ⟨after,actual,_,frame,permission,accessed,cache⟩ :=
    CurrentCallOptionalCellAccess.cell_effect sourceTree row ambient cellNode (some sourceTag) .Read
      registration.1.protectedTags (by rfl) (by rfl) source_depth (by rfl)
      (.inr (by decide_cbv)) (by rfl) (by rfl) (by decide_cbv) initialOwned
  have selected : readRow = (sourceTree.performWildcardAccessAt row ambient (some sourceTag) .Read
      registration.1.protectedTags true).location := by decide_cbv
  rw [actual] at selected
  change readRow = after at selected
  subst after
  exact ⟨permission,accessed,cache,frame⟩

/-- This records actual materialization: the unvisited lazy Cell default was
None; after the real Read it is a stored Cell,false,Read. -/
theorem read_cell_materialized :
    row.perms.get ambient = none ∧
    readRow.perms.get ambient = some ⟨.Cell,false,.Read⟩ ∧
    read.tree.nodes = sourceTree.nodes ∧ read.tree.roots = sourceTree.roots ∧
    read.tree.tagMapping = sourceTree.tagMapping := by decide_cbv

theorem read_effective_cell : read.status = .Completed ∧ EffectiveCell read.tree := by
  refine ⟨by decide_cbv,?_⟩
  intro position valid
  have length : read.tree.locations.entries.size = 1 := by decide_cbv
  have zero : position = 0 := by omega
  subst position
  have value : read.tree.locations.entries[0].data = readRow := by
    simp only [readRow,Array.getElem?_eq_getElem valid,Option.map_some,Option.getD_some]
  rw [value]
  exact ⟨read_callback_preservation.1,read_callback_preservation.2.1⟩

/-- No ambient ghost edge is introduced. ONLY the real fresh child is attached
to the original concrete grant, with the SAME original parent map prefix. -/
theorem real_child :
    constructed.outcome = .ok () ∧ constructed.tree.indexOfTag freshTag = some childIndex ∧
    constructed.tree.nodes.get ambient = some cellNode ∧
    (constructed.tree.nodes.get childIndex).map (·.parent) = some (some primary) ∧
    extended.parents[ambient.toNat]? = some none ∧
    extended.parents[childIndex.toNat]? = some (some primary) ∧
    constructed.tree.roots = sourceTree.roots ∧
    registration.1.protectedTags.get freshTag = some .StrongProtector := by decide_cbv

theorem constructed_effective_cell : EffectiveCell constructed.tree := by
  intro position valid
  have length : constructed.tree.locations.entries.size = 1 := by decide_cbv
  have zero : position = 0 := by omega
  subst position
  have value : constructed.tree.locations.entries[0].data = childRow := by
    simp only [childRow,Array.getElem?_eq_getElem valid,Option.map_some,Option.getD_some]
  rw [value]
  have state : RawState childRow ambient cellNode = ⟨.Cell,false,.Read⟩ := by decide_cbv
  rw [state]
  exact ⟨rfl,rfl⟩

private theorem child_ancestors (index : UniIndex) (below : Below extended index childIndex) :
    index = childIndex ∨ index = primary := by
  cases below with
  | refl => exact .inl rfl
  | @step parent _ edge prior =>
    have fixed : extended.parents[childIndex.toNat]? = some (some primary) := by decide
    have same : parent = primary := Option.some.inj (Option.some.inj (edge.symm.trans fixed))
    subst parent
    cases prior with
    | refl => exact .inr rfl
    | step edge _ => simp [extended,primary,UniIndex.toNat] at edge

/-- The active source footprint is delegated to the REAL child. The incoming
parent grant is not asserted simultaneously active under its Strong child. -/
theorem child_resources :
    CurrentCallOptionalCellAccess.RowResources constructed.tree extended registration.1.protectedTags childIndex childRow := by
  intro index node found
  have bounded := GeneralBorrowNodeUpdate.lookup_valid constructed.tree.nodes index node found
  change index.toNat < constructed.tree.nodes.size at bounded
  have size : constructed.tree.nodes.size = 3 := by decide_cbv
  have cases : index = primary ∨ index = ambient ∨ index = childIndex := by
    have possibilities : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 := by omega
    rcases possibilities with zero | one | two
    · exact .inl (index_inj zero)
    · exact .inr (.inl (index_inj one))
    · exact .inr (.inr (index_inj two))
  constructor
  · intro below
    rcases child_ancestors index below with same | same
    · subst index
      have slot : childRow.perms.get childIndex = some ⟨.ReservedFrz false,true,.None⟩ := by decide_cbv
      unfold RawState
      rw [slot]
      simp [tokens,denote]
    · subst index
      have slot : childRow.perms.get primary = some ⟨.Unique,true,.None⟩ := by decide_cbv
      unfold RawState
      rw [slot]
      simp [tokens,denote]
  · intro clash
    rcases cases with same | same | same
    · subst index
      have tagAt : (constructed.tree.nodes.get primary).map (·.tag) = some sourceTag := by decide_cbv
      rw [found] at tagAt
      have tag : node.tag = sourceTag := Option.some.inj tagAt
      have unheld : registration.1.protectedTags.contains node.tag = false := by rw [tag]; decide_cbv
      rw [unheld] at clash
      simp [denote,CandidateCurrentGrantResources.guard,Clash] at clash
    · subst index
      have tagAt : (constructed.tree.nodes.get ambient).map (·.tag) = some cellTag := by decide_cbv
      rw [found] at tagAt
      have tag : node.tag = cellTag := Option.some.inj tagAt
      have unheld : registration.1.protectedTags.contains node.tag = false := by rw [tag]; decide_cbv
      rw [unheld] at clash
      simp [denote,CandidateCurrentGrantResources.guard,Clash] at clash
    · subst index
      exact .refl childIndex

/-- One fixed actual child grant and completion embeds the whole source span. -/
theorem child_embedding (byte : Nat) (_bound : byte < 2) :
    Embeds (sourceAfter.setExtra constructed.tree) registration.1.protectedTags extended childIndex byte .exclusive := by
  dsimp only [Embeds,Allocation.setExtra,Allocation.mapExtra]
  intro segment member lower upper
  have arrayMember := Array.mem_toList_iff.mp member
  obtain ⟨position,valid,equal⟩ := Array.mem_iff_getElem.mp arrayMember
  have length : constructed.tree.locations.entries.size = 1 := by decide_cbv
  have zero : position = 0 := by omega
  subst position
  subst segment
  have value : constructed.tree.locations.entries[0].data = childRow := by
    simp only [childRow,Array.getElem?_eq_getElem valid,Option.map_some,Option.getD_some]
  rw [value]
  exact child_resources

def delegatedPointer : PointerInstance :=
  ⟨sourceId,Pointer.new (.concrete sourceId output.tag) sourcePointer.value.offset,childIndex⟩

/-- Source owner 0 retains its active footprint through the actual child;
handle 2 retains the incoming parent family with suspended contents. -/
def delegatedContents : CandidateFreezeContentResources.Fragment := fun byte owner =>
  if owner = 2 ∧ byte.1 = sourceId ∧ byte.2 < 2 then some ⟨.mut,.suspended⟩ else contents byte owner

def delegated : Interpretation := {
  precise := #[(sourceId,precise 2 3 extended),(returnId,precise 1 1 oldCompletion)]
  pointers := #[sourcePointer,returnPointer,delegatedPointer]
  loans := #[⟨2,some 2,1⟩,⟨1,none,0⟩,⟨0,none,0⟩]
  content := delegatedContents}

def delegatedWorld : World := #[(sourceId,sourceAfter.setExtra constructed.tree),(returnId,boolAllocation)]

def delegatedIdentities : CandidateCurrentJointCall.Identities := {
  interpretation := delegated
  occurrences := #[⟨0,sourcePointer.value⟩,⟨1,returnPointer.value⟩,⟨2,delegatedPointer.value⟩]
  attachments := #[]}

theorem preserved_families :
    delegated.pointers[0]? = (interpretation true).pointers[0]? ∧
    delegated.pointers[1]? = (interpretation true).pointers[1]? ∧
    delegated.pointers[2]? = some delegatedPointer ∧
    delegated.loans[0]? = some ⟨2,some 2,1⟩ ∧
    delegated.loans[2]? = some ⟨0,none,0⟩ ∧
    (∀ byte, delegated.content byte 0 = contents byte 0) ∧
    (∀ byte, delegated.content byte 1 = contents byte 1) ∧
    (∀ byte, byte.1 = sourceId → byte.2 < 2 → delegated.content byte 2 = some ⟨.mut,.suspended⟩) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · intro byte; simp [delegated,delegatedContents]
  · intro byte; simp [delegated,delegatedContents]
  · intro byte same bound; simp [delegated,delegatedContents,same,bound]

theorem stable_delegation : CandidateCurrentJointCall.StableChoices delegatedIdentities := by
  constructor
  · intro occurrence member
    change occurrence ∈ [⟨0,sourcePointer.value⟩,⟨1,returnPointer.value⟩,⟨2,delegatedPointer.value⟩] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨sourcePointer,rfl,rfl⟩
    · exact ⟨returnPointer,rfl,rfl⟩
    · exact ⟨delegatedPointer,rfl,rfl⟩
  · intro attachment member
    change attachment ∈ ([] : List CandidateCurrentJointCall.Attachment) at member
    cases member

theorem delegated_composition : CandidateFreezeContentResources.Valid delegated.content := by
  intro byte first second firstCharge secondCharge different firstAt secondAt
  change delegatedContents byte first = _ at firstAt
  change delegatedContents byte second = _ at secondAt
  unfold delegatedContents at firstAt secondAt
  split at firstAt
  · have same := Option.some.inj firstAt
    subst firstCharge
    exact Or.inl rfl
  · split at secondAt
    · have same := Option.some.inj secondAt
      subst secondCharge
      exact Or.inr (Or.inl rfl)
    · exact content_composition byte first second firstCharge secondCharge different firstAt secondAt

private theorem return_embedding (byte : Nat) (_bound : byte < 1) :
    Embeds boolAllocation registration.1.protectedTags oldCompletion primary byte .exclusive := by
  intro segment member lower upper index node found
  change segment ∈ [⟨⟨0,1⟩,row⟩] at member
  have same := List.mem_singleton.mp member
  subst segment
  have bounded := GeneralBorrowNodeUpdate.lookup_valid boolAllocation.extra.nodes index node found
  have bound : index.toNat < 1 := bounded
  have same : index = primary := index_inj (show index.toNat = 0 by omega)
  subst index
  have nodeEq : node = rootNode returnTag := Option.some.inj found.symm
  subst node
  have unheld : registration.1.protectedTags.contains returnTag = false := by decide_cbv
  constructor
  · intro _
    change Demand.exclusive ∈ tokens (denote ⟨.Unique,true,.None⟩ _)
    simp [tokens,denote]
  · intro clash
    change Clash (CandidateCurrentGrantResources.guard (denote ⟨.Unique,true,.None⟩
      (registration.1.protectedTags.contains returnTag))) .exclusive at clash
    rw [unheld] at clash
    cases clash

private theorem child_realized (index : UniIndex) (node : TreeNode)
    (found : constructed.tree.nodes.get index = some node) :
    Realized (RawState childRow index node) (registration.1.protectedTags.contains node.tag) := by
  have bounded := GeneralBorrowNodeUpdate.lookup_valid constructed.tree.nodes index node found
  change index.toNat < constructed.tree.nodes.size at bounded
  have size : constructed.tree.nodes.size = 3 := by decide_cbv
  have possibilities : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 := by omega
  rcases possibilities with zero | one | two
  · have same : index = primary := index_inj zero
    subst index
    have slot : childRow.perms.get primary = some ⟨.Unique,true,.None⟩ := by decide_cbv
    unfold RawState
    rw [slot]
    simp [Realized,WellFormed,denote]
  · have same : index = ambient := index_inj one
    subst index
    have slot : childRow.perms.get ambient = some ⟨.Cell,false,.Read⟩ := by decide_cbv
    unfold RawState
    rw [slot]
    simp [Realized,WellFormed,denote]
  · have same : index = childIndex := index_inj two
    subst index
    have slot : childRow.perms.get childIndex = some ⟨.ReservedFrz false,true,.None⟩ := by decide_cbv
    unfold RawState
    rw [slot]
    simp [Realized,WellFormed,denote]

/-- Every actual raw node, including the unowned ambient Cell, has a realized
resource denotation in the SAME post-world and actual protector table. -/
theorem post_realized : ActualRealized delegatedWorld registration.1.protectedTags := by
  intro id allocation present segment member index node found
  change (id,allocation) ∈ [(sourceId,sourceAfter.setExtra constructed.tree),(returnId,boolAllocation)] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at present
  rcases present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · change segment ∈ constructed.tree.locations.entries.toList at member
    change constructed.tree.nodes.get index = some node at found
    obtain ⟨position,valid,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    have length : constructed.tree.locations.entries.size = 1 := by decide_cbv
    have zero : position = 0 := by omega
    subst position
    subst segment
    have value : constructed.tree.locations.entries[0].data = childRow := by
      simp only [childRow,Array.getElem?_eq_getElem valid,Option.map_some,Option.getD_some]
    rw [value]
    exact child_realized index node found
  · change segment ∈ [⟨⟨0,1⟩,row⟩] at member
    have same := List.mem_singleton.mp member
    subst segment
    have bounded := GeneralBorrowNodeUpdate.lookup_valid boolAllocation.extra.nodes index node found
    have bound : index.toNat < 1 := bounded
    have same : index = primary := index_inj (show index.toNat = 0 by omega)
    subst index
    change Realized ⟨.Unique,true,.None⟩ _
    simp [Realized,WellFormed,denote]

/-- A SINGLE correlated post-resource interpretation: active source ownership
uses the real child family; the old family is suspended; the separate return
owner remains active. No complete-graph or old-parent active-right assertion
is silently added. -/
theorem active_resources :
    ∀ byte owner mode, delegated.content byte owner = some ⟨mode,.active⟩ →
    ∃ loan pointer allocation precise,
      delegated.loans[owner]? = some loan ∧ delegated.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present delegatedWorld byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ delegated.precise.toList ∧
      Embeds allocation registration.1.protectedTags precise.completion pointer.grant byte.2 (demandOf mode) := by
  intro byte owner mode charged
  change delegatedContents byte owner = _ at charged
  unfold delegatedContents at charged
  split at charged
  · have impossible := congrArg CandidateFreezeContentResources.Charge.role (Option.some.inj charged)
    cases impossible
  · unfold contents at charged
    split at charged
    · rename_i sourceCase
      obtain ⟨rfl,idEq,bound⟩ := sourceCase
      have modeEq : mode = .mut := (congrArg CandidateFreezeContentResources.Charge.mode (Option.some.inj charged)).symm
      subst mode
      refine ⟨⟨2,some 2,1⟩,delegatedPointer,sourceAfter.setExtra constructed.tree,precise 2 3 extended,
        rfl,rfl,idEq.symm,?_,?_,?_,?_⟩
      · rw [idEq]; simp [Present,delegatedWorld]
      · have length : (sourceAfter.setExtra constructed.tree).len = 2 := by decide_cbv
        rw [length]; exact bound
      · rw [idEq]; simp [delegated]
      · exact child_embedding byte.2 bound
    · split at charged
      · rename_i returnCase
        obtain ⟨rfl,idEq,bound⟩ := returnCase
        have modeEq : mode = .ret := (congrArg CandidateFreezeContentResources.Charge.mode (Option.some.inj charged)).symm
        subst mode
        refine ⟨⟨1,none,0⟩,returnPointer,boolAllocation,precise 1 1 oldCompletion,
          rfl,rfl,idEq.symm,?_,?_,?_,?_⟩
        · rw [idEq]; simp [Present,delegatedWorld]
        · have length : boolAllocation.len = 1 := by decide_cbv
          rw [length]; exact bound
        · rw [idEq]; simp [delegated]
        · exact return_embedding byte.2 bound
      · cases charged

/-- The extension is exactly the real resulting parent array, retaining the
ambient NONE. No exposed origin is invented for the optional component. -/
theorem physical_extension :
    extended.parents = constructed.tree.nodes.data.map (fun saved => saved.bind (·.parent)) := by decide_cbv

theorem retained_storage :
    OrdinaryPhysicalValidity.MutU8Slice (sourceAfter.setExtra constructed.tree) 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination boolAllocation 0 := by
  have initial := source_physical
  refine ⟨?_,bool_physical⟩
  exact ⟨⟨initial.storage.byteLength,initial.storage.maskLength,initial.storage.maskCapacity,initial.storage.provenance⟩,
    initial.nonempty,initial.signedSize,initial.contained,initial.writable,initial.values⟩

/-- Exact finite input → actual registered Read → SAME Read output's real
constructor → one correlated child-backed resource interpretation. The old
pointer families stay present; the parent handle is suspended. This is neither
full caller execution nor ordinary-input coverage. -/
theorem invoke :
    GeneralBorrowForestFnEntry.operation sourceTree global {} sourceId sourceTag 0 2 .VisitChildrenOfAccessed = .ok output ∧
    output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
    EffectiveCell output.access.tree ∧ EffectiveCell output.child.tree ∧
    extended.parents = output.child.tree.nodes.data.map (fun saved => saved.bind (·.parent)) ∧
    delegated.pointers[0]? = (interpretation true).pointers[0]? ∧
    delegated.pointers[1]? = (interpretation true).pointers[1]? ∧
    delegated.loans[0]? = some ⟨2,some 2,1⟩ ∧ delegated.loans[2]? = some ⟨0,none,0⟩ ∧
    CandidateFreezeContentResources.Valid delegated.content ∧
    CandidateCurrentJointCall.StableChoices delegatedIdentities ∧
    ActualRealized delegatedWorld output.global.protectedTags ∧
    (∀ byte owner mode, delegated.content byte owner = some ⟨mode,.active⟩ →
    ∃ loan pointer allocation precise,
      delegated.loans[owner]? = some loan ∧ delegated.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present delegatedWorld byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ delegated.precise.toList ∧
      Embeds allocation registration.1.protectedTags precise.completion pointer.grant byte.2 (demandOf mode)) :=
  ⟨actual_operation,read_effective_cell.1,real_child.1,read_effective_cell.2,constructed_effective_cell,
    physical_extension,rfl,rfl,rfl,rfl,delegated_composition,stable_delegation,post_realized,active_resources⟩

end
end DuplicatePrefix.CurrentCallOptionalCellFnEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallOptionalCellFnEntry.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved optional Cell FnEntry dependency {dependency}"
