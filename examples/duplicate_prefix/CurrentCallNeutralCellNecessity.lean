import duplicate_prefix.CurrentCallAdmission
import duplicate_prefix.S05CompletedRootOrigins
import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFrame

/-! A finite current-state representation test, not an execution counterexample
or an adopted ordinary-input predicate. The added Cell root is physical and
retained; it introduces neither a content owner nor a pointer family. -/
namespace DuplicatePrefix.CurrentCallNeutralCellNecessity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def sourceId : AllocId := ⟨1,by decide⟩
def returnId : AllocId := ⟨2,by decide⟩
def sourceTag : BorTag := ⟨1,by decide⟩
def returnTag : BorTag := ⟨2,by decide⟩
def cellTag : BorTag := ⟨3,by decide⟩
def primary : UniIndex := ⟨0⟩
def ambient : UniIndex := ⟨1⟩
def rootNode (tag : BorTag) : TreeNode := {
  tag := tag,parent := none,children := #[],defaultInitialPermission := .Disabled,defaultInitialSifa := .None,isExposed := false}
def cellNode : TreeNode := {rootNode cellTag with defaultInitialPermission := .Cell}
def row : LocationTree := {perms := {data := #[some ⟨.Unique,true,.None⟩]},exposedCache := {}}
def baseTree (tag : BorTag) (size : UInt64) : BorrowTree := {
  tagMapping := {mapping := #[(tag,primary)]}
  nodes := {data := #[some (rootNode tag)]}
  locations := DedupRangeMap.new (Size.ofBytes size) row
  roots := #[primary]}
def sourceTree : BorrowTree := {baseTree sourceTag 2 with
  tagMapping := {mapping := #[(sourceTag,primary),(cellTag,ambient)]}
  nodes := {data := #[some (rootNode sourceTag),some cellNode]}
  roots := #[primary,ambient]}
def sourceBefore : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[17,23] Align.ONE .Mut).toOption.get (by decide)).mapExtra (fun _ => baseTree sourceTag 2)
def sourceAfter : Allocation Provenance BorrowTree := sourceBefore.setExtra sourceTree
def boolAllocation : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[0] Align.ONE .Mut).toOption.get (by decide)).mapExtra (fun _ => baseTree returnTag 1)
def beforeWorld : World := #[(sourceId,sourceBefore),(returnId,boolAllocation)]
def afterWorld : World := #[(sourceId,sourceAfter),(returnId,boolAllocation)]
def held : ProtectedTags := {}
def sourcePointer : PointerInstance := ⟨sourceId,Pointer.new (.concrete sourceId sourceTag) (Size.ofBytes 16),primary⟩
def returnPointer : PointerInstance := ⟨returnId,Pointer.new (.concrete returnId returnTag) (Size.ofBytes 32),primary⟩
def oldCompletion : Completion := ⟨#[none],#[0]⟩
def newCompletion : Completion := ⟨#[none,none],#[0,0]⟩
def precise (size width : Nat) (completion : Completion) : PreciseAllocation :=
  ⟨completion,Array.replicate size (Array.replicate width ⟨.Disabled,false,.None⟩)⟩
def contents : CandidateFreezeContentResources.Fragment := fun byte owner =>
  if owner = 0 ∧ byte.1 = sourceId ∧ byte.2 < 2 then some ⟨.mut,.active⟩
  else if owner = 1 ∧ byte.1 = returnId ∧ byte.2 < 1 then some ⟨.ret,.active⟩ else none
def interpretation (extra : Bool) : Interpretation := {
  precise := #[(sourceId,precise 2 (if extra then 2 else 1) (if extra then newCompletion else oldCompletion)),
    (returnId,precise 1 1 oldCompletion)]
  pointers := #[sourcePointer,returnPointer]
  loans := #[⟨0,none,0⟩,⟨1,none,0⟩]
  content := contents}
def identities (extra : Bool) : Identities := {
  interpretation := interpretation extra
  occurrences := #[⟨0,sourcePointer.value⟩,⟨1,returnPointer.value⟩]
  attachments := #[]}

private theorem index_inj {left right : UniIndex} (equal : left.toNat = right.toNat) : left = right := by
  cases left;cases right;congr;exact UInt32.toNat_inj.mp equal

private theorem source_nodes (index : UniIndex) (node : TreeNode)
    (found : sourceTree.nodes.get index = some node) :
    (index = primary ∧ node = rootNode sourceTag) ∨ (index = ambient ∧ node = cellNode) := by
  by_cases zero : index.toNat = 0
  · have equal : index = primary := index_inj zero
    subst index
    exact .inl ⟨rfl,Option.some.inj found.symm⟩
  by_cases one : index.toNat = 1
  · have equal : index = ambient := index_inj one
    subst index
    exact .inr ⟨rfl,Option.some.inj found.symm⟩
  have beyond : 2 ≤ index.toNat := by omega
  have missing : sourceTree.nodes.get index = none := by
    simp only [sourceTree,UniValMap.get]
    rw [Array.getElem?_eq_none (by simpa using beyond)]
  rw [missing] at found
  cases found

private theorem base_nodes (tag : BorTag) (size : UInt64) (index : UniIndex) (node : TreeNode)
    (found : (baseTree tag size).nodes.get index = some node) : index = primary ∧ node = rootNode tag := by
  by_cases zero : index.toNat = 0
  · have equal : index = primary := index_inj zero
    subst index
    exact ⟨rfl,Option.some.inj found.symm⟩
  have missing : (baseTree tag size).nodes.get index = none := by
    simp only [baseTree,UniValMap.get]
    rw [Array.getElem?_eq_none (by change 1 ≤ index.toNat;omega)]
  rw [missing] at found
  cases found

theorem source_physical : OrdinaryPhysicalValidity.MutU8Slice sourceAfter 0 2 := by
  refine ⟨⟨rfl,rfl,by trivial,?_⟩,by decide,by decide,by decide,rfl,?_⟩
  · change ProvenanceCopy.WellFormed (ProvenanceMap.new) 2
    constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
  · intro index lower upper
    rfl

theorem bool_physical : OrdinaryPhysicalValidity.BoolDestination boolAllocation 0 := by
  refine ⟨⟨rfl,rfl,by trivial,?_⟩,by decide,rfl⟩
  change ProvenanceCopy.WellFormed (ProvenanceMap.new) 1
  constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]

theorem same_families :
    (interpretation false).pointers = (interpretation true).pointers ∧
    (interpretation false).loans = (interpretation true).loans ∧
    (interpretation false).content = (interpretation true).content := ⟨rfl,rfl,rfl⟩

theorem pointer_bindings : PointerBinds sourceBefore sourcePointer ∧ PointerBinds sourceAfter sourcePointer ∧
    PointerBinds boolAllocation returnPointer := by
  refine ⟨⟨rootNode sourceTag,rfl,by decide,by exact ⟨rfl,rfl⟩⟩,⟨rootNode sourceTag,rfl,by decide,by exact ⟨rfl,rfl⟩⟩,
    ⟨rootNode returnTag,rfl,by decide,by exact ⟨rfl,rfl⟩⟩⟩

theorem stable_families (extra : Bool) : StableChoices (identities extra) := by
  constructor
  · intro occurrence member
    simp only [identities,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with first | second
    · subst occurrence;exact ⟨sourcePointer,rfl,rfl⟩
    · subst occurrence;exact ⟨returnPointer,rfl,rfl⟩
  · intro attachment member
    simp [identities] at member

theorem no_completion (completion : Completion) : ¬ Completes sourceTree completion := by
  intro complete
  have chosen := complete.2.2.2.2.2.1 1 ambient (by decide)
  simp only [show (1 : Nat) ≠ 0 by decide,↓reduceIte] at chosen
  obtain ⟨earlier,originRoot,origin,rootNode,originNode,_,_,_,originAt,exposed,_⟩ := chosen
  rcases source_nodes origin originNode originAt with ⟨_,equal⟩ | ⟨_,equal⟩
  all_goals subst originNode;cases exposed


def source (extra : Bool) : Allocation Provenance BorrowTree := if extra then sourceAfter else sourceBefore
def world (extra : Bool) : World := if extra then afterWorld else beforeWorld

private theorem source_len (extra : Bool) : (source extra).len = 2 := by cases extra <;> rfl
private theorem source_row (extra : Bool) (segment : RangeMapSegment LocationTree)
    (member : segment ∈ (source extra).extra.locations.entries.toList) : segment.data = row := by
  cases extra <;> change segment ∈ [⟨⟨0,2⟩,row⟩] at member
  all_goals exact congrArg RangeMapSegment.data (List.mem_singleton.mp member)

private theorem source_cells (extra : Bool) (segment : RangeMapSegment LocationTree)
    (member : segment ∈ (source extra).extra.locations.entries.toList) (index : UniIndex) (node : TreeNode)
    (found : (source extra).extra.nodes.get index = some node) :
    RawState segment.data index node = ⟨.Unique,true,.None⟩ ∨ RawState segment.data index node = ⟨.Cell,false,.None⟩ := by
  rw [source_row extra segment member]
  cases extra
  · obtain ⟨rfl,rfl⟩ := base_nodes sourceTag 2 index node found
    exact .inl rfl
  · rcases source_nodes index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .inl rfl
    · exact .inr rfl

private theorem bool_cells (segment : RangeMapSegment LocationTree)
    (member : segment ∈ boolAllocation.extra.locations.entries.toList) (index : UniIndex) (node : TreeNode)
    (found : boolAllocation.extra.nodes.get index = some node) : RawState segment.data index node = ⟨.Unique,true,.None⟩ := by
  change segment ∈ [⟨⟨0,1⟩,row⟩] at member
  have same := List.mem_singleton.mp member
  subst segment
  obtain ⟨rfl,rfl⟩ := base_nodes returnTag 1 index node found
  rfl

private theorem source_embedding (extra : Bool) (byte : Nat) :
    Embeds (source extra) held (if extra then newCompletion else oldCompletion) primary byte .exclusive := by
  intro segment member lower upper index node found
  rcases source_cells extra segment member index node found with stateEq | stateEq
  all_goals rw [stateEq]
  all_goals
    constructor
    · intro ancestor
      rw [show held.contains node.tag = false from rfl]
      decide
    · intro clash;exact False.elim clash

private theorem bool_embedding (byte : Nat) : Embeds boolAllocation held oldCompletion primary byte .exclusive := by
  intro segment member lower upper index node found
  rw [bool_cells segment member index node found]
  constructor
  · intro ancestor
    rw [show held.contains node.tag = false from rfl]
    decide
  · intro clash;exact False.elim clash

theorem content_composition : CandidateFreezeContentResources.Valid contents := by
  intro byte first second firstCharge secondCharge different firstAt secondAt
  unfold contents at firstAt secondAt
  split at firstAt
  · rename_i left
    split at secondAt
    · rename_i right
      exact False.elim (different (left.1.trans right.1.symm))
    · split at secondAt
      · rename_i right
        have impossible : sourceId = returnId := left.2.1.symm.trans right.2.1
        exact False.elim ((by decide : sourceId ≠ returnId) impossible)
      · cases secondAt
  · split at firstAt
    · rename_i left
      split at secondAt
      · rename_i right
        have impossible : sourceId = returnId := right.2.1.symm.trans left.2.1
        exact False.elim ((by decide : sourceId ≠ returnId) impossible)
      · split at secondAt
        · rename_i right
          exact False.elim (different (left.1.trans right.1.symm))
        · cases secondAt
    · cases firstAt

theorem realized (extra : Bool) : ActualRealized (world extra) held := by
  intro id allocation present segment member index node found
  have listed : allocation = source extra ∨ allocation = boolAllocation := by
    cases extra <;> simp [world,afterWorld,beforeWorld,Present] at present
    all_goals rcases present with first | second
    all_goals first | exact .inl first.2 | exact .inr second.2
  rcases listed with rfl | rfl
  · rcases source_cells extra segment member index node found with unique | cell
    · rw [unique,show held.contains node.tag = false from rfl];simp [Realized,CandidateCurrentGrantResources.WellFormed,denote]
    · rw [cell,show held.contains node.tag = false from rfl];simp [Realized,CandidateCurrentGrantResources.WellFormed,denote]
  · rw [bool_cells segment member index node found,show held.contains node.tag = false from rfl];simp [Realized,CandidateCurrentGrantResources.WellFormed,denote]

/-- Active ownership is charged to the SAME two concrete families before and
 after the extra component. No completion-existence assertion is hidden here. -/
theorem active_resources (extra : Bool) :
    ∀ byte owner mode, (interpretation extra).content byte owner = some ⟨mode,.active⟩ →
    ∃ loan pointer allocation precise,
      (interpretation extra).loans[owner]? = some loan ∧
      (interpretation extra).pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present (world extra) byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ (interpretation extra).precise.toList ∧
      Embeds allocation held precise.completion pointer.grant byte.2 (demandOf mode) := by
  intro byte owner mode charged
  change contents byte owner = _ at charged
  unfold contents at charged
  split at charged
  · rename_i sourceCase
    obtain ⟨rfl,idEq,bound⟩ := sourceCase
    have modeEq : mode = .mut := (congrArg CandidateFreezeContentResources.Charge.mode (Option.some.inj charged)).symm
    subst mode
    refine ⟨⟨0,none,0⟩,sourcePointer,source extra,precise 2 (if extra then 2 else 1) (if extra then newCompletion else oldCompletion),
      rfl,rfl,idEq.symm,?_,?_,?_,?_⟩
    · rw [idEq]
      cases extra <;> simp [world,beforeWorld,afterWorld,source,Present]
    · rw [source_len];exact bound
    · rw [idEq];simp [interpretation]
    · exact source_embedding extra byte.2
  · split at charged
    · rename_i returnCase
      obtain ⟨rfl,idEq,bound⟩ := returnCase
      have modeEq : mode = .ret := (congrArg CandidateFreezeContentResources.Charge.mode (Option.some.inj charged)).symm
      subst mode
      refine ⟨⟨1,none,0⟩,returnPointer,boolAllocation,precise 1 1 oldCompletion,rfl,rfl,idEq.symm,?_,?_,?_,?_⟩
      · rw [idEq]
        cases extra <;> simp [world,beforeWorld,afterWorld,Present]
      · exact bound
      · rw [idEq];simp [interpretation]
      · exact bool_embedding byte.2
    · cases charged

private def source_depth : GeneralBorrowExposure.ParentDepth sourceTree.nodes where
  depth := fun _ => 0
  bounded := by intro index node found;exact Nat.zero_le _
  parent := by
    intro index node found parent edge
    rcases source_nodes index node found with ⟨_,rfl⟩ | ⟨_,rfl⟩
    all_goals cases edge

/-- The actual later-root callback already has a finite existing leaf proof;
this adds no origin, future table, or access-success premise. -/
theorem cell_callback (maximum : Option BorTag) (kind : AccessKind) :
    ∃ after, sourceTree.performWildcardAccessAt row ambient maximum kind held true = ⟨after,.Completed⟩ ∧
      GeneralBorrowPermissions.ForeignOwned (GeneralBorrowWildcardVirtualLeaf.effective after ambient cellNode) false ∧
      GeneralBorrowWildcardVirtualLeafFrame.Frame ambient row after := by
  exact GeneralBorrowWildcardVirtualLeafFrame.foreign_access sourceTree row ambient cellNode maximum kind held
    rfl rfl source_depth rfl (.inr (by cases kind <;> rfl))
    (by change GeneralBorrowPermissions.ForeignOwned ⟨.Cell,false,.None⟩ false;exact ⟨rfl,.inl rfl⟩)


/-- Only allocation-local tree metadata changes, not the owned byte storage. -/
theorem storage_frame : sourceAfter.len = sourceBefore.len ∧ sourceAfter.byteSize = sourceBefore.byteSize ∧
    sourceAfter.initializationMask = sourceBefore.initializationMask ∧ sourceAfter.provenanceMap = sourceBefore.provenanceMap ∧
    AllocationCopy.snapshot sourceAfter = AllocationCopy.snapshot sourceBefore := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem families_do_not_use_ambient (extra : Bool) :
    ∀ pointer ∈ (interpretation extra).pointers.toList, pointer.grant ≠ ambient := by
  intro pointer member
  simp only [interpretation,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals exact (by decide : primary ≠ ambient)

theorem no_delegation_to_ambient : ¬ Below newCompletion ambient primary := by
  have last : ∀ index, Below newCompletion index primary → index = primary := by
    intro index ancestry
    cases ancestry with
    | refl => rfl
    | step edge prior => simp [newCompletion,primary,UniIndex.toNat] at edge
  intro ancestry
  exact (by decide : ambient ≠ primary) (last ambient ancestry)

/-- Neutrality is stated in semantic resource constructors on every row and
 descendant. It is not a ForeignWrite-table or operation-success assumption. -/
theorem ambient_neutral (segment : RangeMapSegment LocationTree)
    (_member : segment ∈ sourceAfter.extra.locations.entries.toList) (index : UniIndex) (node : TreeNode)
    (_found : sourceTree.nodes.get index = some node) (_descendant : GeneralBorrowExposedNonleafPrimaryPath.Path sourceTree ambient index) :
    guard (denote (RawState segment.data index node) (held.contains node.tag)) = .none := rfl

theorem allocation_ids (extra : Bool) : ((world extra).toList.map Prod.fst).Nodup := by
  cases extra <;> decide

theorem completion_ids (extra : Bool) : ((interpretation extra).precise.toList.map Prod.fst).Nodup := by
  cases extra <;> decide

theorem source_roots_distinct : sourceTree.roots.toList.Nodup := by decide

/-- The strict completed-graph representation rejects this resource frame. -/
theorem semantic_gap :
    CandidateFreezeContentResources.Valid contents ∧
    ActualRealized afterWorld held ∧ StableChoices (identities true) ∧
    OrdinaryPhysicalValidity.MutU8Slice sourceAfter 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination boolAllocation 0 ∧
    (∀ completion, ¬ Completes sourceTree completion) :=
  ⟨content_composition,realized true,stable_families true,source_physical,bool_physical,no_completion⟩

end
end DuplicatePrefix.CurrentCallNeutralCellNecessity

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallNeutralCellNecessity.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved neutral Cell necessity dependency {dependency}"
