import duplicate_prefix.CurrentCallLen
import duplicate_prefix.CurrentCallDefaultSharedBoolFrame
import duplicate_prefix.CurrentCallLenSharedBoolFrame
import duplicate_prefix.CurrentCallEntryProtectionData
import duplicate_prefix.GeneralBorrowSharedFnEntryGlobalReturn
import duplicate_prefix.CurrentCallRootPhysicalWindow

namespace DuplicatePrefix.CurrentCallLenRootData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open S05ConcreteProtectedChildCompletion CurrentCallLen
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private def stageCompletion {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (reader : UniIndex) : Completion :=
  extend (CurrentCallSharedReference.sourceCompletion s.out.borrowed) reader s.out.source.base.raw.child

private def literal (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615) (parentTag : BorTag) (offset len : UInt64) : GeneralBorrowForestFnEntry.Output :=
  let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
  let accessed := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true⟩

private theorem literal_operation (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615) (parentTag : BorTag) (offset len : UInt64) :
    GeneralBorrowRawSharedFnEntry.operation tree global {} allocation parentTag offset len .VisitChildrenOfAccessed =
      .ok (literal tree global allocation room parentTag offset len) := by
  simp only [GeneralBorrowRawSharedFnEntry.operation,TypedRetagEmpty.allocate_tag global room,Except.bind,Except.pure,bind,pure]
  rfl

structure Data {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count)
    (post : Interpreter.MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (held : Interpreter.MachineHooks.BorrowState) (sourceCompletion : Completion) where
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  completion : Completion
  live : post.memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,entry)
  sameEntry : call.sourceId = call.returnId → entry = sourceEntry
  sameCompletion : call.sourceId = call.returnId → completion = sourceCompletion
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global
  completes : Completes entry.allocation.extra completion
  order : ParentTagOrder entry.allocation.extra
  short : entry.allocation.extra.nodes.size < 65536
  node : TreeNode
  present : entry.allocation.extra.nodeAt s.out.borrowed.child = some node
  tag : node.tag = s.out.borrowed.output.tag
  leaf : node.children = #[]
  hidden : node.isExposed = false
  active : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.borrowed.child .Write
    (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1)
  owned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
    (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) entry.allocation.extra.locations
  edge : completion.parents[s.out.borrowed.child.toNat]? = some (some s.out.source.base.raw.returnPointer.grant)
  originalNode : TreeNode
  originalPresent : entry.allocation.extra.nodeAt s.out.source.base.raw.returnPointer.grant = some originalNode
  originalProvenance : match s.out.source.base.raw.returnPointer.value.provenance with
    | .concrete _ tag => tag = originalNode.tag | .wildcard => originalNode.isExposed = true
  bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ entry.allocation.extra.locations.size.bytes.toNat
  sourceAbsent : call.sourceId ≠ call.returnId → entry.allocation.extra.indexOfTag s.out.source.base.raw.output.tag = none

private theorem same_stage {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat) (same : call.sourceId = call.returnId) :
    ∃ reader node, s.tree.indexOfTag s.out.borrowed.output.global.nextPointerTag = some reader ∧
      s.tree.nodeAt s.out.borrowed.child = some node ∧ node.tag = s.out.borrowed.output.tag ∧
      node.children = #[] ∧ node.isExposed = false ∧
      OwnedOn (Authority s.tree (stageCompletion s reader) s.held.global.protectedTags s.out.borrowed.child)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) s.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin s.tree s.out.borrowed.child .Write
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) ∧
      s.entry.allocation.extra.locations.size = s.entry.allocation.byteSize := by
  let prepared := CurrentCallPush.prepared_input input #[]
  let raw := s.out.source.base.raw
  obtain ⟨runtime,complete,order,owned⟩ := CurrentCallSharedReference.source_ready prepared {} raw s.out.borrowed s.facts.written
  obtain ⟨parentNode,parentAt,parentTag⟩ := CurrentCallSharedReference.source_node raw s.out.borrowed s.facts.written
  rw [←s.extra] at runtime complete order owned parentAt
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path s.entry.allocation.extra runtime.formed.toGraphState raw.child parentNode parentAt
  obtain ⟨entry,base,live,_,storage,room,physicalBounds,_,_,_⟩ := s.facts.sourceWindow
  have sameEntry : entry = s.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans s.live))).2
  subst entry
  have offsetEq : (UInt64.ofNat call.sourceOffset).toNat = call.sourceOffset := by
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : call.sourceOffset<2^64)]
  obtain ⟨actual,actualLive,_,_,actualLength,_,_,_,_,_⟩ := s.facts.source_allocation positive
  have actualEq : actual = s.entry := (Prod.mk.inj (Option.some.inj (actualLive.symm.trans s.live))).2
  rw [actualEq] at actualLength
  obtain ⟨_,_,_,_,_,rawSize⟩ := CandidateCurrentLiveRuntime.live options limits remaining (CurrentCallPush.preparedMachine before #[]) tracker len
    prepared.machine.state prepared.machine.resources call.sourceId raw.sourceAllocation raw.sourcePresent
  have capacityBefore : s.entry.allocation.extra.locations.size = s.entry.allocation.byteSize := by
    have size : s.entry.allocation.extra.locations.size.bytes.toNat = s.entry.allocation.byteSize.bytes.toNat := by
      rw [s.extra,CurrentCallSharedReference.source_capacity raw s.out.borrowed s.facts.written,rawSize,←actualLength,storage]
    exact congrArg Size.ofBytes (UInt64.toNat_inj.mp size)
  have bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [capacityBefore,←storage,offsetEq];exact physicalBounds
  have budgets := CurrentCallSharedReference.source_budget prepared {} raw s.out.borrowed s.facts.written
  rw [←s.extra] at budgets
  have initialTree : s.entry.allocation.extra = s.out.updated.extra := by
    rw [s.extra]
    simp only [CurrentCallSharedReference.sourceTree,same,ite_true]
    exact s.facts.extra.symm
  obtain ⟨bNode,bAt,bTag,bLeaf,bHidden,bActive⟩ := CurrentCallEntryProtectionData.Facts.bool_data s.facts positive
  have bOwned := CurrentCallEntryProtectionData.Facts.bool_authority s.facts positive
  rw [←initialTree] at bAt bActive bOwned
  have different : s.out.borrowed.child ≠ raw.child := by
    intro equal
    have found : s.entry.allocation.extra.nodes.get raw.child = some bNode := by simpa only [equal] using bAt
    have nodeEq : bNode = parentNode := Option.some.inj (found.symm.trans parentAt)
    have tags := CurrentCallEntryProtectionData.source_bool_tags_ne raw s.out.borrowed
    exact tags (parentTag.symm.trans ((congrArg TreeNode.tag nodeEq).symm.trans bTag))
  have endpoints := CurrentCallBoolProtection.endpoints prepared {} raw positive
  have disjoint : ∀ point : UInt64, (UInt64.ofNat call.returnOffset).toNat ≤ point.toNat →
      point.toNat < (UInt64.ofNat call.returnOffset+1).toNat →
      point.toNat < (UInt64.ofNat call.sourceOffset).toNat ∨ (UInt64.ofNat call.sourceOffset+len).toNat ≤ point.toNat := by
    intro point start stop
    by_cases before : point.toNat < (UInt64.ofNat call.sourceOffset).toNat
    · exact .inl before
    · right
      by_cases after : (UInt64.ofNat call.sourceOffset+len).toNat ≤ point.toNat
      · exact after
      · have outside := endpoints.2.2.2.2.2 same point (by omega) (by omega)
        omega
  have bOwnedInitial : OwnedOn (Authority s.entry.allocation.extra (CurrentCallSharedReference.sourceCompletion s.out.borrowed)
      s.out.borrowed.output.global.protectedTags s.out.borrowed.child)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) s.entry.allocation.extra.locations := by
    simpa only [CurrentCallSharedReference.sourceCompletion,same,ite_true] using bOwned
  obtain ⟨_,_,_,_,_,reader,lookup,retained,⟨node,nodeAt,nodeTag,nodeParent,nodeLeaf,nodeHidden⟩,activity⟩ :=
    CurrentCallDefaultSharedBoolFrame.construct s.entry.allocation.extra s.out.borrowed.output.global
      (CurrentCallSharedReference.sourceCompletion s.out.borrowed) runtime complete order position root raw.child s.out.borrowed.child
      rootNode parentNode bNode slot rootAt parentAt path bAt bLeaf bHidden different s.room budgets.2.1 budgets.2.2
      (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1)
      (by intro zero;simp [zero] at positive) bounds disjoint owned bOwnedInitial bActive
  simp only [parentTag] at lookup retained nodeAt activity
  exact ⟨reader,node,lookup,nodeAt,nodeTag.trans bTag,nodeLeaf.trans bLeaf,nodeHidden.trans bHidden,retained,activity,capacityBefore⟩

/-- Concrete public Len result fields recover the original Bool resources. -/
theorem of_len {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat)
    (post : Interpreter.MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (held : Interpreter.MachineHooks.BorrowState) (completion : Completion)
    (sourceLive : post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry))
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global)
    (sourceComplete : Completes entry.allocation.extra completion)
    (sourceAllocation : entry.allocation = s.entry.allocation.setExtra entry.allocation.extra)
    (sourceOrder : ParentTagOrder entry.allocation.extra)
    (sourceCapacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (sourceShort : entry.allocation.extra.nodes.size < 65536)
    (oldNodes : ∀ index node, s.entry.allocation.extra.nodes.get index = some node →
      ∃ next, entry.allocation.extra.nodes.get index = some next ∧ next.tag = node.tag ∧
        next.parent = node.parent ∧ next.isExposed = node.isExposed)
    (otherLive : ∀ id otherEntry, id≠call.sourceId →
      (s.out.machine count).memory.live.find? (fun row => row.1 == id) = some (id,otherEntry) →
      post.memory.live.find? (fun row => row.1 == id) = some (id,otherEntry))
    (witness : ∃ (reader helper : UniIndex) (output : GeneralBorrowForestFnEntry.Output),
      s.tree.indexOfTag s.out.borrowed.output.global.nextPointerTag = some reader ∧
      output.child.tree.indexOfTag output.tag = some helper ∧ s.tree.nodes.get helper = none ∧
      completion = extend (s.completion reader) helper reader ∧
      GeneralBorrowRawSharedFnEntry.operation s.tree s.held.global {} call.sourceId s.out.borrowed.output.global.nextPointerTag
        (UInt64.ofNat call.sourceOffset) len .VisitChildrenOfAccessed = .ok output ∧
      entry.allocation.extra = (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree ∧
      held.global = output.global.endCall output.frame) :
    Nonempty (Data s post entry held completion) := by
  obtain ⟨reader,helper,output,readerLookup,helperLookup,helperVacant,completionEq,actual,treeEq,globalEq⟩ := witness
  obtain ⟨logicalReader,readerNode,stageRuntime,stageComplete,stageOrder,readerAt,readerTag,readerParent,readerHidden,
    readable,owned,stageCapacity,bounds,stageGrowth,stageOld,sourceActive⟩ := s.logical positive
  have logicalLookup := (stageComplete.2.2.2.2.1 logicalReader readerNode readerAt).1
  rw [readerTag] at logicalLookup
  have logicalEq : logicalReader = reader := Option.some.inj (logicalLookup.symm.trans readerLookup)
  subst logicalReader
  have budgets := s.budget positive
  let raw := s.out.source.base.raw
  let initialGlobal := s.out.borrowed.output.global
  let outputLiteral := literal s.tree s.held.global call.sourceId budgets.1 s.out.borrowed.output.global.nextPointerTag
    (UInt64.ofNat call.sourceOffset) len
  have outputEq : outputLiteral = output := Except.ok.inj
    ((literal_operation s.tree s.held.global call.sourceId budgets.1 s.out.borrowed.output.global.nextPointerTag
      (UInt64.ofNat call.sourceOffset) len).symm.trans actual)
  have restored := GeneralBorrowSharedFnEntryGlobalReturn.global s.tree s.held.global stageRuntime {} call.sourceId budgets.1
  have heldEq : held.global = GeneralBorrowFnEntryRegistration.advanced s.held.global budgets.1 := by
    rw [globalEq,←outputEq]
    exact restored
  have flagsEq : held.global.protectedTags = initialGlobal.protectedTags := by rw [heldEq];rfl
  obtain ⟨initialNode,initialAt,initialTag,initialLeaf,initialHidden,initialActive⟩ := CurrentCallEntryProtectionData.Facts.bool_data s.facts positive
  have boolResources := CurrentCallEntryProtectionData.Facts.bool_resources s.facts
  have initialOwned := CurrentCallEntryProtectionData.Facts.bool_authority s.facts positive
  obtain ⟨originalNode,originalAt,originalProvenance⟩ := CurrentCallEntryProtectionData.Facts.original_return_node s.facts
  have initialBounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ s.out.updated.extra.locations.size.bytes.toNat := by
    rw [s.facts.extra,s.facts.written.capacity,s.out.borrowed.metadata.capacity]
    exact (CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} raw positive).2.2.2.2.1
  by_cases same : call.sourceId = call.returnId
  · obtain ⟨stageReader,node,lookup,nodeAt,nodeTag,nodeLeaf,nodeHidden,boolOwned,boolActive,initialCapacity⟩ := same_stage s positive same
    have stageReaderEq : stageReader = reader := Option.some.inj (lookup.symm.trans readerLookup)
    subst stageReader
    have initialTree : s.entry.allocation.extra = s.out.updated.extra := by
      rw [s.extra]
      simp only [CurrentCallSharedReference.sourceTree,same,ite_true]
      exact s.facts.extra.symm
    have sourceBoolTag : s.out.borrowed.output.tag ≠ s.out.borrowed.output.global.nextPointerTag := by
      have high := GeneralBorrowForestTagHighWater.complete s.out.updated.extra _ _ boolResources.1.below boolResources.1.formed.allocator.nodeTags
      obtain ⟨_,freshNode,_⟩ := GenericFunctionTagFormation.fresh_above s.out.updated.extra _ _ s.out.borrowed.output.global.nextPointerTag high (Nat.le_refl _)
      have fresh := freshNode (s.out.borrowed.child,initialNode)
        (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get s.out.updated.extra.nodes s.out.borrowed.child initialNode).mpr initialAt))
      simpa only [initialTag] using fresh
    have different : s.out.borrowed.child ≠ reader := by
      intro equal
      have found : s.tree.nodes.get reader = some node := by simpa only [equal,BorrowTree.nodeAt] using nodeAt
      have nodeEq := Option.some.inj (found.symm.trans readerAt)
      exact sourceBoolTag (nodeTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans readerTag))
    have endpoints := CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} raw positive
    have disjoint : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
        (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat := by
      by_cases left : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
      · exact .inl left
      by_cases after : (UInt64.ofNat call.sourceOffset).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
      · have impossible := endpoints.2.2.2.2.2 same (UInt64.ofNat call.returnOffset) after (by omega)
        omega
      · have qPositive : (UInt64.ofNat call.sourceOffset).toNat < (UInt64.ofNat call.sourceOffset+len).toNat := by
          rw [endpoints.1,endpoints.2.2.1];omega
        have earlier := endpoints.2.2.2.2.2 same (UInt64.ofNat call.sourceOffset) (Nat.le_refl _) qPositive
        exact .inr (by omega)
    obtain ⟨depth⟩ := stageRuntime.formed.depth
    obtain ⟨sourceNode,sourceAt,_⟩ := depth.parent reader readerNode readerAt raw.child readerParent
    obtain ⟨position,selected,selectedNode,slot,selectedAt,path⟩ := CandidateCurrentWindowAuthority.root_path s.tree stageRuntime.formed.toGraphState raw.child sourceNode sourceAt
    have readerPath : Path s.tree selected reader := .step path readerNode readerAt readerParent
    obtain ⟨freshHelper,freshLookup,retained,⟨finalNode,finalAt,finalTag,finalParent,finalLeaf,finalHidden⟩,finalActive⟩ :=
      CurrentCallLenSharedBoolFrame.construct s.tree s.held.global call.sourceId (s.completion reader) stageRuntime stageComplete stageOrder
        position selected raw.child reader s.out.borrowed.child selectedNode readerNode node slot selectedAt path readerAt readerPath readerParent
        readerHidden (by rw [readerTag];exact s.reader_unheld) nodeAt nodeLeaf nodeHidden different budgets.1
        (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1)
        (by intro zero;simp [zero] at positive) bounds budgets.2.1 budgets.2.2.2 disjoint readable owned boolOwned boolActive
    rw [readerTag] at freshLookup retained finalAt finalActive
    have helperEq : freshHelper = helper := by
      have finalLookup : outputLiteral.child.tree.indexOfTag outputLiteral.tag = some freshHelper := freshLookup
      rw [outputEq] at finalLookup
      exact Option.some.inj (finalLookup.symm.trans helperLookup)
    subst freshHelper
    have finalOwned : OwnedOn (Authority entry.allocation.extra completion held.global.protectedTags s.out.borrowed.child)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) entry.allocation.extra.locations := by
      rw [completionEq,treeEq,globalEq,←outputEq]
      exact retained
    have actualAt : entry.allocation.extra.nodeAt s.out.borrowed.child = some finalNode := by rw [treeEq,←outputEq];exact finalAt
    have actualActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.borrowed.child .Write
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) := by rw [treeEq,←outputEq];exact finalActive
    obtain ⟨originalFinal,originalFinalAt,originalFinalTag,_,originalFinalHidden⟩ := oldNodes raw.returnPointer.grant originalNode (by rw [initialTree];exact originalAt)
    change (match raw.returnPointer.value.provenance with
      | .concrete _ tag => tag = originalNode.tag | .wildcard => originalNode.isExposed = true) at originalProvenance
    have finalProvenance : match raw.returnPointer.value.provenance with
        | .concrete _ tag => tag = originalFinal.tag | .wildcard => originalFinal.isExposed = true := by
      cases prov : raw.returnPointer.value.provenance with
      | concrete id tag =>
        have old : tag = originalNode.tag := by simpa only [prov] using originalProvenance
        exact old.trans originalFinalTag.symm
      | wildcard => exact originalFinalHidden.trans (by simpa only [prov] using originalProvenance)
    have finalBounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ entry.allocation.extra.locations.size.bytes.toNat := by
      have capacity : entry.allocation.extra.locations.size = s.out.updated.extra.locations.size := by
        rw [sourceCapacity,sourceAllocation]
        exact initialCapacity.symm.trans (congrArg (fun tree : BorrowTree => tree.locations.size) initialTree)
      rw [capacity]
      exact initialBounds
    have helperDifferent : s.out.borrowed.child ≠ helper := by
      intro equal
      change s.tree.nodes.get s.out.borrowed.child = some node at nodeAt
      rw [equal,helperVacant] at nodeAt
      cases nodeAt
    have baseBound : s.out.borrowed.child.toNat <
        (extend (CurrentCallBoolProtection.returnCompletion raw) s.out.borrowed.child raw.returnPointer.grant).parents.size := by
      rw [boolResources.2.1.1]
      exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ initialAt
    have stageBound : s.out.borrowed.child.toNat < (s.completion reader).parents.size := by
      rw [stageComplete.1]
      exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ nodeAt
    have edge : completion.parents[s.out.borrowed.child.toNat]? = some (some raw.returnPointer.grant) := by
      rw [completionEq,old_parent _ helper reader s.out.borrowed.child helperDifferent stageBound]
      change (stageCompletion s reader).parents[s.out.borrowed.child.toNat]? = _
      rw [stageCompletion,old_parent _ reader raw.child s.out.borrowed.child different (by simpa only [CurrentCallSharedReference.sourceCompletion,same,ite_true] using baseBound)]
      simpa only [CurrentCallSharedReference.sourceCompletion,same,ite_true] using boolResources.2.2.2.2
    exact ⟨⟨entry,completion,by simpa only [same] using sourceLive,(fun _ => rfl),(fun _ => rfl),sourceRuntime,sourceComplete,
      sourceOrder,sourceShort,finalNode,actualAt,finalTag.trans nodeTag,finalLeaf.trans nodeLeaf,finalHidden.trans nodeHidden,actualActive,finalOwned,edge,
      originalFinal,originalFinalAt,finalProvenance,finalBounds,fun separate => False.elim (separate same)⟩⟩
  · let bEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.out.physical.entry with allocation := s.out.updated}
    let bCompletion := extend (CurrentCallBoolProtection.returnCompletion raw) s.out.borrowed.child raw.returnPointer.grant
    have bLive : post.memory.live.find? (fun row => row.1 == call.returnId) = some (call.returnId,bEntry) :=
      otherLive call.returnId bEntry (Ne.symm same) (by simpa only [s.facts.returnId] using CurrentCallRootPhysicalWindow.bool_live s.out count)
    have raise : initialGlobal.nextPointerTag.value.toNat ≤ held.global.nextPointerTag.value.toNat := by
      rw [heldEq]
      have first := GenericFunctionEntryNumerics.successor_value initialGlobal.nextPointerTag s.room
      have second := GenericFunctionEntryNumerics.successor_value s.held.global.nextPointerTag budgets.1
      change initialGlobal.nextPointerTag.value.toNat ≤ (TypedRetagEmpty.successorTag s.held.global.nextPointerTag budgets.1).value.toNat
      have initialStep : s.held.global.nextPointerTag.value.toNat = initialGlobal.nextPointerTag.value.toNat+1 := first
      omega
    have boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts bEntry.allocation.extra held.global := by
      refine ⟨?_,?_,boolResources.1.possible,?_⟩
      · rw [flagsEq];exact boolResources.1.formed
      · rw [flagsEq];exact boolResources.1.coherent
      · rw [flagsEq]
        exact GeneralBorrowForestTagHighWaterHistory.weaken _ _ _ _ boolResources.1.below raise
    have boolOwnedFinal : OwnedOn (Authority bEntry.allocation.extra bCompletion held.global.protectedTags s.out.borrowed.child)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) bEntry.allocation.extra.locations := by
      rw [flagsEq]
      exact initialOwned
    exact ⟨⟨bEntry,bCompletion,bLive,(fun equal => False.elim (same equal)),(fun equal => False.elim (same equal)),boolRuntime,
      boolResources.2.1,boolResources.2.2.1,boolResources.2.2.2.1,initialNode,initialAt,initialTag,initialLeaf,initialHidden,initialActive,boolOwnedFinal,
      boolResources.2.2.2.2,originalNode,originalAt,originalProvenance,initialBounds,
      fun _ => CurrentCallEntryProtectionData.Facts.source_tag_absent s.facts positive same⟩⟩


end
end DuplicatePrefix.CurrentCallLenRootData
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallLenRootData").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Len root data dependency {dependency}"
