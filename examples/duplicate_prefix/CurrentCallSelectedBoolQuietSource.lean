import duplicate_prefix.CurrentCallEmptyEntryQuietCompleteBorrow
import duplicate_prefix.CurrentCallSelectedBoolWindow
import duplicate_prefix.CurrentCallResourceSourceActivity
namespace DuplicatePrefix.CurrentCallSelectedBoolQuietSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open Lean Elab Term in
elab "quiet_source_rule " suffix:str : term => do
  let found:=(←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked quiet-source helper {suffix.getString}"
noncomputable section
/-- The original live Bool grant cannot be the fresh zero-byte source node.
Only its original pointer identity, binding and pre-source high water matter. -/
theorem different {initial oldTracker oldData oldOwner before tracker data owner id offset}
    (old : UniformWindow initial oldTracker oldData oldOwner id offset 1 .ret)
    (oldRuntime : DuplicatePrefixBorrowContract.RuntimeFacts old.allocation.extra oldTracker.global)
    (current : UniformWindow before tracker data owner id offset 1 .ret)
    (pointer : current.pointer=old.pointer)
    (query : UniIndex) (node : TreeNode) (present : current.allocation.extra.nodes.get query=some node)
    (tag : node.tag=oldTracker.global.nextPointerTag) (hidden : node.isExposed=false) : query≠current.pointer.grant := by
  intro same
  obtain ⟨currentNode,currentAt,_,binding⟩:=current.binding
  rw [←same] at currentAt
  have equal : currentNode=node:=Option.some.inj (currentAt.symm.trans present)
  subst currentNode
  rw [pointer] at binding
  obtain ⟨oldNode,oldAt,_,oldBinding⟩:=old.binding
  cases prov : old.pointer.value.provenance with
  | concrete supplied parentTag=>
    rw [prov] at binding oldBinding
    have older:=GeneralBorrowParentTagInvariant.parent_below_fresh _ _ oldRuntime _ _ oldAt
    rw [←oldBinding.2,binding.2,tag] at older
    exact UInt64.lt_irrefl _ older
  | wildcard=>
    rw [prov] at binding
    rw [hidden] at binding
    cases binding

private theorem inactive_active (tree : BorrowTree) (query : UniIndex) (node : TreeNode)
    (inactive : Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) tree.locations) :
    GeneralBorrowFreshActiveWithin.ActiveWithin tree query .Write 0 0 := by
  intro point location atPoint state stored accessed kind associated
  obtain ⟨position,valid,_,_,data⟩:=atPoint
  have old:=inactive position valid
  have impossible : (true : Bool)=false := by
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,data,stored,Option.getD_some,accessed] using old
  cases impossible

private theorem fnentry {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (room : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (query : UniIndex) (node : TreeNode) (present : W.allocation.extra.nodes.get query=some node)
    (leaf : node.children=#[]) (hidden : node.isExposed=false) (different : query≠W.pointer.grant)
    (inactive : Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) W.allocation.extra.locations) :
    ∃ next,output.child.tree.nodes.get query=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧next.children=node.children ∧next.isExposed=node.isExposed ∧
      Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query next).accessed=false) output.child.tree.locations := by
  have bounds : start.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have bound:=(W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  have oldShort : W.allocation.extra.nodes.size<65536:=by omega
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295:=by omega
  obtain ⟨next,nextAt,tag,parent,children,exposure,_⟩:=(quiet_source_rule "CurrentCallResourceSourceActivity.fnentry_frame") W runtime frame fresh rfl distinct oldShort nodeRoom
    start 1 startEq rfl (by decide) bounds output actual query node present leaf hidden different 0 0 (inactive_active _ _ _ inactive)
  have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id fresh W.pointer.value.provenance start 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ fresh _ _ _))
  let registration:=registered tracker.global frame id fresh
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩:=CurrentCallResourceFnEntry.prepare_read_selected W runtime frame fresh rfl distinct oldShort start 1 startEq rfl bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id fresh W.pointer.value.provenance start 1).access.tree registration.1 at afterRuntime
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id fresh W.pointer.value.provenance start 1).access.tree.nodes=W.allocation.extra.nodes at nodes
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id fresh W.pointer.value.provenance start 1).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id fresh W.pointer.value.provenance start 1).access.tree.locations.size=W.allocation.extra.locations.size at bytes
  rw [←literalEq] at afterRuntime nodes tags bytes
  have targetAfter : output.access.tree.nodes.get query=some node := by rw [nodes];exact present
  have freshOld:=(GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id fresh runtime).2.2.2.2.2
  have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshOld
  have nodeCapacity : output.access.tree.nodes.size+1≤4294967295:=by rw [nodes];exact nodeRoom
  have afterBounds : start.toNat+1≤output.access.tree.locations.size.bytes.toNat:=by rw [bytes];exact bounds
  have registeredRuntime:=(GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id fresh runtime).2.2.2.1
  obtain ⟨G⟩:=CurrentCallResourceFnEntry.registered_geometry_selected W runtime frame fresh rfl
  have normals:=(quiet_source_rule "CurrentCallResourceSourceActivity.window_normals") (CurrentCallResourceFnEntry.registered_window W runtime frame fresh) G registeredRuntime rfl start 1 startEq rfl bounds
  have childEq : output.child=output.access.tree.newChild (Size.ofBytes start) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
      tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
  have quiet : Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) output.child.tree.locations := by
    cases prov : W.pointer.value.provenance with
    | concrete actualId parentTag=>
      obtain ⟨parentNode,parentAt,_,binds⟩:=W.binding
      rw [prov] at binds
      have taggedOld : W.allocation.extra.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact runtime.formed.allocator.nodeTags _ _ parentAt
      have quietRead:=CurrentCallEmptyEntryQuietRelease.concrete W.allocation.extra registration.1 registeredRuntime parentTag W.pointer.grant query start 1 bounds normals
        parentNode parentAt taggedOld node present leaf hidden different inactive .Read .VisitChildrenOfAccessed
      have readInactive : Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) output.access.tree.locations := by
        rw [literalEq]
        simpa only [CurrentCallTypedFnEntry.literal,prov,CandidateCurrentWindowPointerChecks.extraOf] using quietRead
      have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
      have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
      have ctor:=CurrentCallEmptyEntryQuietRelease.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode
        tagged parentAfter freshAfter nodeCapacity start 1 (by decide) afterBounds query node targetAfter readInactive
      rw [childEq]
      simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using ctor
    | wildcard=>
      have quietRead:=(quiet_source_rule "CurrentCallEmptyEntryQuietCompleteBorrow.wildcard_range") W.allocation.extra registration.1 registeredRuntime start 1 bounds query node present leaf hidden inactive .Read .VisitChildrenOfAccessed
      have readInactive : Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) output.access.tree.locations := by
        rw [literalEq]
        simpa only [CurrentCallTypedFnEntry.literal,prov,CandidateCurrentWindowPointerChecks.extraOf] using quietRead
      have ctor:=(quiet_source_rule "CurrentCallEmptyEntryQuietCompleteBorrow.wildcard_construct") output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity
        start afterBounds query node targetAfter readInactive
      rw [childEq]
      simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using ctor.2
  exact ⟨next,nextAt,tag,parent,children,exposure,(quiet_source_rule "CurrentCallEmptyEntryQuietCompleteBorrow.effective_node") _ query node next quiet⟩

theorem resources {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (room : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1) (tag : output.tag=tracker.global.nextPointerTag)
    (constructor : Before) (constructorPresent : Present (ActualWorld constructor) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id=tracker.global.rootTag? id)
 :
    let written:=output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed
    written.tree.roots.toList.Nodup ∧written.tree.nodes.size<65536 := by
  have bounds : start.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have bound:=(W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  have oldShort : W.allocation.extra.nodes.size<65536:=by omega
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295:=by omega
  have roots:=(quiet_source_rule "CurrentCallSelectedBoolCurrent.roots") W runtime frame fresh rfl distinct oldShort nodeRoom start 1 startEq rfl (by decide) bounds output actual
  have growth:=(quiet_source_rule "CurrentCallSelectedBoolCurrent.growth") W runtime frame fresh rfl distinct oldShort nodeRoom start 1 startEq rfl (by decide) bounds output actual
  have result:=CurrentCallSelectedBoolCurrent.operation_runtime W runtime frame fresh distinct room start startEq output child actual witness tag constructor constructorPresent rootTag .VisitChildrenOfAccessed
  constructor
  · rw [result.2.2.2.2.2.1];exact roots
  · rw [result.2.2.2.2.1];omega

/-- A current hidden empty-source leaf remains unaccessed through the SAME
selected Bool retag and Write. Optional parent interpretation is sufficient. -/
theorem operation {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (room : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1) (tag : output.tag=tracker.global.nextPointerTag)
    (constructor : Before) (constructorPresent : Present (ActualWorld constructor) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id=tracker.global.rootTag? id)
    (query : UniIndex) (node : TreeNode) (present : W.allocation.extra.nodes.get query=some node)
    (leaf : node.children=#[]) (hidden : node.isExposed=false) (different : query≠W.pointer.grant)
    (inactive : Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) W.allocation.extra.locations) :
    let written:=output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed
    ∃ next,written.tree.nodes.get query=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧next.children=node.children ∧next.isExposed=node.isExposed ∧
      Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query next).accessed=false) written.tree.locations := by
  obtain ⟨next,nextAt,nextTag,nextParent,nextLeaf,nextHidden,quiet⟩:=fnentry W runtime frame fresh distinct room start startEq output actual query node present leaf hidden different inactive
  have issued:=(CurrentCallBorrowIssuance.post W runtime output child start 1 witness tag constructor ⟨output.global,tracker.retagMode⟩ constructorPresent rootTag).2
  let current:=(quiet_source_rule "CurrentCallSelectedBoolWindow.childView") W output child start witness constructor constructorPresent issued
  obtain ⟨G⟩:=geometry_selected current (CandidateCurrentGrantRuntime.tree_rows output.child.tree output.global witness.runtime) rfl
  have bounds : start.toNat+1≤output.child.tree.locations.size.bytes.toNat := by
    rw [witness.capacity,W.issued.capability.treeExtent,←W.issued.capability.extent]
    have bound:=(W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    omega
  have normals:=(quiet_source_rule "CurrentCallResourceSourceActivity.window_normals") current G witness.runtime rfl start 1 startEq rfl bounds
  have childDifferent : query≠child := by
    intro same
    have found:=nextAt
    rw [same] at found
    have nodeEq : next=witness.node:=Option.some.inj (found.symm.trans witness.nodeAt)
    have older:=GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime query node present
    have equal:=nextTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans witness.tag)
    rw [equal,tag] at older
    exact UInt64.lt_irrefl _ older
  have tagged : output.child.tree.indexOfTag output.tag=some child := by rw [←witness.tag];exact witness.runtime.formed.allocator.nodeTags _ _ witness.nodeAt
  have quietWrite:=CurrentCallEmptyEntryQuietRelease.concrete output.child.tree output.global witness.runtime output.tag child query start 1 bounds normals
    witness.node witness.nodeAt tagged next nextAt (nextLeaf.trans leaf) (nextHidden.trans hidden) childDifferent quiet .Write .VisitChildrenOfAccessed
  have nodes:=(CurrentCallSelectedBoolCurrent.operation_runtime W runtime frame fresh distinct room start startEq output child actual witness tag
    constructor constructorPresent rootTag .VisitChildrenOfAccessed).2.2.2.2.1
  exact ⟨next,by rw [nodes];exact nextAt,nextTag,nextParent,nextLeaf,nextHidden,quietWrite⟩
end
end DuplicatePrefix.CurrentCallSelectedBoolQuietSource

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSelectedBoolQuietSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual empty live entry dependency {dependency}"
