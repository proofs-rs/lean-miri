import duplicate_prefix.CurrentCallResourceCurrentRelease
import duplicate_prefix.S05CompletedChildReanchor
import duplicate_prefix.CurrentCallResourceSingleBoolRelease
import duplicate_prefix.CurrentCallResourceEmptyRootRelease
import duplicate_prefix.S03NonliveEmptyMetadata

namespace DuplicatePrefix.CurrentCallEmptyLedgerRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem released_pair (result : BorrowTree.ProtectorReleaseResult) (done : result.status=.Released) :
    result=⟨result.tree,.Released⟩ := by
  cases result
  cases done
  rfl

/-- A real nonlive ledger entry is skipped using its actual metadata. The Bool
child is then released and the WHOLE frame ends before its parent is reanchored. -/
private theorem nonlive {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (short : B.allocation.extra.nodes.size<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (present : B.allocation.extra.nodes.get B.pointer.grant=some node) (hidden : node.isExposed=false)
    (sourceId : AllocId) (sourceTag : BorTag) (metadataTag : Option BorTag)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory sourceId metadataTag)
    (absent : before.memory.live.find? (fun row=>row.1==sourceId)=none)
    (sourceHidden : ∀index current,B.allocation.extra.nodes.get index=some current→current.tag=sourceTag→current.isExposed=false)
    (frame : FrameState) (tags : frame.protectedTags=#[(sourceId,sourceTag),(id,node.tag)])
    (original : UniIndex) (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start : UInt64) (startEq : start.toNat=offset)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write start (start+1))
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (allocationEq : entry.allocation=B.allocation) :
    Nonempty (CurrentCallResourceCurrentRelease.Released B frame original start entry) := by
  have first:=(B.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have extent:=B.issued.capability.extent
  have limit:=UInt64.toNat_lt B.allocation.byteSize.bytes
  have fits : start.toNat+1<2^64:=by omega
  have noWrap : (start+1).toNat=start.toNat+1:=by
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]
  have positive : start.toNat<(start+1).toNat:=by rw [noWrap];omega
  obtain ⟨done,shape,afterRuntime,parents,capacity,owned⟩:=CurrentCallResourceRelease.release B rfl runtime concrete distinct short node present hidden
    start 1 startEq rfl positive noWrap active
  let result:=B.allocation.extra.releaseProtector node.tag tracker.global.protectedTags
  let memory:=StackPopRelease.commitTree before.memory id entry result.tree
  have nodeAt : result.tree.nodes.get B.pointer.grant=some node:=by rw [shape];exact present
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame result.tree frame:=by
    intro row member index current currentAt sameTag
    rw [tags] at member
    have alternatives : row=(sourceId,sourceTag) ∨row=(id,node.tag) := by simpa using member
    rcases alternatives with sourceEq | boolEq
    · subst row
      apply sourceHidden index current
      · rw [shape] at currentAt
        exact currentAt
      · exact sameTag
    · subst row
      have one:=afterRuntime.formed.allocator.nodeTags index current currentAt
      have two:=afterRuntime.formed.allocator.nodeTags B.pointer.grant node nodeAt
      rw [sameTag] at one
      have indexEq : index=B.pointer.grant:=Option.some.inj (one.symm.trans two)
      subst index
      have nodeEq : current=node:=Option.some.inj (currentAt.symm.trans nodeAt)
      subst current
      exact hidden
  have finalRuntime:=S05CompletedChildReanchor.runtime_end_call result.tree tracker.global frame afterRuntime hiddenFrame
  have member : (id,node.tag)∈frame.protectedTags.toList:=by rw [tags];simp
  have parentOwned:=S05CompletedChildReanchor.owned_end_call result.tree B.precise.completion tracker.global frame id
    B.pointer.grant original node start (start+1) edge nodeAt member owned
  have actualRelease : entry.allocation.extra.releaseProtector node.tag tracker.global.protectedTags=⟨result.tree,.Released⟩:=by
    rw [allocationEq]
    exact released_pair _ done
  refine ⟨⟨memory,result.tree,?_,?_,finalRuntime,parents,shape,capacity,?_,?_,parentOwned⟩⟩
  · rw [tags]
    obtain ⟨info,lookup,notLive⟩:=S03NonliveEmptyMetadata.known before.memory sourceId metadataTag metadata absent
    exact StackPopRelease.Plan.skip sourceId sourceTag info [(id,node.tag)] before.memory memory lookup notLive
      (StackPopRelease.Plan.live id node.tag entry result.tree [] before.memory memory live actualRelease (.nil _))
  · simpa only [allocationEq] using StackPopRelease.lookup_commit_same before.memory id entry result.tree
  · rw [shape]
    exact distinct
  · rw [shape]
    exact short


/-- Current source release data, independent of its ABI representation and
of source byte ownership. The index states the exact real optional ledger row. -/
inductive SourceLedger (before : Before) (boolTree : BorrowTree) : Option (AllocId × BorTag) → Type where
  | none : SourceLedger before boolTree none
  | nonlive (id : AllocId) (tag : BorTag) (metadataTag : Option BorTag)
      (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id metadataTag)
      (absent : before.memory.live.find? (fun row=>row.1==id)=none)
      (hidden : ∀index node,boolTree.nodes.get index=some node→node.tag=tag→node.isExposed=false) :
      SourceLedger before boolTree (some (id,tag))
  | live (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (present : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
      (index : UniIndex) (node : TreeNode)
      (tagged : entry.allocation.extra.indexOfTag tag=some index)
      (nodeAt : entry.allocation.extra.nodeAt index=some node) (hidden : node.isExposed=false)
      (quiet : S04ReturnReleaseInactive.Quiescent entry.allocation.extra index)
      (hiddenOnBool : ∀index current,boolTree.nodes.get index=some current→current.tag=tag→current.isExposed=false) :
      SourceLedger before boolTree (some (id,tag))

namespace SourceLedger
/-- Representation-only transport along an actual unchanged heap. No source
row is supplied where the ledger records absence. -/
def transport {before after : Before} {tree source}
    (ledger : SourceLedger before tree source) (memory : after.memory=before.memory) : SourceLedger after tree source := by
  cases ledger with
  | none=>exact .none
  | nonlive id tag metadataTag metadata absent hidden=>
    exact .nonlive id tag metadataTag (by rw [memory];exact metadata) (by rw [memory];exact absent) hidden
  | live id tag entry present index node tagged nodeAt hidden quiet hiddenOnBool=>
    exact .live id tag entry (by rw [memory];exact present) index node tagged nodeAt hidden quiet hiddenOnBool
end SourceLedger

def rows (source : Option (AllocId × BorTag)) (id : AllocId) (tag : BorTag) :=
  match source with | none=>#[(id,tag)] | some row=>#[row,(id,tag)]

/-- One release consumer for every optional source ledger. No source family,
source authority, fabricated tree or successful future release is assumed. -/
theorem release {before tracker data owner id offset source}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (short : B.allocation.extra.nodes.size<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (present : B.allocation.extra.nodes.get B.pointer.grant=some node) (hidden : node.isExposed=false)
    (ledger : SourceLedger before B.allocation.extra source)
    (frame : FrameState) (tags : frame.protectedTags=rows source id node.tag)
    (original : UniIndex) (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start : UInt64) (startEq : start.toNat=offset)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write start (start+1))
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (allocationEq : entry.allocation=B.allocation) :
    Nonempty (CurrentCallResourceCurrentRelease.Released B frame original start entry) := by
  cases ledger with
  | none=>exact CurrentCallResourceSingleBoolRelease.release B runtime distinct short concrete node present hidden frame tags original edge start startEq active entry live allocationEq
  | nonlive sourceId sourceTag metadataTag metadata absent hiddenSource=>
    exact nonlive B runtime distinct short concrete node present hidden sourceId sourceTag metadataTag metadata absent hiddenSource frame tags original edge start startEq active entry live allocationEq
  | live sourceId sourceTag sourceEntry sourceLive index sourceNode tagged sourceAt sourceHidden quiet hiddenSource=>
    exact CurrentCallResourceEmptyRootRelease.release B runtime distinct short concrete node present hidden sourceId sourceTag sourceEntry sourceLive index sourceNode tagged sourceAt sourceHidden quiet hiddenSource frame tags original edge start startEq active entry live allocationEq
end
end DuplicatePrefix.CurrentCallEmptyLedgerRelease
