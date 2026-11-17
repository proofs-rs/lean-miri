import duplicate_prefix.GeneralBorrowObserverReadRelease
import duplicate_prefix.GeneralBorrowReadProtectorReleaseEndCall
namespace DuplicatePrefix.GeneralBorrowObserverReadRestore
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowObserverReadRow (virtual)
open GeneralBorrowObserverReadRange (Observer)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Removing a tag absent from the actual table is exactly a no-op. -/
theorem remove_absent (tags : ProtectedTags) (tag : BorTag) (absent : tags.contains tag = false) :
    tags.remove tag = tags := by
  have filtered : tags.entries.filter (fun entry => entry.1 != tag) = tags.entries := by
    apply Array.filter_eq_self.mpr
    intro entry member
    have different : entry.1 ≠ tag := by
      intro same
      have held := (GeneralBorrowRelease.contains_iff_entry tags tag).mpr ⟨entry,member,same⟩
      rw [absent] at held
      contradiction
    exact bne_iff_ne.mpr different
  cases tags
  simpa only [ProtectedTags.remove] using congrArg ProtectedTags.mk filtered

/-- The virtual two-tag table is the REAL child-only endCall table whenever
the intermediate shared temporary carries no protector. -/
theorem virtual_eq (global : GlobalState) (allocation : AllocId) (childTag temporaryTag : BorTag)
    (unprotected : global.protectedTags.contains temporaryTag = false) :
    virtual global allocation childTag temporaryTag =
      (global.endCall (({} : FrameState).addProtector allocation childTag)).protectedTags := by
  let first := global.endCall (({} : FrameState).addProtector allocation childTag)
  have stillAbsent : first.protectedTags.contains temporaryTag = false := by
    cases held : first.protectedTags.contains temporaryTag with
    | false => rfl
    | true =>
      have earlier := GeneralBorrowRelease.end_call_weakens global _ temporaryTag held
      rw [unprotected] at earlier
      contradiction
  change (first.endCall (({} : FrameState).addProtector allocation temporaryTag)).protectedTags = first.protectedTags
  simpa only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty] using
    remove_absent first.protectedTags temporaryTag stillAbsent

/-- Actual Read-helper release and singleton endCall restore the original
mutable observer's full Positive window. Current independent observer data are
carried through the real scan; source Read-only data supply the actual operations.
The intermediate shared temporary's unprotected status identifies the virtual
ledger with the real endCall table, rather than postulating final permissions. -/
theorem release_end_call (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (anchor selected temporary observer : UniIndex) (maximum : Option BorTag)
    (anchorNode temporaryNode observerNode : TreeNode)
    (present : tree.nodeAt anchor = some anchorNode) (childEdge : anchorNode.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some observer)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (childHidden : anchorNode.isExposed = false) (temporaryHidden : temporaryNode.isExposed = false)
    (temporaryUnprotected : global.protectedTags.contains temporaryNode.tag = false)
    (observerPath : ((source_normal_projection tree default
      (virtual global allocation anchorNode.tag temporaryNode.tag)).topology.ancestorPath observer.toNat).getLast? = some selected.toNat)
    (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags anchor selected maximum offset len)
    (observerOwned : OwnedOn (Observer tree (virtual global allocation anchorNode.tag temporaryNode.tag) observer)
      offset (offset+len) tree.locations)
    (tagged : tree.indexOfTag anchorNode.tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read offset (offset+len)) :
    let actual := tree.releaseProtector anchorNode.tag global.protectedTags
    let after := global.endCall (({} : FrameState).addProtector allocation anchorNode.tag)
    actual.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree after ∧
    Nonempty (GeneralBorrowReadRowRange.Positive actual.tree after.protectedTags anchor selected maximum offset len) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree after.protectedTags
      (some observer) (some selected) maximum offset len) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree anchor .Write offset (offset+len) ∧
    actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have nonempty : offset.toNat < (offset+len).toNat := by rw [sum];have p:=positive.positive;omega
  have runtimeRows : Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  have initial : OwnedOn (GeneralBorrowObserverReadRelease.Row tree global allocation anchor selected maximum
      anchorNode.tag temporaryNode.tag observer) offset (offset+len) tree.locations := by
    intro position valid positiveWindow start stop
    exact ⟨positive.rows position valid positiveWindow start stop,observerOwned position valid positiveWindow start stop⟩
  obtain ⟨_,_,pairedRows,_,_,_,_⟩ := GeneralBorrowObserverReadRelease.release tree global before anchorNode.tag anchor selected
    maximum offset (offset+len) nonempty anchorNode present childHidden allocation temporary observer temporaryNode observerNode
    childEdge temporaryPresent temporaryEdge observerPresent temporaryHidden observerPath distinct order short tagged active
    before.formed.well runtimeRows initial
  obtain ⟨done,runtime,⟨sourceAfter⟩,activity,_,_,frame,capacity⟩ := GeneralBorrowReadProtectorReleaseEndCall.release_end_call tree global before
    allocation anchorNode.tag anchor selected maximum offset len positive anchorNode present rfl childHidden tagged distinct order short active
  let actual := tree.releaseProtector anchorNode.tag global.protectedTags
  let after := global.endCall (({} : FrameState).addProtector allocation anchorNode.tag)
  have virtualSame := virtual_eq global allocation anchorNode.tag temporaryNode.tag temporaryUnprotected
  have observerAfter : OwnedOn (Observer actual.tree after.protectedTags observer) offset (offset+len) actual.tree.locations := by
    intro position valid positiveWindow start stop
    have current := (pairedRows position valid positiveWindow start stop).2
    change Observer actual.tree (virtual global allocation anchorNode.tag temporaryNode.tag) observer _ at current
    rw [virtualSame] at current
    exact current
  have observerPresentAfter : actual.tree.nodeAt observer = some observerNode := by
    rw [frame]
    exact observerPresent
  have pathAfter : ∀ location, ((source_normal_projection actual.tree location after.protectedTags).topology.ancestorPath observer.toNat).getLast? = some selected.toNat := by
    intro location
    rw [frame]
    exact observerPath
  have restored : DuplicatePrefixBorrowAuthorization.Positive actual.tree after.protectedTags
      (some observer) (some selected) maximum offset len := {
    positive := sourceAfter.positive
    bounds := sourceAfter.bounds
    sourcePresent := by intro found equal;cases equal;exact ⟨observerNode,observerPresentAfter⟩
    wildcardRoot := by intro impossible;cases impossible
    rows := by
      intro position valid positiveWindow start stop
      obtain ⟨readRow⟩ := sourceAfter.rows position valid positiveWindow start stop
      obtain ⟨normal⟩ := observerAfter position valid positiveWindow start stop
      refine ⟨{
        wildcard := by intro impossible;cases impossible
        rootPath := ?_
        rootPresent := readRow.rootPresent
        cutoff := readRow.cutoff
        normal := ?_
        callbacks := readRow.callbacks}⟩
      · intro found equal
        cases equal
        exact pathAfter _
      · intro found equal
        cases equal
        exact ⟨normal⟩ }
  exact ⟨done,runtime,⟨sourceAfter⟩,⟨restored⟩,activity,frame,capacity⟩
end DuplicatePrefix.GeneralBorrowObserverReadRestore
