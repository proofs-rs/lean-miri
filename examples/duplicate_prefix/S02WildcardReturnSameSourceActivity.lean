import duplicate_prefix.S02HiddenLeafQuietWildcardRange
import duplicate_prefix.S02WildcardReturnSameSource
import duplicate_prefix.GeneralBorrowProtectedSiblingActivityConstructor
import duplicate_prefix.GeneralBorrowWildcardConstructorExact
import duplicate_prefix.S02HiddenLeafActivityRange
namespace DuplicatePrefix.S02WildcardReturnSameSourceActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual parentless wildcard-root insertion preserves an existing slot's
activity and node. Materialization changes only the fresh slot; there is no
ancestor SIFA walk in this constructor. -/
theorem constructor (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ActiveWithin actual.tree query .Write lower upper ∧ actual.tree.nodeAt query = some node := by
  obtain ⟨mapping,index,inserted,_rows,vacant,_graph,_size,_growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have different : query ≠ index := by
    intro same
    change tree.nodes.get query = some node at present
    rw [same,vacant] at present
    cases present
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have preserved := GeneralBorrowProtectedSiblingActivityConstructor.modified tree index query GeneralBorrowFreshChild.inside .Write
    (Size.ofBytes offset) (Size.ofBytes len) lower upper different runtime.formed.well bounds active
  dsimp only
  rw [actual]
  refine ⟨preserved,?_⟩
  exact (GeneralBorrowFreshLocation.get_other tree.nodes index query _ different).trans present
/-- Full registered wildcard return retag and concrete uninit Write retain
an old hidden source leaf's activity on its original byte window. -/
theorem preserved (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset : UInt64) (destination : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset 1)
    (distinct : tree.roots.toList.Nodup) (headroom : tree.nodes.size+1 < 65536)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper) :
    let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation fresh
    let read := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes 1)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let written := child.tree.performBorrowAccessRange (.concrete global.nextPointerTag)
      (Size.ofBytes offset) (Size.ofBytes 1) .Write registration.1.protectedTags .VisitChildrenOfAccessed
    ActiveWithin written.tree query .Write lower upper := by
  dsimp only
  obtain ⟨_allocated,_held,_frame,registeredRuntime,⟨registeredPositive⟩,tagFresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation fresh runtime none none none offset 1 destination
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation fresh
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes 1)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨readContract,readRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access tree registration.1 registeredRuntime
    (Size.ofBytes offset) (Size.ofBytes 1) .Read .VisitChildrenOfAccessed offset 1 registeredPositive distinct (by omega)
    (Nat.le_refl _) (Nat.le_refl _)
  have readActive := S02HiddenLeafQuietWildcardRange.wildcard tree registration.1 registeredRuntime offset 1 destination.bounds
    query node present leaf hidden lower upper active .Read .VisitChildrenOfAccessed
  have readPresent : accessed.tree.nodeAt query = some node := by
    change accessed.tree.nodes.get query = some node
    rw [readContract.nodes]
    exact present
  have afterFresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by
    rw [readContract.tags]
    exact tagFresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [readContract.nodes];omega
  have bounds : offset.toNat+(1 : UInt64).toNat ≤ accessed.tree.locations.size.bytes.toNat := by
    rw [readContract.capacity]
    exact destination.bounds
  obtain ⟨childActive,childPresent⟩ := constructor accessed.tree registration.1 readRuntime global.nextPointerTag afterFresh room
    offset 1 (by decide) bounds query node readPresent lower upper readActive
  obtain ⟨output,actual,_tag,_global,_frameEq,_readDone,_childDone,childRuntime,_capacity,growth,roots,
    newChild,tagged,_rootsEq,⟨childPositive⟩,_childActivity,newNode,newPresent,newTag,_parentless,_leaf,_hidden⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke tree global frame allocation runtime offset 1 destination
      distinct (by omega) (by omega) fresh
  have shape := actual
  simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag global fresh,
    Except.bind,Except.pure,bind,pure] at shape
  have outputEq := Except.ok.inj shape
  subst output
  have different : query ≠ newChild := by
    intro equal
    have sameNode : node = newNode := Option.some.inj ((equal ▸ childPresent).symm.trans newPresent)
    have tagEq : node.tag = global.nextPointerTag := (congrArg TreeNode.tag sameNode).trans newTag
    have below := GeneralBorrowForestTagHighWater.mapped tree global.protectedTags global.nextPointerTag node.tag
      runtime.below query (runtime.formed.allocator.nodeTags query node present)
    rw [tagEq] at below
    omega
  exact S02HiddenLeafActivityRange.concrete _ _ childRuntime global.nextPointerTag newChild newChild query
    (some global.nextPointerTag) offset 1 childPositive.base tagged node childPresent leaf hidden different lower upper childActive
    .Write .VisitChildrenOfAccessed

end DuplicatePrefix.S02WildcardReturnSameSourceActivity
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardReturnSameSourceActivity." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved same-allocation wildcard source activity dependency {dependency}"
