import duplicate_prefix.GenericFunctionTagFormation
import duplicate_prefix.GeneralBorrowFreshMetadataChildProtector
import duplicate_prefix.GeneralBorrowFreshSharedStagePaths

namespace DuplicatePrefix.GenericTagHighWaterPreservation
open Miri Miri.ABI Miri.Interpreter Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericFunctionTagFormation GeneralBorrowFreshLocation GeneralBorrowFreshReadFrame GeneralBorrowView GeneralRangeMapOrigins
open GeneralBorrowFreshSharedSequence GeneralBorrowFreshReleaseMixed GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
def NodesBelow (nodes : UniValMap TreeNode) (counter : BorTag) : Prop :=
  ∀ query node, nodes.get query = some node → node.tag.value.toNat < counter.value.toNat

set_option autoImplicit false in
private theorem nodes_of_entries (tree : BorrowTree) (counter : BorTag)
    (below : ∀ row ∈ tree.nodes.entries, row.2.tag.value.toNat < counter.value.toNat) : NodesBelow tree.nodes counter := by
  intro query node present
  exact below (query,node) (Array.mem_def.mpr ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes query node).mpr present))

set_option autoImplicit false in
private theorem entries_of_nodes (tree : BorrowTree) (counter : BorTag) (below : NodesBelow tree.nodes counter) :
    ∀ row ∈ tree.nodes.entries, row.2.tag.value.toNat < counter.value.toNat := by
  intro row member
  exact below row.1 row.2 ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_def.mp member))

set_option autoImplicit false in
private theorem inserted (nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode) (counter : BorTag)
    (old : NodesBelow nodes counter) (new : node.tag.value.toNat < counter.value.toNat) : NodesBelow (nodes.insert index node) counter := by
  intro query next present
  by_cases same : query=index
  · subst query
    rw [get_same] at present
    cases present
    exact new
  · rw [get_other nodes index query node same] at present
    exact old query next present

set_option autoImplicit false in
private theorem shape (before after : BorrowTree) (protections : ProtectedTags) (counter : BorTag)
    (same : treeShape after = treeShape before) (below : Below before protections counter) : Below after protections counter := by
  refine ⟨?_,?_,below.protectors⟩
  · rw [GeneralBorrowFreshMetadata.mapping before after same]
    exact below.mapping
  · apply entries_of_nodes
    intro query node present
    obtain ⟨old,lookup,tagEq,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm query node present
    have oldBound := nodes_of_entries before counter below.nodes query old lookup
    simpa only [tagEq] using oldBound

set_option autoImplicit false in
private theorem staged (tree : BorrowTree) (protections : ProtectedTags) (counter : BorTag)
    (index parent : UniIndex) (parentNode newNode : TreeNode) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (below : Below tree protections counter)
    (parentPresent : tree.nodeAt parent = some parentNode) (new : newNode.tag.value.toNat < counter.value.toNat)
    (mappingBound : ∀ row ∈ mapping.mapping, row.1.value.toNat < counter.value.toNat) :
    Below (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations) protections counter := by
  have original := nodes_of_entries tree counter below.nodes
  have parentBound := original parent parentNode parentPresent
  have first := inserted tree.nodes index newNode counter original new
  have second := inserted (tree.nodes.insert index newNode) parent {parentNode with children := parentNode.children.push index}
    counter first parentBound
  refine ⟨mappingBound,?_,below.protectors⟩
  apply entries_of_nodes
  exact second

set_option autoImplicit false in
private theorem pushed (mapping : UniKeyMap BorTag) (tag counter : BorTag) (index : UniIndex) (pool : Array UniIndex)
    (below : ∀ row ∈ mapping.mapping, row.1.value.toNat < counter.value.toNat)
    (new : tag.value.toNat < counter.value.toNat) :
    ∀ row ∈ (⟨mapping.mapping.push (tag,index),pool⟩ : UniKeyMap BorTag).mapping, row.1.value.toNat < counter.value.toNat := by
  intro row member
  simp only [Array.mem_push] at member
  rcases member with old | same
  · exact below row old
  · subst row;exact new

set_option autoImplicit false in
private theorem protected_insert (protections : ProtectedTags) (tag counter : BorTag) (kind : ProtectorKind)
    (below : ∀ row ∈ protections.entries, row.1.value.toNat < counter.value.toNat)
    (new : tag.value.toNat < counter.value.toNat) :
    ∀ row ∈ (protections.insert tag kind).entries, row.1.value.toNat < counter.value.toNat := by
  intro row member
  simp only [ProtectedTags.insert,Array.mem_push,Array.mem_filter] at member
  rcases member with old | same
  · exact below row old.1
  · subst row;exact new

set_option autoImplicit false in
/-- Real protector insertion is bounded by the genuinely incremented counter. -/
theorem register_below (tree : BorrowTree) (protections : ProtectedTags) (counter : BorTag)
    (fresh : counter.value < 18446744073709551615) (below : Below tree protections counter) (isProtected : Bool) :
    Below tree (GeneralBorrowFreshSharedSequence.registered protections counter isProtected) (TypedRetagEmpty.successorTag counter fresh) := by
  have value := GenericFunctionEntryNumerics.successor_value counter fresh
  have strict : counter.value.toNat < (TypedRetagEmpty.successorTag counter fresh).value.toNat := by omega
  have raised : Below tree protections (TypedRetagEmpty.successorTag counter fresh) := by
    refine ⟨?_,?_,?_⟩
    · intro row member;have old:=below.mapping row member;omega
    · intro row member;have old:=below.nodes row member;omega
    · intro row member;have old:=below.protectors row member;omega
  cases isProtected with
  | false => exact raised
  | true => exact ⟨raised.mapping,raised.nodes,protected_insert protections counter _ .StrongProtector raised.protectors strict⟩

set_option autoImplicit false in
/-- Actual newPointerTag completion and the corresponding optional registration
both preserve the high-water invariant at the returned counter. -/
theorem allocate_registered (tree : BorrowTree) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (below : Below tree global.protectedTags global.nextPointerTag) (isProtected : Bool) :
    ∃ allocated, global.newPointerTag = .ok (allocated,global.nextPointerTag) ∧
      Below tree (GeneralBorrowFreshSharedSequence.registered allocated.protectedTags global.nextPointerTag isProtected) allocated.nextPointerTag := by
  refine ⟨{global with nextPointerTag := TypedRetagEmpty.successorTag global.nextPointerTag fresh},TypedRetagEmpty.allocate_tag global fresh,?_⟩
  exact register_below tree global.protectedTags global.nextPointerTag fresh below isProtected

set_option autoImplicit false in
/-- A newly allocated source borrow tree contains only its original root tag.
The per-global protected-table high-water condition remains an explicit input. -/
theorem new_tree (root counter : BorTag) (size : Size) (protections : ProtectedTags)
    (old : root.value.toNat < counter.value.toNat)
    (protectedBound : ∀ row ∈ protections.entries, row.1.value.toNat < counter.value.toNat) :
    Below (BorrowTree.new root size) protections counter := by
  refine ⟨?_,?_,protectedBound⟩
  · change ∀ row ∈ #[(root,(⟨0⟩ : UniIndex))], row.1.value.toNat < counter.value.toNat
    intro row member
    simp only [Array.mem_singleton] at member
    subst row;exact old
  · apply entries_of_nodes
    let node : TreeNode := {tag := root,parent := none,children := #[],defaultInitialPermission := .newDisabled,defaultInitialSifa := .None,isExposed := false}
    have empty : NodesBelow ({} : UniValMap TreeNode) counter := by intro query node present;simp [UniValMap.get] at present
    have result := inserted ({} : UniValMap TreeNode) ⟨0⟩ node counter empty old
    exact result

set_option autoImplicit false in
/-- A source counter allocation followed by BorrowTree.new establishes the
initial tree invariant. No earlier tree invariant is needed; only the original
per-global protected-table bound and counter capacity are inputs. -/
theorem allocate_tree (global : GlobalState) (size : Size)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (protectedBound : ∀ row ∈ global.protectedTags.entries, row.1.value.toNat < global.nextPointerTag.value.toNat)
    (isProtected : Bool) :
    ∃ allocated, global.newPointerTag = .ok (allocated,global.nextPointerTag) ∧
      Below (BorrowTree.new global.nextPointerTag size)
        (GeneralBorrowFreshSharedSequence.registered allocated.protectedTags global.nextPointerTag isProtected) allocated.nextPointerTag := by
  let counter := TypedRetagEmpty.successorTag global.nextPointerTag fresh
  have strict : global.nextPointerTag.value.toNat < counter.value.toNat := by
    have value := GenericFunctionEntryNumerics.successor_value global.nextPointerTag fresh
    change counter.value.toNat = global.nextPointerTag.value.toNat+1 at value
    omega
  have raised : ∀ row ∈ global.protectedTags.entries, row.1.value.toNat < counter.value.toNat := by
    intro row member
    have old := protectedBound row member
    omega
  have registeredBound : ∀ row ∈ (GeneralBorrowFreshSharedSequence.registered global.protectedTags global.nextPointerTag isProtected).entries,
      row.1.value.toNat < counter.value.toNat := by
    cases isProtected with
    | false => exact raised
    | true => exact protected_insert global.protectedTags global.nextPointerTag counter .StrongProtector raised strict
  refine ⟨{global with nextPointerTag := counter},TypedRetagEmpty.allocate_tag global fresh,?_⟩
  exact new_tree global.nextPointerTag counter size _ strict registeredBound


set_option autoImplicit false in
theorem append_child (input : GeneralBorrowFreshMetadataChildShared.Input) (protections : ProtectedTags) (counter : BorTag)
    (below : Below input.tree protections counter) (new : input.newTag.value.toNat < counter.value.toNat) :
    Below (GeneralBorrowFreshMetadataChildShared.result input) protections counter := by
  apply shape _ _ protections counter (GeneralBorrowFreshMetadataChildShared.shape input)
  exact staged input.tree protections counter _ input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
    _ _ below input.parentPresent new (pushed input.tree.tagMapping input.newTag counter _ _ below.mapping new)

set_option autoImplicit false in
theorem reuse_child (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (protections : ProtectedTags) (counter : BorTag)
    (below : Below input.tree protections counter) (new : input.newTag.value.toNat < counter.value.toNat) :
    Below (GeneralBorrowFreshMetadataChildSharedReuse.result input) protections counter := by
  apply shape _ _ protections counter (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
  exact staged input.tree protections counter _ input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
    _ _ below input.parentPresent new (pushed input.tree.tagMapping input.newTag counter _ _ below.mapping new)

set_option autoImplicit false in
/-- The actual ranged parent Read and actual append/reuse shared construction
preserve the high-water invariant at the incremented runtime counter. Both
operation outcomes are derived from initial ownership and structural Data. -/
theorem shared_stage (tree : BorrowTree) (counter : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree counter parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : GeneralRangeMapOrigins.OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (freshCounter : counter.value < 18446744073709551615) (below : Below tree protections counter) :
    (read data protections isProtected).status = .Completed ∧ (child data protections isProtected).outcome = .ok () ∧
      Below (child data protections isProtected).tree
        (GeneralBorrowFreshSharedSequence.registered protections counter isProtected)
        (TypedRetagEmpty.successorTag counter freshCounter) := by
  have completed := GeneralBorrowFreshSharedSequence.run tree counter parent offset len data protections isProtected writable owned
  refine ⟨completed.1,completed.2.1,?_⟩
  let accessed := read data protections isProtected
  have owners := GeneralBorrowFreshStageMetadata.registered_owned tree counter parent offset len data protections isProtected writable owned
  have good := GeneralBorrowFreshMixedRead.access tree (registered protections counter isProtected) data.parentTag parent data.root
    (Size.ofBytes offset) (Size.ofBytes len) writable .VisitChildrenOfAccessed data.nodeFits data.depth data.children data.parentNode
    data.parentPresent data.roots data.covered data.parentTagPresent data.well offset (offset+len) owners data.bounds
    (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ OwnedOn (Combined accessed.tree (registered protections counter isProtected) parent writable)
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections counter isProtected) .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : accessed.tree.nodes = tree.nodes := nodeEq
  have mappingEq := congrArg BorrowTree.tagMapping framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := mappingEq
  have rootsEq := congrArg BorrowTree.roots framed
  have roots : accessed.tree.roots = tree.roots := rootsEq
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping counter := by rw [mapping];exact data.tagFresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact data.bounds
  let slot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree data.depth depth nodes mapping rfl parent data.slot

  have registeredBound := register_below tree protections counter freshCounter below isProtected
  have accessedBelow : Below accessed.tree (GeneralBorrowFreshSharedSequence.registered protections counter isProtected)
      (TypedRetagEmpty.successorTag counter freshCounter) := by
    rw [framed]
    exact ⟨registeredBound.mapping,registeredBound.nodes,registeredBound.protectors⟩
  have newBound : counter.value.toNat < (TypedRetagEmpty.successorTag counter freshCounter).value.toNat := by
    have value := GenericFunctionEntryNumerics.successor_value counter freshCounter
    omega
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨accessed.tree,depth,children,covered,data.parentTag,counter,parent,data.parentNode,tagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
    exact append_child input _ _ accessedBelow newBound
  | reuse query available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨accessed.tree,depth,children,covered,data.parentTag,counter,parent,data.parentNode,tagPresent,parentPresent,fresh,
        query,available,valid,vacant,slack,isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
    exact reuse_child input _ _ accessedBelow newBound

end DuplicatePrefix.GenericTagHighWaterPreservation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GenericTagHighWaterPreservation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved high-water preservation dependency {name}: {dependency}"
