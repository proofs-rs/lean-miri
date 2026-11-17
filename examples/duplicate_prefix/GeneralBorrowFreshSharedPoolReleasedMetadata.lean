import duplicate_prefix.GeneralBorrowFreshSharedNextPool
import duplicate_prefix.GeneralBorrowFreshSharedStageVacant
import duplicate_prefix.GeneralBorrowFreshSharedStageLookup
import duplicate_prefix.GeneralBorrowFreshReleaseVacantClean
import duplicate_prefix.GeneralBorrowFreshSharedReleaseWithin
namespace DuplicatePrefix.GeneralBorrowFreshSharedPoolReleasedMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowFreshAllocatorInvariant
open DuplicatePrefix.GeneralBorrowFreshStagePool DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem projection_size (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags) :
    (source_normal_projection tree location tags).topology.nodes.size = tree.nodes.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map,UniValMap.size]

set_option autoImplicit false in
structure Stage (before after : BorrowTree) (tag : BorTag) (inserted : UniIndex) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates after
  roots : after.roots = before.roots
  pool : Pool after.nodes after.tagMapping.deassigned
  accounting : Accounting after
  size : after.nodes.size ≤ before.nodes.size+1
  well : after.locations.WellFormed
  capacity : after.locations.size = before.locations.size
  lookup : after.indexOfTag tag = some inserted
  node : ∃ node, after.nodeAt inserted = some node ∧ node.tag = tag ∧ node.isExposed = false
  oldNode : ∀ query node, before.nodeAt query = some node →
    ∃ next, after.nodeAt query = some next ∧ next.tag = node.tag ∧ next.isExposed = node.isExposed
  oldLookup : ∀ old, tag ≠ old → after.indexOfTag old = before.indexOfTag old
  freshTag : ∀ next, GeneralBorrowTagMap.Fresh before.tagMapping next → tag ≠ next → GeneralBorrowTagMap.Fresh after.tagMapping next
  freshProtector : ∀ next, GeneralBorrowProtector.Fresh before next → tag ≠ next → GeneralBorrowProtector.Fresh after next
  vacant : ∀ query, before.nodes.get query = none → query ≠ inserted → after.nodes.get query = none
  clean : ∀ query, before.nodes.get query = none → query ≠ inserted →
    GeneralBorrowFreshFutureClean.Clean before query → GeneralBorrowFreshFutureClean.Clean after query

private theorem finish_one (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (protectedFlag : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (metadata : GeneralBorrowFreshStageMetadata.Output tree newTag parent offset len data protections protectedFlag)
    (pool : Pool (child data protections protectedFlag).tree.nodes (child data protections protectedFlag).tree.tagMapping.deassigned)
    (accounting : Accounting (child data protections protectedFlag).tree) :
    Nonempty (Stage tree (child data protections protectedFlag).tree newTag (index data)) := by
  have size : (child data protections protectedFlag).tree.nodes.size ≤ tree.nodes.size+1 := by
    rcases metadata.extension default default protections with appended | reused
    · have eq := appended.length
      rw [projection_size,projection_size] at eq
      omega
    · have eq := reused.length
      rw [projection_size,projection_size] at eq
      omega
  refine ⟨⟨metadata.certificates,metadata.roots,pool,accounting,size,metadata.well,metadata.capacity,
    metadata.lookup,metadata.node,?_,?_,metadata.freshTag,metadata.freshProtector,?_,metadata.futureClean⟩⟩
  · intro query node present
    exact GeneralBorrowFreshSharedStagePaths.old_node tree newTag parent offset len data protections protectedFlag writable owned query node present
  · intro old different
    exact GeneralBorrowFreshSharedStageLookup.old_lookup tree newTag parent offset len data protections protectedFlag writable owned old different
  · intro query vacant different
    exact GeneralBorrowFreshSharedStageVacant.vacant tree newTag parent offset len data protections protectedFlag writable owned query vacant different

/-- One actual shared stage summarized without assuming operation success. -/
theorem one (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (protectedFlag : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree) :
    Nonempty (Stage tree (child data protections protectedFlag).tree newTag (index data)) := by
  have metadata := GeneralBorrowFreshStageMetadata.build tree newTag parent offset len data protections protectedFlag writable owned
  have allocator := GeneralBorrowFreshStagePool.stage tree newTag parent offset len data protections protectedFlag writable owned pool accounting
  exact finish_one tree newTag parent offset len data protections protectedFlag writable owned metadata allocator.1 allocator.2

set_option autoImplicit false in
/-- Structural, allocator and remaining-slot hygiene after two actual shared
stages. Neither allocator emptiness nor a post-state borrow contract is assumed. -/
structure Output (before after : BorrowTree) (exprTag nextTag : BorTag) (expr child : UniIndex) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates after
  roots : after.roots = before.roots
  pool : Pool after.nodes after.tagMapping.deassigned
  accounting : Accounting after
  size : after.nodes.size ≤ before.nodes.size+2
  nodeFits : after.nodes.data.size ≤ 4294967296
  well : after.locations.WellFormed
  capacity : after.locations.size = before.locations.size
  oldNode : ∀ query node, before.nodeAt query = some node →
    ∃ next, after.nodeAt query = some next ∧ next.tag = node.tag ∧ next.isExposed = node.isExposed
  inserted : (∃ node, after.nodeAt expr = some node) ∧ (∃ node, after.nodeAt child = some node)
  oldLookup : ∀ old, exprTag ≠ old → nextTag ≠ old → after.indexOfTag old = before.indexOfTag old
  freshTag : ∀ next, GeneralBorrowTagMap.Fresh before.tagMapping next → exprTag ≠ next → nextTag ≠ next →
    GeneralBorrowTagMap.Fresh after.tagMapping next
  freshProtector : ∀ next, GeneralBorrowProtector.Fresh before next → exprTag ≠ next → nextTag ≠ next →
    GeneralBorrowProtector.Fresh after next
  vacant : ∀ query, before.nodes.get query = none → query ≠ expr → query ≠ child → after.nodes.get query = none
  clean : ∀ query, before.nodes.get query = none → query ≠ expr → query ≠ child →
    GeneralBorrowFreshFutureClean.Clean before query → GeneralBorrowFreshFutureClean.Clean after query

private theorem compose (before middle after : BorrowTree) (exprTag nextTag : BorTag) (expr child : UniIndex)
    (first : Stage before middle exprTag expr) (second : Stage middle after nextTag child)
    (room : before.nodes.size+1 ≤ 4294967295) : Nonempty (Output before after exprTag nextTag expr child) := by
  have size : after.nodes.size ≤ before.nodes.size+2 := by have := first.size;have := second.size;omega
  refine ⟨⟨second.certificates,second.roots.trans first.roots,second.pool,second.accounting,size,?_,second.well,
    second.capacity.trans first.capacity,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · change after.nodes.size ≤ 4294967296
    omega
  · intro query node present
    obtain ⟨middleNode,lookup,tag,exposure⟩ := first.oldNode query node present
    obtain ⟨afterNode,presentAfter,tagAfter,exposureAfter⟩ := second.oldNode query middleNode lookup
    exact ⟨afterNode,presentAfter,tagAfter.trans tag,exposureAfter.trans exposure⟩
  · obtain ⟨exprNode,exprPresent,_,_⟩ := first.node
    obtain ⟨afterExpr,afterExprPresent,_,_⟩ := second.oldNode expr exprNode exprPresent
    obtain ⟨childNode,childPresent,_,_⟩ := second.node
    exact ⟨⟨afterExpr,afterExprPresent⟩,⟨childNode,childPresent⟩⟩
  · intro old differentFirst differentSecond
    exact (second.oldLookup old differentSecond).trans (first.oldLookup old differentFirst)
  · intro next fresh differentFirst differentSecond
    exact second.freshTag next (first.freshTag next fresh differentFirst) differentSecond
  · intro next fresh differentFirst differentSecond
    exact second.freshProtector next (first.freshProtector next fresh differentFirst) differentSecond
  · intro query vacant differentFirst differentSecond
    exact second.vacant query (first.vacant query vacant differentFirst) differentSecond
  · intro query vacant differentFirst differentSecond clean
    exact second.clean query (first.vacant query vacant differentFirst) differentSecond (first.clean query vacant differentFirst clean)

private theorem finish_release (before final : BorrowTree) (protections : ProtectedTags)
    (exprTag nextTag : BorTag) (expr anchor root : UniIndex) (offset len : UInt64)
    (summary : Output before final exprTag nextTag expr anchor)
    (roots : final.roots = #[root]) (anchorNode : TreeNode)
    (present : final.nodeAt anchor = some anchorNode) (notExposed : anchorNode.isExposed = false)
    (tagPresent : final.indexOfTag nextTag = some anchor)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin final anchor .Read offset (offset+len))
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned final protections anchor .Read) offset (offset+len) final.locations)
    (positive : offset.toNat < (offset+len).toNat) :
    let result := final.releaseProtector nextTag protections
    result.status = .Released ∧ Nonempty (Output before result.tree exprTag nextTag expr anchor) := by
  let result := final.releaseProtector nextTag protections
  have activeRows := GeneralBorrowFreshActiveWithin.active_on final anchor .Read offset (offset+len) summary.well active
  have activeWrite := GeneralBorrowFreshActiveWithin.to_write final anchor offset (offset+len) active
  have released := GeneralBorrowFreshSharedReleaseWithin.release final protections nextTag anchor root .Read offset (offset+len)
    positive summary.nodeFits summary.certificates.depth summary.certificates.children anchorNode present notExposed roots
    summary.certificates.covered tagPresent active anchor summary.well activeWrite owned
  change result.status = .Released ∧ result.tree = {final with locations := result.tree.locations} ∧
    OwnedOn (GeneralBorrowRange.LocationOwned result.tree protections anchor .Read) offset (offset+len) result.tree.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin result.tree anchor .Write offset (offset+len) ∧
    result.tree.locations.WellFormed ∧ result.tree.locations.size = final.locations.size at released
  have frame := released.2.1
  have nodeEq := congrArg BorrowTree.nodes frame
  have nodes : result.tree.nodes = final.nodes := nodeEq
  have mappingEq := congrArg BorrowTree.tagMapping frame
  have mapping : result.tree.tagMapping = final.tagMapping := mappingEq
  have rootsEq := congrArg BorrowTree.roots frame
  have rootsFrame : result.tree.roots = final.roots := rootsEq
  let depth := GeneralBorrowFreshReadFrame.depth_on final result.tree nodes summary.certificates.depth
  have children : GeneralBorrowGraph.ChildNodes result.tree := by rw [frame];exact summary.certificates.children
  have covered : GeneralBorrowGraph.RootsCover result.tree := by rw [frame];exact summary.certificates.covered
  refine ⟨released.1,⟨⟨⟨depth,children,covered⟩,rootsFrame.trans summary.roots,?_,?_,?_,?_,released.2.2.2.2.1,
    released.2.2.2.2.2.trans summary.capacity,?_,?_,?_,?_,?_,?_,?_⟩⟩⟩
  · rw [nodes,mapping];exact summary.pool
  · unfold Accounting;rw [nodes,mapping];exact summary.accounting
  · rw [nodes];exact summary.size
  · rw [nodes];exact summary.nodeFits
  · intro query node presentOld
    obtain ⟨next,presentNext,tag,exposure⟩ := summary.oldNode query node presentOld
    refine ⟨next,?_,tag,exposure⟩
    change result.tree.nodes.get query = some next
    rw [nodes];exact presentNext
  · obtain ⟨exprNode,exprPresent⟩ := summary.inserted.1
    obtain ⟨childNode,childPresent⟩ := summary.inserted.2
    refine ⟨⟨exprNode,?_⟩,⟨childNode,?_⟩⟩
    · change result.tree.nodes.get expr = some exprNode
      rw [nodes];exact exprPresent
    · change result.tree.nodes.get anchor = some childNode
      rw [nodes];exact childPresent
  · intro old firstDifferent secondDifferent
    change result.tree.tagMapping.get old = before.tagMapping.get old
    rw [mapping]
    exact summary.oldLookup old firstDifferent secondDifferent
  · intro next fresh firstDifferent secondDifferent
    rw [mapping]
    exact summary.freshTag next fresh firstDifferent secondDifferent
  · intro next fresh firstDifferent secondDifferent
    unfold GeneralBorrowProtector.Fresh
    rw [nodes]
    exact summary.freshProtector next fresh firstDifferent secondDifferent
  · intro query vacant firstDifferent secondDifferent
    rw [nodes]
    exact summary.vacant query vacant firstDifferent secondDifferent
  · intro query vacant firstDifferent secondDifferent clean
    have finalVacant := summary.vacant query vacant firstDifferent secondDifferent
    have finalClean := summary.clean query vacant firstDifferent secondDifferent clean
    have preserved := GeneralBorrowFreshReleaseVacantClean.release final protections nextTag anchor root .Read offset (offset+len)
      positive summary.nodeFits summary.certificates.depth summary.certificates.children anchorNode present notExposed roots
      summary.certificates.covered tagPresent activeRows owned query finalVacant finalClean
    exact preserved.2.2


private theorem finish_two (before middle : BorrowTree) (protections : ProtectedTags)
    (exprTag nextTag : BorTag) (expr : UniIndex) (offset len : UInt64)
    (second : Data middle nextTag expr offset len)
    (firstSummary : Stage before middle exprTag expr)
    (owned : OwnedOn (Combined middle protections expr (extend (fun _ => true) expr.toNat)) offset (offset+len) middle.locations)
    (room : before.nodes.size+1 ≤ 4294967295) :
    let final := (child second protections true).tree
    let result := final.releaseProtector nextTag (registered protections nextTag true)
    result.status = .Released ∧ Nonempty (Output before result.tree exprTag nextTag expr (index second)) := by
  obtain ⟨secondSummary⟩ := one middle nextTag expr offset len second protections true
    (extend (fun _ => true) expr.toNat) owned firstSummary.pool firstSummary.accounting
  obtain ⟨summary⟩ := compose before middle (child second protections true).tree exprTag nextTag expr (index second) firstSummary secondSummary room
  have completed := run middle nextTag expr offset len second protections true (extend (fun _ => true) expr.toNat) owned
  have childOwned : OwnedOn (GeneralBorrowRange.LocationOwned (child second protections true).tree
      (registered protections nextTag true) (index second) .Read) offset (offset+len) (child second protections true).tree.locations := by
    intro position valid positive lower upper
    exact (completed.2.2.1 position valid positive lower upper).1
  have lenNonzero : len.toNat ≠ 0 := fun zero => second.nonzero (UInt64.toNat_inj.mp (by simpa using zero))
  have sizeBound : middle.locations.size.bytes.toNat < 2^64 := UInt64.toNat_lt_size middle.locations.size.bytes
  have positive : offset.toNat < (offset+len).toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by have bounds := second.bounds;omega)]
    omega
  obtain ⟨node,present,tag,notExposed⟩ := secondSummary.node
  exact finish_release before (child second protections true).tree (registered protections nextTag true) exprTag nextTag
    expr (index second) second.root offset len summary (secondSummary.roots.trans second.roots) node present notExposed
    secondSummary.lookup completed.2.2.2 childOwned positive

/-- Original coherent allocator data form two actual shared stages and the
actual child-protector release. All graph, free-pool, accounting, old-node/tag,
future-tag freshness and remaining-vacant-slot cleanliness facts are derived;
no post-state metadata or operation-success premise is accepted. -/
theorem build (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanVacant : ∀ query, tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean tree query)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations) :
    let choice := GeneralBorrowFreshSharedNextPool.next tree protections target exprTag nextTag offset len first
      pool accounting room freshTag freshProtector different cleanVacant owned
    let final := (child choice.val protections true).tree
    let result := final.releaseProtector nextTag (registered protections nextTag true)
    result.status = .Released ∧ Nonempty (Output tree result.tree exprTag nextTag (index first) (index choice.val)) := by
  generalize nextEq : GeneralBorrowFreshSharedNextPool.next tree protections target exprTag nextTag offset len first
    pool accounting room freshTag freshProtector different cleanVacant owned = choice
  rcases choice with ⟨second,secondFacts⟩
  dsimp only at ⊢
  have initial : OwnedOn (Combined tree protections target (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ protections target (owned position valid positive lower upper)
  have completed := run tree exprTag target offset len first protections false (fun _ => true) initial
  have firstOwned := completed.2.2.1
  have regFalse : registered protections exprTag false = protections := by simp only [registered,Bool.false_eq_true,↓reduceIte]
  rw [regFalse] at firstOwned
  obtain ⟨firstSummary⟩ := one tree exprTag target offset len first protections false (fun _ => true) initial pool accounting
  exact finish_two tree (child first protections false).tree protections exprTag nextTag (index first) offset len second firstSummary firstOwned room


/-- Full initial vacancy hygiene becomes full resulting vacancy hygiene; the
consumed slots cannot be selected again while their newly inserted nodes live. -/
theorem clean_all {before after : BorrowTree} {exprTag nextTag : BorTag} {expr child : UniIndex}
    (metadata : Output before after exprTag nextTag expr child)
    (initial : ∀ query, before.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean before query)
    (query : UniIndex) (vacant : after.nodes.get query = none) : GeneralBorrowFreshFutureClean.Clean after query := by
  have initialVacant : before.nodes.get query = none := by
    cases present : before.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,presentNext,_,_⟩ := metadata.oldNode query node present
      change after.nodes.get query = some next at presentNext
      rw [vacant] at presentNext
      cases presentNext
  have differentFirst : query ≠ expr := by
    obtain ⟨node,present⟩ := metadata.inserted.1
    intro equal
    change after.nodes.get expr = some node at present
    rw [equal,present] at vacant
    cases vacant
  have differentSecond : query ≠ child := by
    obtain ⟨node,present⟩ := metadata.inserted.2
    intro equal
    change after.nodes.get child = some node at present
    rw [equal,present] at vacant
    cases vacant
  exact metadata.clean query initialVacant differentFirst differentSecond (initial query initialVacant)

/-- Reserve the following mutable constructor's slot using only original room,
original parent presence and the derived released metadata. No old Slot or rank
slack is required; the permission premise follows separately via clean_all. -/
noncomputable def next_slot {before after : BorrowTree} {exprTag nextTag : BorTag} {expr child : UniIndex}
    (metadata : Output before after exprTag nextTag expr child)
    (parent : UniIndex) (oldNode : TreeNode) (present : before.nodeAt parent = some oldNode)
    (room : before.nodes.size+2 ≤ 4294967295) :
    GeneralBorrowFreshReborrowStages.Slot after
      (GeneralBorrowTightAncestry.tight after.nodes metadata.certificates.depth) parent := by
  let node := Classical.choose (metadata.oldNode parent oldNode present)
  have nodePresent := (Classical.choose_spec (metadata.oldNode parent oldNode present)).1
  have fits : after.tagMapping.mapping.size ≤ 4294967295 := by
    have accounting := metadata.accounting
    have size := metadata.size
    unfold Accounting at accounting
    omega
  exact GeneralBorrowFreshAllocatorInvariant.slot after
    (GeneralBorrowTightAncestry.tight after.nodes metadata.certificates.depth) parent metadata.pool
    (empty_aligned after metadata.accounting) (fun _ => fits)
    (GeneralBorrowTightAncestry.present_slack after.nodes metadata.certificates.depth parent node nodePresent)

end DuplicatePrefix.GeneralBorrowFreshSharedPoolReleasedMetadata
