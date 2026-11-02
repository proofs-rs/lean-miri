import duplicate_prefix.GeneralBorrowWildcardConstructorExact
import duplicate_prefix.GeneralBorrowWildcardRootCache
import duplicate_prefix.GeneralBorrowWildcardRootInstalled
namespace DuplicatePrefix.GeneralBorrowWildcardConstructorRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifaPermissionConsistency GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

private theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess held = .Access sifa)
    (insideInitial : inside.permission.isInitial = true)
    (insideForeign : inside.permission.strongestIdempotentForeignAccess held = .Access inside.idempotentForeignAccess)
    (defaultConsistent : Consistent (WildcardHitZeroConstructor.rootNode tag outside sifa).defaultLocationState (global.protectedTags.contains tag))
    (insideConsistent : Consistent inside (global.protectedTags.contains tag))
    (defaultPossible : (WildcardHitZeroConstructor.rootNode tag outside sifa).defaultLocationState.possible = true)
    (insidePossible : inside.possible = true)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new (Size.ofBytes len) inside) outside held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child,actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        (∃ node,actual.tree.nodeAt child = some node ∧ node.tag = tag ∧ node.parent = none ∧ node.isExposed = false) ∧
        OwnedOn (fun location => location.perms.get child = some inside) offset (offset+len) actual.tree.locations := by
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room outside sifa
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    outside sifa inside held initial nonunique foreign insideInitial insideForeign offset len nonzero bounds
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag outside sifa inside offset len
  have scalar := GeneralBorrowWildcardConstructorState.stage tree global runtime mapping index tag outside sifa inside vacant
    offset len bounds defaultConsistent insideConsistent defaultPossible insidePossible
  have geometry := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => {location with perms := location.perms.insert index inside}) runtime.formed.well bounds
  have state : GeneralBorrowStructuralHistoryState.State model :=
    ⟨GeneralBorrowStructuralHistoryState.graph_locations _ _ graph,geometry.1⟩
  obtain ⟨depth⟩ := runtime.formed.depth
  have caches := GeneralBorrowWildcardRootCache.constructor tree depth mapping index tag outside sifa inside offset len
    vacant monotone runtime.formed.well bounds global.protectedTags runtime.coherent
  have full : DuplicatePrefixBorrowContract.RuntimeFacts model global := by
    refine ⟨⟨state,scalar.1⟩,caches,scalar.2,⟨?_,runtime.below.protectors⟩⟩
    intro row member
    change row ∈ mapping.mapping at member
    rw [rows] at member
    rcases Array.mem_push.mp member with old | added
    · exact runtime.below.mapping row old
    · subst row
      exact tagBound
  have rootGeometry := GeneralBorrowPositiveWildcardConstructor.geometry tree mapping index tag outside sifa inside offset len
  have newPresent : (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa).nodeAt index =
      some (WildcardHitZeroConstructor.rootNode tag outside sifa) := GeneralBorrowFreshLocation.get_same tree.nodes index _
  have lookup : model.indexOfTag tag = some index := graph.allocator.nodeTags index _ newPresent
  dsimp only
  rw [actual]
  refine ⟨rfl,full,congrArg Size.ofBytes geometry.2,growth,index,lookup,rootGeometry.1,
    ⟨WildcardHitZeroConstructor.rootNode tag outside sifa,rootGeometry.2,rfl,rfl,rfl⟩,?_⟩
  exact GeneralBorrowWildcardRootInstalled.installed tree.locations index inside (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well bounds

/-- Positive shared wildcard-root constructor from raw runtime and policy
metadata. The real allocator append/reuse, all SIFA/Clean/possible/cache and
high-water invariants, root geometry and actual stored rows are derived.
No exposure/permission profile, noFree or operation success is assumed. -/
theorem shared (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (aligned : global.protectedTags.contains tag = held)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child,actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        (∃ node,actual.tree.nodeAt child = some node ∧ node.tag = tag ∧ node.parent = none ∧ node.isExposed = false) ∧
        OwnedOn (fun location => location.perms.get child = some GeneralBorrowFreshAnchor.sharedState)
          offset (offset+len) actual.tree.locations := by
  have foreign : Permission.Frozen.strongestIdempotentForeignAccess held = .Access .Read := by cases held <;> rfl
  apply construct tree global runtime tag fresh room tagBound .Frozen .Read GeneralBorrowFreshAnchor.sharedState held
    rfl rfl foreign rfl foreign _ _ rfl rfl offset len nonzero bounds
  · change Consistent ⟨.Frozen,false,.Read⟩ _
    rw [aligned]
    exact GeneralBorrowSifaPermissionConsistency.frozen false held
  · rw [aligned]
    exact GeneralBorrowSifaPermissionConsistency.frozen true held

/-- Actual protected mutable FnEntry wildcard-root constructor, with the
pinned ReservedFrz(false)/SIFA.None policy. Full runtime and isolated-root
resources follow from raw input, even with arbitrary coherent reuse pools. -/
theorem protected_mutable (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child,actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        (∃ node,actual.tree.nodeAt child = some node ∧ node.tag = tag ∧ node.parent = none ∧ node.isExposed = false) ∧
        OwnedOn (fun location => location.perms.get child = some GeneralBorrowFreshChild.inside)
          offset (offset+len) actual.tree.locations := by
  apply construct tree global runtime tag fresh room tagBound (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true
    rfl rfl rfl rfl rfl _ _ rfl rfl offset len nonzero bounds
  · change Consistent ⟨.ReservedFrz false,false,.None⟩ _
    rw [held]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation false
  · rw [held]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation true
end DuplicatePrefix.GeneralBorrowWildcardConstructorRuntime
