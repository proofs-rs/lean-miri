import duplicate_prefix.S05WildcardProtectedRootCompletion
import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.GeneralBorrowWildcardRootRangeTransport

/-! Initial raw authority at one chosen origin transports through actual
protected wildcard-root construction. The physical new root has no parent;
its completed parent remains that SAME exposed origin across the whole window.
No legacy Positive, future table or whole-Joint preservation is assumed. -/
namespace DuplicatePrefix.S05WildcardProtectedRootAuthority
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralRangeMapOrigins S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem model_location (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (mapping : UniKeyMap BorTag) (child origin : UniIndex) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (originLive : ∃ node, tree.nodes.get origin = some node)
    (offset len : UInt64) (location : LocationTree)
    (authority : Authority tree completion protections origin location) :
    Authority (GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len) (extend completion child origin) protections child
      {location with perms := location.perms.insert child GeneralBorrowFreshChild.inside} := by
  intro index node present
  by_cases new : index = child
  · subst index
    have raw : RawState {location with perms := location.perms.insert child GeneralBorrowFreshChild.inside} child node =
        GeneralBorrowFreshChild.inside := by simp [RawState,GeneralBorrowFreshLocation.get_same]
    constructor
    · intro _
      rw [raw]
      simp [LocalWrite,GeneralBorrowFreshChild.inside,LocationState.possible,Permission.isUnique]
    · intro impossible
      exact False.elim (impossible (.refl child))
  · change (tree.nodes.insert child (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get index = some node at present
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ new] at present
    have raw : RawState {location with perms := location.perms.insert child GeneralBorrowFreshChild.inside} index node =
        RawState location index node := by simp only [RawState,GeneralBorrowFreshLocation.get_other _ _ _ _ new]
    have original := authority index node present
    have ancestry := child_ancestry_iff tree completion complete child origin vacant originLive index
    constructor
    · intro below
      rcases ancestry.mp below with same | old
      · exact False.elim (new same)
      · simpa only [raw] using original.1 old
    · intro outside
      simpa only [raw] using original.2 (fun old => outside (ancestry.mpr (.inr old)))

private theorem model_owned (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (mapping : UniKeyMap BorTag) (child origin : UniIndex) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (originLive : ∃ node, tree.nodes.get origin = some node)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion protections origin) offset (offset+len) tree.locations) :
    let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len
    OwnedOn (Authority model (extend completion child origin) protections child) offset (offset+len) model.locations := by
  dsimp only
  exact GeneralBorrowWildcardRootRangeTransport.transport tree.locations child GeneralBorrowFreshChild.inside
    (Size.ofBytes offset) (Size.ofBytes len) well bounds (Authority tree completion protections origin) _ owned
    (fun location authority => model_location tree completion protections complete mapping child origin tag vacant originLive offset len location authority)

/-- The actual allocator and range materializer produce protected-child raw
rights from the initial chosen-origin tables, with one unchanged origin choice. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true)
    (origin : UniIndex) (originNode : TreeNode) (originAt : tree.nodes.get origin = some originNode)
    (exposed : originNode.isExposed = true) (older : originNode.tag.value < tag.value)
    (originPosition : Nat) (originRoot : UniIndex)
    (originSlot : tree.roots[originPosition]? = some originRoot) (originPath : Path tree originRoot origin)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags origin) offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        S05WildcardProtectedRootCompletion.RootFrame tree actual.tree child origin tag ∧
        Completes actual.tree (extend completion child origin) ∧
        OwnedOn (Authority actual.tree (extend completion child origin) global.protectedTags child)
          offset (offset+len) actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,roots,frame,completed⟩ :=
    S05WildcardProtectedRootCompletion.construct tree global completion runtime complete tag fresh room tagBound held
      origin originNode originAt exposed older originPosition originRoot originSlot originPath offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,roots,frame,completed,?_⟩
  obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  rw [actual] at afterRuntime lookup ⊢
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside offset len
  have ownLookup : model.indexOfTag tag = some index :=
    afterRuntime.formed.allocator.nodeTags index _ (GeneralBorrowFreshLocation.get_same tree.nodes index _)
  have same : index = child := Option.some.inj (ownLookup.symm.trans lookup)
  have authority := model_owned tree completion global.protectedTags complete mapping index origin tag vacant ⟨originNode,originAt⟩
    offset len runtime.formed.well bounds owned
  subst child
  exact authority
/-- Every output segment overlapping the disjoint window is an unchanged
prepared value. Actual iterator splitting may change all segment indices. -/
private theorem modify_outside_owned (map : DedupRangeMap LocationTree) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (modify : LocationTree → LocationTree) (idempotent : ∀ location, modify (modify location) = modify location)
    (P : LocationTree → Prop) (lower upper : UInt64)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.bytes.toNat ∨ (offset.bytes+len.bytes).toNat ≤ point.toNat)
    (owned : OwnedOn P lower upper map) :
    OwnedOn P lower upper (map.modifyRange offset len (fun _ location => modify location)).state := by
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len (fun _ location => modify location)
  have good := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := refines_owned_on map prepared.state P lower upper good.1.wellFormed good.2.1 owned
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by
    change position < changed.state.entries.size at valid
    omega
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len (fun _ location => modify location)
    (fun _ location => idempotent location) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    split at known <;> exact known
  rw [rangeEq] at start stop
  by_cases selected : position ∈ prepared.positions.toList
  · obtain ⟨cursor,bounded,same⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr selected)
    have segmentValid : cursor < prepared.segments.size := by rw [←good.1.lengths];exact bounded
    have contained := good.2.2 cursor segmentValid
    have selectedEq := good.1.selected cursor bounded
    rw [selectedEq.2] at contained
    change offset.bytes.toNat ≤ prepared.state.entries[prepared.positions[cursor]].range.start.toNat ∧
      prepared.state.entries[prepared.positions[cursor]].range.stop.toNat ≤ (offset.bytes+len.bytes).toNat at contained
    simp only [same] at contained
    have segmentPositive := (GeneralRangeMapGeometry.facts prepared.state good.1.wellFormed (by omega)).2.1 position oldValid
    by_cases earlier : lower.toNat ≤ prepared.state.entries[position].range.start.toNat
    · have outside := disjoint prepared.state.entries[position].range.start earlier start
      exact False.elim (by omega)
    · have outside := disjoint lower (Nat.le_refl _) positive
      exact False.elim (by omega)
  · simp only [show ¬position ∈ (map.iterMut offset len).positions.toList from selected,↓reduceIte] at entryEq
    rw [entryEq]
    exact preparedOwned position oldValid positive start stop

private theorem no_vacant_ancestor (tree : BorrowTree) (completion : Completion)
    (complete : Completes tree completion) (child target : UniIndex)
    (vacant : tree.nodes.get child = none) (live : ∃ node, tree.nodes.get target = some node)
    (path : Below completion child target) : False := by
  induction path with
  | refl => obtain ⟨node,present⟩ := live; rw [vacant] at present; cases present
  | @step predecessor target edge path induction =>
    exact induction ((complete.2.2.2.2.2.2 target predecessor edge).2.1)


private theorem model_disjoint_location (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (mapping : UniKeyMap BorTag) (child origin target : UniIndex) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (targetLive : ∃ node, tree.nodes.get target = some node)
    (offset len : UInt64) (location : LocationTree) (clean : location.perms.get child = none)
    (authority : Authority tree completion protections target location) :
    Authority (GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len) (extend completion child origin) protections target location := by
  intro index node present
  change (tree.nodes.insert child (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get index = some node at present
  by_cases new : index = child
  · subst index
    rw [GeneralBorrowFreshLocation.get_same] at present
    have nodeEq : node = WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None := Option.some.inj present.symm
    have outside : ¬Below (extend completion child origin) child target := by
      intro path
      exact no_vacant_ancestor tree completion complete child target vacant targetLive
        ((old_ancestry_iff tree completion complete child origin vacant targetLive).mp path)
    constructor
    · intro impossible; exact False.elim (outside impossible)
    · intro _
      simp [RawState,clean,nodeEq,WildcardHitZeroConstructor.rootNode,TreeNode.defaultLocationState,
        ForeignWrite,LocationState.possible,Permission.isUnique]
  · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ new] at present
    have original := authority index node present
    have ancestry := old_ancestry_iff tree completion complete child origin vacant targetLive (ancestor := index)
    exact ⟨fun below => original.1 (ancestry.mp below),
      fun outside => original.2 (fun below => outside (ancestry.mpr below))⟩

private theorem model_disjoint_owned (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (mapping : UniKeyMap BorTag) (child origin target : UniIndex) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (targetLive : ∃ node, tree.nodes.get target = some node)
    (offset len lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get child = none)
    (owned : OwnedOn (Authority tree completion protections target) lower upper tree.locations) :
    let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len
    OwnedOn (Authority model (extend completion child origin) protections target) lower upper model.locations := by
  have initial : OwnedOn (fun location => Authority tree completion protections target location ∧ location.perms.get child = none)
      lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨owned position valid positive start stop,clean position valid⟩
  have unchanged := modify_outside_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => {location with perms := location.perms.insert child GeneralBorrowFreshChild.inside})
    (fun location => by simp only [GeneralBorrowFreshInstallation.insert_idempotent])
    _ lower upper disjoint initial
  dsimp only
  intro position valid positive start stop
  obtain ⟨oldAuthority,oldClean⟩ := unchanged position valid positive start stop
  exact model_disjoint_location tree completion protections complete mapping child origin target tag vacant targetLive
    offset len _ oldClean oldAuthority

/-- A disjoint old grant keeps its authority even in the same allocation.
The new root is a dormant protected reservation outside its source window. -/
theorem disjoint (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true)
    (origin : UniIndex) (originNode : TreeNode) (originAt : tree.nodes.get origin = some originNode)
    (exposed : originNode.isExposed = true) (older : originNode.tag.value < tag.value)
    (originPosition : Nat) (originRoot : UniIndex)
    (originSlot : tree.roots[originPosition]? = some originRoot) (originPath : Path tree originRoot origin)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (targetLive : ∃ node, tree.nodes.get target = some node)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child, actual.tree.indexOfTag tag = some child ∧
      Completes actual.tree (extend completion child origin) ∧
      OwnedOn (Authority actual.tree (extend completion child origin) global.protectedTags target)
        lower upper actual.tree.locations := by
  obtain ⟨_,afterRuntime,_,_,child,lookup,_,frame,completed⟩ :=
    S05WildcardProtectedRootCompletion.construct tree global completion runtime complete tag fresh room tagBound held
      origin originNode originAt exposed older originPosition originRoot originSlot originPath offset len nonzero bounds
  refine ⟨child,lookup,completed,?_⟩
  obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  rw [actual] at afterRuntime lookup ⊢
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside offset len
  have ownLookup : model.indexOfTag tag = some index :=
    afterRuntime.formed.allocator.nodeTags index _ (GeneralBorrowFreshLocation.get_same tree.nodes index _)
  have same : index = child := Option.some.inj (ownLookup.symm.trans lookup)
  have clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get index = none := by
    intro position valid
    exact (runtime.formed.profile position valid).vacant index vacant
  have authority := model_disjoint_owned tree completion global.protectedTags complete mapping index origin target tag vacant targetLive
    offset len lower upper runtime.formed.well bounds disjoint clean owned
  subst child
  exact authority

end DuplicatePrefix.S05WildcardProtectedRootAuthority

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05WildcardProtectedRootAuthority." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved wildcard protected authority dependency {dependency}"
