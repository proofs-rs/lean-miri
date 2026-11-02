import duplicate_prefix.GeneralBorrowTwoRootPolicySeed

namespace DuplicatePrefix.GeneralBorrowTwoRootExposedPolicySeed
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowExposureRelease GeneralRangeMapState RangeMapNonempty
open GeneralBorrowTwoRootConstructed (first second unique exposedLocation exposedTree rootNode)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Both root caches are formed by actual exposeTag operations. -/
def location : LocationTree :=
  {GeneralBorrowTwoRootConstructed.location with exposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩]⟩⟩}
def parentNode (tag : BorTag) : TreeNode := {GeneralBorrowTwoRootPolicySeed.parentNode tag with isExposed := true}
def tree (rootTag newTag : BorTag) : BorrowTree :=
  {GeneralBorrowTwoRootPolicySeed.activated rootTag newTag with
    nodes := ⟨#[some (rootNode rootTag true),some (parentNode newTag)]⟩
    locations := homogeneous 1 location}

set_option autoImplicit false in
private theorem cache_expose (nodes : UniValMap TreeNode) (node : TreeNode)
    (present : nodes.get second = some node) (parentless : node.parent = none) :
    GeneralBorrowTwoRootConstructed.location.exposedCache.updateExposure nodes second .None .Write =
      ⟨location.exposedCache,.ok ()⟩ := by
  unfold ExposedCache.updateExposure
  simp only [reduceCtorEq,↓reduceIte,Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have initial : scan () (GeneralBorrowTwoRootConstructed.location.exposedCache,some second,0,.ok (),true) =
      .yield (location.exposedCache,none,1,.ok (),false) := by
    simp only [scan,show ¬0>nodes.size from by omega,↓reduceIte,present,parentless,Option.isNone_none]
    with_unfolding_all rfl
  have done : scan () (location.exposedCache,none,1,.ok (),false) =
      .done (location.exposedCache,none,1,.ok (),false) := by simp only [scan,Bool.false_eq_true,↓reduceIte,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [initial,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [done,bind,pure]
  rfl

set_option autoImplicit false in
/-- Actual second-root exposure after policy activation. No exposure flag or
cache postcondition is supplied as an assumption. -/
theorem expose_second (rootTag newTag : BorTag) (different : rootTag ≠ newTag) :
    (GeneralBorrowTwoRootPolicySeed.activated rootTag newTag).exposeTag {} newTag = ⟨tree rootTag newTag,.ok ()⟩ := by
  have fresh : GeneralBorrowTagMap.Fresh (exposedTree rootTag).tagMapping newTag := by
    intro row member
    change row ∈ #[(rootTag,first)] at member
    have same := Array.mem_singleton.mp member
    subst row
    exact different
  have tagged : (GeneralBorrowTwoRootPolicySeed.activated rootTag newTag).indexOfTag newTag = some second :=
    GeneralBorrowTagMap.pushed_get_new (exposedTree rootTag).tagMapping newTag fresh second #[]
  have present : (GeneralBorrowTwoRootPolicySeed.activated rootTag newTag).nodeAt second = some (GeneralBorrowTwoRootPolicySeed.parentNode newTag) := rfl
  let marked := {(GeneralBorrowTwoRootPolicySeed.activated rootTag newTag) with nodes :=
    ((GeneralBorrowTwoRootPolicySeed.activated rootTag newTag).nodes.insert second (parentNode newTag))}
  have markedPresent : marked.nodes.get second = some (parentNode newTag) := by
    dsimp only [marked]
    exact GeneralBorrowFreshLocation.get_same (GeneralBorrowTwoRootPolicySeed.activated rootTag newTag).nodes second (parentNode newTag)
  have update := cache_expose marked.nodes (parentNode newTag) markedPresent rfl
  have locations : (GeneralBorrowTwoRootPolicySeed.activated rootTag newTag).locations = homogeneous 1 GeneralBorrowTwoRootConstructed.location := rfl
  unfold BorrowTree.exposeTag
  simp only [tagged,present,GeneralBorrowTwoRootPolicySeed.parentNode,Bool.false_eq_true,↓reduceIte]
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,locations,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  simp only [show (homogeneous (1 : UInt64) GeneralBorrowTwoRootConstructed.location).entries.size = 1 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn'_cons,List.forIn'_nil,bind,pure]
  simp only [index_exact (homogeneous (1 : UInt64) GeneralBorrowTwoRootConstructed.location) 0 (by change 0<1;decide)]
  simp only [homogeneous,Array.getElem_singleton] at *
  simp only [GeneralBorrowTwoRootConstructed.location,unique,second,UniValMap.get,Array.getElem?_singleton,Option.getD_some,
    Permission.strongestAllowedLocalAccess]
  dsimp only [marked] at update
  erw [update]
  simp only [Except.mapError,Except.map,bind,pure]
  erw [setAtPos_exact (homogeneous (1 : UInt64) GeneralBorrowTwoRootConstructed.location) 0 (by change 0<1;decide)]
  with_unfolding_all rfl

set_option autoImplicit false in
private theorem node_cases (rootTag newTag : BorTag) (query : UniIndex) (node : TreeNode)
    (present : (tree rootTag newTag).nodeAt query = some node) :
    (query=first ∧ node=rootNode rootTag true) ∨ (query=second ∧ node=parentNode newTag) := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid (tree rootTag newTag).nodes query node present
  change query.toNat < 2 at valid
  have cases : query.toNat=0 ∨ query.toNat=1 := by omega
  rcases cases with h | h
  · have same : query=first := GeneralBorrowNodeUpdate.index_injective query first h
    subst query
    change some (rootNode rootTag true) = some node at present
    exact Or.inl ⟨rfl,(Option.some.inj present).symm⟩
  · have same : query=second := GeneralBorrowNodeUpdate.index_injective query second h
    subst query
    change some (parentNode newTag) = some node at present
    exact Or.inr ⟨rfl,(Option.some.inj present).symm⟩

set_option autoImplicit false in
def depth (rootTag newTag : BorTag) : ParentDepth (tree rootTag newTag).nodes where
  depth := fun _ => 0
  bounded := by intro query node present;omega
  parent := by
    intro query node present before edge
    rcases node_cases rootTag newTag query node present with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> cases edge

set_option autoImplicit false in
theorem children (rootTag newTag : BorTag) : GeneralBorrowGraph.ChildNodes (tree rootTag newTag) := by
  intro query node present child member
  rcases node_cases rootTag newTag query node present with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> cases member

set_option autoImplicit false in
theorem covered (rootTag newTag : BorTag) : GeneralBorrowGraph.RootsCover (tree rootTag newTag) := by
  intro query node present parentless
  rcases node_cases rootTag newTag query node present with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp [tree,GeneralBorrowTwoRootPolicySeed.activated,GeneralBorrowTwoRootPolicySeed.tree]


set_option autoImplicit false in
theorem projection (rootTag newTag : BorTag) :
    source_normal_projection (tree rootTag newTag) location {} = GeneralBorrowTwoRootPolicySeed.activatedNormal := by
  unfold_general_projection
  unfold_general_topology
  with_unfolding_all rfl

set_option autoImplicit false in
def forest (rootTag newTag : BorTag) :
    GeneralBorrowForest.Forest (source_normal_projection (tree rootTag newTag) location {}).topology := by
  rw [projection]
  exact GeneralBorrowTwoRootPolicySeed.normal_forest

set_option autoImplicit false in
theorem owned (rootTag newTag : BorTag) (kind : AccessKind) :
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection (tree rootTag newTag) location {}) second.toNat kind := by
  rw [projection]
  have old := GeneralBorrowTwoRootPolicySeed.activated_owned rootTag newTag kind
  rw [GeneralBorrowTwoRootPolicySeed.activated_projection] at old
  exact old

set_option autoImplicit false in
theorem foreign_data (rootTag newTag : BorTag) (ordered : rootTag.value ≤ newTag.value) :
    GeneralBorrowWildcardLeaf.Data (tree rootTag newTag) location first (rootNode rootTag true) newTag :=
  ⟨rfl,rfl,rfl,rfl,rfl,ordered⟩

set_option autoImplicit false in
theorem shape (rootTag newTag : BorTag) :
    (tree rootTag newTag).roots = #[first,second] ∧
    (tree rootTag newTag).nodeAt first = some (rootNode rootTag true) ∧
    (tree rootTag newTag).nodeAt second = some (parentNode newTag) ∧
    (rootNode rootTag true).parent = none ∧ (parentNode newTag).parent = none ∧
    (rootNode rootTag true).isExposed = true ∧ (parentNode newTag).isExposed = true ∧
    location.perms.get first = some unique ∧ location.perms.get second = some unique ∧
    location.exposedCache.nodes.get first = some ⟨1,1⟩ ∧ location.exposedCache.nodes.get second = some ⟨1,1⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

set_option autoImplicit false in
theorem read_visited (rootTag newTag : BorTag) :
    ((source_normal_projection (tree rootTag newTag) location {}).performAccess
      second.toNat .Read .VisitChildrenOfAccessed).visited = [⟨1,.LocalAccess⟩] := by
  rw [projection]
  with_unfolding_all rfl

set_option autoImplicit false in
theorem read_frozen_others (rootTag newTag : BorTag) :
    ∀ event ∈ ((source_normal_projection (tree rootTag newTag) location {}).performAccess
        second.toNat .Read .VisitChildrenOfAccessed).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → (tree rootTag newTag).nodeAt index = some node →
      index ≠ second → node.isExposed = true →
      ∃ state, location.perms.get index = some state ∧ state.permission = .Frozen := by
  rw [read_visited]
  intro event member index node converted present different exposed
  have same : event = ⟨1,.LocalAccess⟩ := List.mem_singleton.mp member
  subst event
  have idx : index = second := (Option.some.inj converted).symm
  exact False.elim (different idx)

set_option autoImplicit false in
theorem read_outside (rootTag newTag : BorTag) :
    ∀ event ∈ ((source_normal_projection (tree rootTag newTag) location {}).topology.traverse second.toNat
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection (tree rootTag newTag) location {}) .Read)).2,
      event.node ≠ first.toNat := by
  rw [projection]
  have events : (GeneralBorrowTwoRootPolicySeed.activatedNormal.topology.traverse second.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped GeneralBorrowTwoRootPolicySeed.activatedNormal .Read)).2 = [⟨1,.LocalAccess⟩] := by
    with_unfolding_all rfl
  rw [events]
  intro event member
  have same : event = ⟨1,.LocalAccess⟩ := List.mem_singleton.mp member
  subst event
  decide +kernel


set_option autoImplicit false in
/-- Composition with the actual initial policy seed. The second exposure is
performed on the actual activating Write result. No full retag caller or
Rust-history reachability is claimed. -/
theorem construct (rootTag newTag : BorTag) (ordered : rootTag.value < newTag.value) :
    let exposed := (BorrowTree.new rootTag (Size.ofBytes 1)).exposeTag {} rootTag
    let built := exposed.tree.newChild Size.ZERO .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowTwoRootPolicySeed.reserved)
      GeneralBorrowTwoRootPolicySeed.policy.outsidePermission GeneralBorrowTwoRootPolicySeed.policy.protector.isSome
    let written := built.tree.performBorrowAccessRange (.concrete newTag) (Size.ofBytes 0) (Size.ofBytes 1)
      .Write {} .VisitChildrenOfAccessed
    exposed.outcome = .ok () ∧ built.outcome = .ok () ∧ written.status = .Completed ∧
      written.tree.exposeTag {} newTag = ⟨tree rootTag newTag,.ok ()⟩ := by
  have different : rootTag ≠ newTag := by
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    have h := UInt64.lt_iff_toNat_lt.mp ordered
    omega
  have previous := (GeneralBorrowTwoRootPolicySeed.construct rootTag newTag ordered).2.2
  dsimp only at previous ⊢
  refine ⟨previous.1,previous.2.1,previous.2.2.1,?_⟩
  rw [previous.2.2.2.1]
  exact expose_second rootTag newTag different

end DuplicatePrefix.GeneralBorrowTwoRootExposedPolicySeed
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoRootExposedPolicySeed.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved exposed policy seed dependency {name}: {dependency}"
