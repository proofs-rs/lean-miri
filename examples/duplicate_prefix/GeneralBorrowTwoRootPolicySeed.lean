import duplicate_prefix.GeneralBorrowTwoRootConstructed
import Miri.TreeBorrows.RetagPolicy

namespace DuplicatePrefix.GeneralBorrowTwoRootPolicySeed
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowExposureRelease GeneralRangeMapState RangeMapNonempty
open GeneralBorrowTwoRootConstructed (first second unique exposedLocation exposedTree rootNode)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Exact default mutable policy for an Unpin, UnsafeUnpin, Freeze byte. -/
def policy : RetagPolicy.NewPermission := ⟨.ReservedFrz false,.ReservedIM,.ReservedFrz false,none⟩
def reserved : LocationState := ⟨.ReservedFrz false,true,.Read⟩
theorem create_policy : RetagPolicy.create ⟨true,true,true⟩ .Mutable .Default ⟨false,false⟩ = some policy := by
  with_unfolding_all rfl
theorem initial_state : RetagPolicy.initialLocationState policy true = .ok reserved := by
  with_unfolding_all rfl

def parentNode (tag : BorTag) : TreeNode := ⟨tag,none,#[],.ReservedFrz false,.Read,false,none⟩
def location : LocationTree := ⟨⟨#[some unique,some reserved]⟩,exposedLocation.exposedCache⟩
def tree (rootTag newTag : BorTag) : BorrowTree :=
  ⟨⟨#[(rootTag,first),(newTag,second)],#[]⟩,
    ⟨#[some (rootNode rootTag true),some (parentNode newTag)]⟩,homogeneous 1 location,#[first,second]⟩

set_option autoImplicit false in
/-- Actual wildcard construction with the policy reservation inside and outside.
The first exposed leaf remains unchanged; activation is a later local Write. -/
theorem wildcard_child (rootTag newTag : BorTag) (different : rootTag ≠ newTag) :
    (exposedTree rootTag).newChild Size.ZERO .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes 1) reserved) (.ReservedFrz false) false = ⟨tree rootTag newTag,.ok ()⟩ := by
  have fresh : GeneralBorrowTagMap.Fresh (exposedTree rootTag).tagMapping newTag := by
    intro row member
    change row ∈ #[(rootTag,first)] at member
    have same := Array.mem_singleton.mp member
    subst row
    exact different
  have inserted : (exposedTree rootTag).tagMapping.insert newTag = .Inserted (tree rootTag newTag).tagMapping second :=
    GeneralBorrowTagMap.insert_append (exposedTree rootTag).tagMapping newTag fresh rfl (by change (1 : Nat) ≤ 4294967295;omega)
  let modify := fun (_ : ByteRange) (current : LocationTree) => {current with perms := current.perms.insert second reserved}
  have well : (exposedTree rootTag).locations.WellFormed := by simp [exposedTree,homogeneous,DedupRangeMap.WellFormed]
  have bounds : (0 : Nat)+1 ≤ (exposedTree rootTag).locations.size.bytes.toNat := by change (0 : Nat)+1 ≤ 1;omega
  have modifyOK := GeneralBorrowFreshRange.modify_success (exposedTree rootTag).locations Size.ZERO (Size.ofBytes 1) modify well bounds
  have modified : ((exposedTree rootTag).locations.modifyRange Size.ZERO (Size.ofBytes 1) modify).state = homogeneous 1 location := by
    have exactState := GeneralBorrowFreshModify.state_exact (homogeneous (1 : UInt64) exposedLocation)
      Size.ZERO (Size.ofBytes 1) modify well bounds
    rw [iter_mut_homogeneous_full (1 : UInt64) exposedLocation (by decide)] at exactState
    simpa [GeneralBorrowFreshModify.atPosition,modify,homogeneous,exposedTree,location,exposedLocation,reserved,
      second,UniValMap.insert,UniValMap.extendTo,UniIndex.toNat] using exactState
  have zeroAdd : ({bytes := 0} : Size).add Size.ZERO = .ok Size.ZERO := by decide +kernel
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
    Bool.not_true,Id.run,bind,pure]
  simp only [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes,reserved,show ((1 : UInt64)==0)=false from rfl,beq_self_eq_true,Bool.false_eq_true,↓reduceIte,
    ←Array.forIn_toList,List.forIn_cons,List.forIn_nil,Id.run,bind,pure,
    Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,Bool.not_true,bne_self_eq_false,↓reduceIte]
  try simp only [UInt64.sub_zero,zeroAdd,Id.run,bind,pure]
  dsimp only [modify,reserved,Size.ofBytes] at modifyOK modified
  erw [modifyOK,modified]
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
  rcases node_cases rootTag newTag query node present with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp [tree]

def normal : NormalTreeState := {
  topology := ⟨#[⟨none,[]⟩,⟨none,[]⟩]⟩
  defaultStates := #[⟨.Disabled,false,.None⟩,⟨.ReservedFrz false,false,.Read⟩]
  protectedNodes := []
  locationStates := #[some unique,some reserved]
}

set_option autoImplicit false in
theorem projection (rootTag newTag : BorTag) : source_normal_projection (tree rootTag newTag) location {} = normal := by
  unfold_general_projection
  unfold_general_topology
  with_unfolding_all rfl

def normal_forest : GeneralBorrowForest.Forest normal.topology where
  rank := fun _ => 0
  parents := by
    intro index valid parent edge
    have cases : index=0 ∨ index=1 := by change index<2 at valid;omega
    rcases cases with rfl | rfl <;> cases edge
  childrenDistinct := by
    intro index valid
    have cases : index=0 ∨ index=1 := by change index<2 at valid;omega
    rcases cases with rfl | rfl <;> exact List.nodup_nil
  childParent := by
    intro index valid child member
    have cases : index=0 ∨ index=1 := by change index<2 at valid;omega
    rcases cases with rfl | rfl <;> cases member
  parentChild := by
    intro index valid parent edge
    have cases : index=0 ∨ index=1 := by change index<2 at valid;omega
    rcases cases with rfl | rfl <;> cases edge

set_option autoImplicit false in
def forest (rootTag newTag : BorTag) : GeneralBorrowForest.Forest (source_normal_projection (tree rootTag newTag) location {}).topology := by
  rw [projection]
  exact normal_forest

set_option autoImplicit false in
theorem normal_owned (rootTag newTag : BorTag) (kind : AccessKind) :
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection (tree rootTag newTag) location {}) second.toNat kind := by
  rw [projection]
  refine ⟨by decide,rfl,rfl,?_⟩
  intro index valid
  have cases : index=0 ∨ index=1 := by change index<2 at valid;omega
  rcases cases with rfl | rfl
  · refine ⟨unique,rfl,?_⟩
    cases kind <;> cases GeneralBorrowAnchor.relation normal second.toNat _ <;>
      simp [GeneralBorrowPermissions.AccessOwned, GeneralBorrowPermissions.Owned,
        GeneralBorrowPermissions.LocalOwned, GeneralBorrowPermissions.ForeignOwned,
        GeneralBorrowPermissions.LocalReadable,normal,unique,reserved,LocationState.possible,Permission.isUnique]
  · refine ⟨reserved,rfl,?_⟩
    cases kind <;> cases GeneralBorrowAnchor.relation normal second.toNat _ <;>
      simp [GeneralBorrowPermissions.AccessOwned, GeneralBorrowPermissions.Owned,
        GeneralBorrowPermissions.LocalOwned, GeneralBorrowPermissions.ForeignOwned,
        GeneralBorrowPermissions.LocalReadable,normal,unique,reserved,LocationState.possible,Permission.isUnique]



set_option autoImplicit false in
theorem read_visited (rootTag newTag : BorTag) :
    ((source_normal_projection (tree rootTag newTag) location {}).performAccess
      second.toNat .Read .VisitChildrenOfAccessed).visited = [⟨1,.LocalAccess⟩] := by
  rw [projection]
  with_unfolding_all rfl

set_option autoImplicit false in
theorem read_unexposed (rootTag newTag : BorTag) :
    ∀ event ∈ ((source_normal_projection (tree rootTag newTag) location {}).performAccess
      second.toNat .Read .VisitChildrenOfAccessed).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → (tree rootTag newTag).nodeAt index = some node →
      node.isExposed = false := by
  rw [read_visited]
  intro event member index node converted present
  have same : event = ⟨1,.LocalAccess⟩ := List.mem_singleton.mp member
  subst event
  have idx : index = second := (Option.some.inj converted).symm
  subst index
  have nd : parentNode newTag = node := Option.some.inj present
  rw [←nd]
  rfl


set_option autoImplicit false in
/-- The actual normal local Write activates the policy reservation. -/
theorem normal_write (rootTag newTag : BorTag) :
    ((tree rootTag newTag).performNormalAccessAt location second .Write {} .VisitChildrenOfAccessed).access.status = .Completed ∧
    ((tree rootTag newTag).performNormalAccessAt location second .Write {} .VisitChildrenOfAccessed).location =
      GeneralBorrowTwoRootConstructed.location := by
  simp only [BorrowTree.performNormalAccessAt,projection]
  constructor <;> with_unfolding_all rfl

set_option autoImplicit false in
theorem write_visited (rootTag newTag : BorTag) :
    ((source_normal_projection (tree rootTag newTag) location {}).performAccess
      second.toNat .Write .VisitChildrenOfAccessed).visited = [⟨1,.LocalAccess⟩] := by
  rw [projection]
  with_unfolding_all rfl

set_option autoImplicit false in
theorem write_unexposed (rootTag newTag : BorTag) :
    ∀ event ∈ ((source_normal_projection (tree rootTag newTag) location {}).performAccess
      second.toNat .Write .VisitChildrenOfAccessed).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → (tree rootTag newTag).nodeAt index = some node →
      node.isExposed = false := by
  rw [write_visited]
  intro event member index node converted present
  have same : event = ⟨1,.LocalAccess⟩ := List.mem_singleton.mp member
  subst event
  have idx : index = second := (Option.some.inj converted).symm
  subst index
  have nd : parentNode newTag = node := Option.some.inj present
  rw [←nd]
  rfl



set_option autoImplicit false in
theorem foreign_data (rootTag newTag : BorTag) (ordered : rootTag.value ≤ newTag.value) :
    GeneralBorrowWildcardLeaf.Data (tree rootTag newTag) location first (rootNode rootTag true) newTag :=
  ⟨rfl,rfl,rfl,rfl,rfl,ordered⟩

set_option autoImplicit false in
theorem write_at (rootTag newTag : BorTag) (ordered : rootTag.value ≤ newTag.value) :
    source_access_location (source_tree_access_at (tree rootTag newTag) location (some second)
      .Write {} .VisitChildrenOfAccessed ⟨0,1⟩) = GeneralBorrowTwoRootConstructed.location ∧
    source_access_status (source_tree_access_at (tree rootTag newTag) location (some second)
      .Write {} .VisitChildrenOfAccessed ⟨0,1⟩) = none := by
  have path : ((source_normal_projection (tree rootTag newTag) location {}).topology.ancestorPath second.toNat).getLast! = second.toNat := by
    rw [projection]
    with_unfolding_all rfl
  have access := GeneralBorrowTwoRootNormalAccess.access (tree rootTag newTag) location {} second second first
    (parentNode newTag) (parentNode newTag) (rootNode rootTag true) .Write ⟨0,1⟩
    (forest rootTag newTag) (normal_owned rootTag newTag .Write) (depth rootTag newTag)
    (children rootTag newTag) rfl rfl rfl (by decide +kernel) path
    (foreign_data rootTag newTag ordered) (write_unexposed rootTag newTag)
  exact ⟨access.1.trans (normal_write rootTag newTag).2,access.2⟩


def activated (rootTag newTag : BorTag) : BorrowTree :=
  {tree rootTag newTag with locations := homogeneous 1 GeneralBorrowTwoRootConstructed.location}

set_option autoImplicit false in
/-- Actual ranged Write through the new concrete tag, including the exposed
foreign-root loop. This is not the preceding reborrow access of a full retag. -/
theorem write_exact (rootTag newTag : BorTag) (ordered : rootTag.value < newTag.value) :
    ((tree rootTag newTag).performBorrowAccessRange (.concrete newTag) (Size.ofBytes 0) (Size.ofBytes 1)
      .Write {} .VisitChildrenOfAccessed).status = .Completed ∧
    ((tree rootTag newTag).performBorrowAccessRange (.concrete newTag) (Size.ofBytes 0) (Size.ofBytes 1)
      .Write {} .VisitChildrenOfAccessed).tree = activated rootTag newTag := by
  have different : rootTag ≠ newTag := by
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    have h := UInt64.lt_iff_toNat_lt.mp ordered
    omega
  have lower : rootTag.value ≤ newTag.value := UInt64.le_iff_toNat_le.mpr (by have h:=UInt64.lt_iff_toNat_lt.mp ordered;omega)
  have fresh : GeneralBorrowTagMap.Fresh (exposedTree rootTag).tagMapping newTag := by
    intro row member
    change row ∈ #[(rootTag,first)] at member
    have same := Array.mem_singleton.mp member
    subst row
    exact different
  have tagged : (tree rootTag newTag).indexOfTag newTag = some second :=
    GeneralBorrowTagMap.pushed_get_new (exposedTree rootTag).tagMapping newTag fresh second #[]
  have access := write_at rootTag newTag lower
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,
    show (tree rootTag newTag).locations = homogeneous 1 location from rfl]
  have zero : Size.ofBytes 0 = Size.ZERO := rfl
  rw [zero,iter_mut_homogeneous_full (1 : UInt64) location (by decide)]
  simp only [Array.size_singleton,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
  rw [setAtPos_exact (homogeneous (1 : UInt64) location) 0 (by change 0<1;decide)]
  simp only [access.1,access.2]
  constructor
  · trivial
  · rfl

set_option autoImplicit false in
theorem activated_foreign_data (rootTag newTag : BorTag) (ordered : rootTag.value ≤ newTag.value) :
    GeneralBorrowWildcardLeaf.Data (activated rootTag newTag) GeneralBorrowTwoRootConstructed.location
      first (rootNode rootTag true) newTag :=
  ⟨rfl,rfl,rfl,rfl,rfl,ordered⟩


set_option autoImplicit false in
/-- The newChild fields are taken from the actual mutable/default policy and
its actual frozen-byte state selector. The surrounding retag caller is not
part of this lower-level construction theorem. -/
theorem policy_child (rootTag newTag : BorTag) (different : rootTag ≠ newTag) :
    ∃ selected state,
      RetagPolicy.create ⟨true,true,true⟩ .Mutable .Default ⟨false,false⟩ = some selected ∧
      RetagPolicy.initialLocationState selected true = .ok state ∧
      (exposedTree rootTag).newChild Size.ZERO .wildcard newTag
        (DedupRangeMap.new (Size.ofBytes 1) state) selected.outsidePermission selected.protector.isSome =
        ⟨tree rootTag newTag,.ok ()⟩ := by
  exact ⟨policy,reserved,create_policy,initial_state,wildcard_child rootTag newTag different⟩

set_option autoImplicit false in
/-- Exact stored permissions and exposed-leaf cache after the activating Write.
Both nodes retain the parentless/unexposed shape created by newChild. -/
theorem activated_shape (rootTag newTag : BorTag) :
    (activated rootTag newTag).roots = #[first,second] ∧
    (activated rootTag newTag).nodeAt first = some (rootNode rootTag true) ∧
    (activated rootTag newTag).nodeAt second = some (parentNode newTag) ∧
    (parentNode newTag).parent = none ∧ (parentNode newTag).isExposed = false ∧
    GeneralBorrowTwoRootConstructed.location.perms.get second = some unique ∧
    GeneralBorrowTwoRootConstructed.location.perms.get first = some unique ∧
    GeneralBorrowTwoRootConstructed.location.exposedCache.nodes.get first = some ⟨1,1⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def activatedNormal : NormalTreeState := {normal with locationStates := #[some unique,some unique]}

set_option autoImplicit false in
theorem activated_projection (rootTag newTag : BorTag) :
    source_normal_projection (activated rootTag newTag) GeneralBorrowTwoRootConstructed.location {} = activatedNormal := by
  unfold_general_projection
  unfold_general_topology
  with_unfolding_all rfl

set_option autoImplicit false in
def activated_forest (rootTag newTag : BorTag) :
    GeneralBorrowForest.Forest (source_normal_projection (activated rootTag newTag) GeneralBorrowTwoRootConstructed.location {}).topology := by
  rw [activated_projection]
  exact normal_forest

set_option autoImplicit false in
theorem activated_owned (rootTag newTag : BorTag) (kind : AccessKind) :
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection (activated rootTag newTag)
      GeneralBorrowTwoRootConstructed.location {}) second.toNat kind := by
  rw [activated_projection]
  refine ⟨by decide,rfl,rfl,?_⟩
  intro index valid
  have cases : index=0 ∨ index=1 := by change index<2 at valid;omega
  rcases cases with rfl | rfl <;> refine ⟨unique,rfl,?_⟩
  all_goals cases kind <;> cases GeneralBorrowAnchor.relation activatedNormal second.toNat _ <;>
    simp [GeneralBorrowPermissions.AccessOwned, GeneralBorrowPermissions.Owned,
      GeneralBorrowPermissions.LocalOwned, GeneralBorrowPermissions.ForeignOwned,
      GeneralBorrowPermissions.LocalReadable,activatedNormal,normal,unique,LocationState.possible,Permission.isUnique]

set_option autoImplicit false in
theorem activated_read_unexposed (rootTag newTag : BorTag) :
    ∀ event ∈ ((source_normal_projection (activated rootTag newTag) GeneralBorrowTwoRootConstructed.location {}).performAccess
      second.toNat .Read .VisitChildrenOfAccessed).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → (activated rootTag newTag).nodeAt index = some node →
      node.isExposed = false := by
  have visited : ((source_normal_projection (activated rootTag newTag) GeneralBorrowTwoRootConstructed.location {}).performAccess
      second.toNat .Read .VisitChildrenOfAccessed).visited = [⟨1,.LocalAccess⟩] := by
    rw [activated_projection]
    with_unfolding_all rfl
  rw [visited]
  intro event member index node converted present
  have same : event = ⟨1,.LocalAccess⟩ := List.mem_singleton.mp member
  subst event
  have idx : index = second := (Option.some.inj converted).symm
  subst index
  have nd : parentNode newTag = node := Option.some.inj present
  rw [←nd]
  rfl


set_option autoImplicit false in
/-- A source-policy seed from BorrowTree.new through exposure, wildcard
construction, and concrete-tag activation. This does not prove a full retag
caller, global-memory trace, or Rust-history reachability. -/
theorem construct (rootTag newTag : BorTag) (ordered : rootTag.value < newTag.value) :
    RetagPolicy.create ⟨true,true,true⟩ .Mutable .Default ⟨false,false⟩ = some policy ∧
    RetagPolicy.initialLocationState policy true = .ok reserved ∧
    let exposed := (BorrowTree.new rootTag (Size.ofBytes 1)).exposeTag {} rootTag
    let built := exposed.tree.newChild Size.ZERO .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes 1) reserved) policy.outsidePermission policy.protector.isSome
    exposed.outcome = .ok () ∧ built.outcome = .ok () ∧
    (built.tree.performBorrowAccessRange (.concrete newTag) (Size.ofBytes 0) (Size.ofBytes 1)
      .Write {} .VisitChildrenOfAccessed).status = .Completed ∧
    (built.tree.performBorrowAccessRange (.concrete newTag) (Size.ofBytes 0) (Size.ofBytes 1)
      .Write {} .VisitChildrenOfAccessed).tree = activated rootTag newTag ∧
    GeneralBorrowWildcardLeaf.Data (activated rootTag newTag) GeneralBorrowTwoRootConstructed.location
      first (rootNode rootTag true) newTag := by
  have different : rootTag ≠ newTag := by
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    have h := UInt64.lt_iff_toNat_lt.mp ordered
    omega
  have lower : rootTag.value ≤ newTag.value := UInt64.le_iff_toNat_le.mpr (by have h:=UInt64.lt_iff_toNat_lt.mp ordered;omega)
  refine ⟨create_policy,initial_state,?_⟩
  dsimp only
  rw [GeneralBorrowTwoRootConstructed.expose_root rootTag {}]
  rw [show (exposedTree rootTag).newChild Size.ZERO .wildcard newTag
    (DedupRangeMap.new (Size.ofBytes 1) reserved) policy.outsidePermission policy.protector.isSome =
      ⟨tree rootTag newTag,.ok ()⟩ from wildcard_child rootTag newTag different]
  exact ⟨rfl,rfl,(write_exact rootTag newTag ordered).1,(write_exact rootTag newTag ordered).2,
    activated_foreign_data rootTag newTag lower⟩

end DuplicatePrefix.GeneralBorrowTwoRootPolicySeed
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoRootPolicySeed.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved policy seed dependency {name}: {dependency}"
