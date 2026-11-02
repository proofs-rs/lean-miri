import duplicate_prefix.GeneralBorrowExposeRead
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
import duplicate_prefix.GeneralBorrowTagMap
import duplicate_prefix.GeneralBorrowFreshRange

namespace DuplicatePrefix.GeneralBorrowTwoRootConstructed
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowExposureRelease GeneralRangeMapState RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def first : UniIndex := ⟨0⟩
def second : UniIndex := ⟨1⟩
def unique : LocationState := ⟨.Unique,true,.None⟩
def initialLocation : LocationTree := ⟨⟨#[some unique]⟩,{}⟩
def exposedLocation : LocationTree := ⟨⟨#[some unique]⟩,⟨⟨#[some ⟨1,1⟩]⟩⟩⟩
def location : LocationTree := ⟨⟨#[some unique,some unique]⟩,exposedLocation.exposedCache⟩
def rootNode (tag : BorTag) (exposed : Bool) : TreeNode := ⟨tag,none,#[],.Disabled,.None,exposed,none⟩
def parentNode (tag : BorTag) : TreeNode := ⟨tag,none,#[],.Frozen,.Read,false,none⟩
def exposedTree (tag : BorTag) : BorrowTree :=
  ⟨⟨#[(tag,first)],#[]⟩,⟨#[some (rootNode tag true)]⟩,homogeneous 1 exposedLocation,#[first]⟩
def tree (rootTag newTag : BorTag) : BorrowTree :=
  ⟨⟨#[(rootTag,first),(newTag,second)],#[]⟩,
    ⟨#[some (rootNode rootTag true),some (parentNode newTag)]⟩,homogeneous 1 location,#[first,second]⟩

set_option autoImplicit false in
private theorem root_exposure (nodes : UniValMap TreeNode) (node : TreeNode)
    (present : nodes.get first = some node) (parentless : node.parent = none) :
    ({} : ExposedCache).updateExposure nodes first .None .Write = ⟨exposedLocation.exposedCache,.ok ()⟩ := by
  unfold ExposedCache.updateExposure
  simp only [reduceCtorEq,↓reduceIte,Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have initial : scan () ({},some first,0,.ok (),true) =
      .yield (exposedLocation.exposedCache,none,1,.ok (),false) := by
    simp only [scan,show ¬0>nodes.size from by omega,↓reduceIte,present,parentless,Option.isNone_none]
    rfl
  have done : scan () (exposedLocation.exposedCache,none,1,.ok (),false) =
      .done (exposedLocation.exposedCache,none,1,.ok (),false) := by simp only [scan,Bool.false_eq_true,↓reduceIte,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [initial,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [done,bind,pure]
  rfl

set_option autoImplicit false in
/-- The allocation root is exposed by the real source operation, producing the
exact one-read/one-write cache witness. No earlier retag or Rust-history claim. -/
theorem expose_root (tag : BorTag) (protections : ProtectedTags) :
    (BorrowTree.new tag (Size.ofBytes 1)).exposeTag protections tag = ⟨exposedTree tag,.ok ()⟩ := by
  have tagged : (BorrowTree.new tag (Size.ofBytes 1)).indexOfTag tag = some first := by
    simp [BorrowTree.indexOfTag,BorrowTree.new,UniKeyMap.get,first]
    rfl
  have present : (BorrowTree.new tag (Size.ofBytes 1)).nodeAt first = some (rootNode tag false) :=
    BorrowTree.new_root_node tag (Size.ofBytes 1)
  let marked := {(BorrowTree.new tag (Size.ofBytes 1)) with nodes :=
    ((BorrowTree.new tag (Size.ofBytes 1)).nodes.insert first (rootNode tag true))}
  have markedPresent : marked.nodes.get first = some (rootNode tag true) := by
    dsimp only [marked]
    exact GeneralBorrowFreshLocation.get_same (BorrowTree.new tag (Size.ofBytes 1)).nodes first (rootNode tag true)
  have update := root_exposure marked.nodes (rootNode tag true) markedPresent rfl
  have locations : (BorrowTree.new tag (Size.ofBytes 1)).locations = homogeneous 1 initialLocation := rfl
  unfold BorrowTree.exposeTag
  simp only [tagged,present,rootNode,Bool.false_eq_true,↓reduceIte]
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,locations,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  simp only [show (homogeneous (1 : UInt64) initialLocation).entries.size = 1 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn'_cons,List.forIn'_nil,bind,pure]
  simp only [index_exact (homogeneous (1 : UInt64) initialLocation) 0 (by change 0<1;decide)]
  simp only [homogeneous,Array.getElem_singleton] at *
  simp only [initialLocation,unique,first,UniValMap.get,Array.getElem?_singleton,Option.getD_some,
    Permission.strongestAllowedLocalAccess]
  dsimp only [marked] at update
  erw [update]
  simp only [Except.mapError,Except.map,bind,pure]
  erw [setAtPos_exact (homogeneous (1 : UInt64) initialLocation) 0 (by change 0<1;decide)]
  with_unfolding_all rfl

set_option autoImplicit false in
/-- Actual wildcard parent construction after exposure. Frozen is a permitted
outside default; Disabled is rejected by the pinned constructor before node
creation. The whole one-byte range stores Unique regardless of this default. -/
theorem wildcard_child (rootTag newTag : BorTag) (different : rootTag ≠ newTag) :
    (exposedTree rootTag).newChild Size.ZERO .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes 1) unique) .Frozen false = ⟨tree rootTag newTag,.ok ()⟩ := by
  have fresh : GeneralBorrowTagMap.Fresh (exposedTree rootTag).tagMapping newTag := by
    intro row member
    change row ∈ #[(rootTag,first)] at member
    have same := Array.mem_singleton.mp member
    subst row
    exact different
  have inserted : (exposedTree rootTag).tagMapping.insert newTag = .Inserted (tree rootTag newTag).tagMapping second :=
    GeneralBorrowTagMap.insert_append (exposedTree rootTag).tagMapping newTag fresh rfl (by change (1 : Nat) ≤ 4294967295;omega)
  let modify := fun (_ : ByteRange) (current : LocationTree) => {current with perms := current.perms.insert second unique}
  have well : (exposedTree rootTag).locations.WellFormed := by simp [exposedTree,homogeneous,DedupRangeMap.WellFormed]
  have bounds : (0 : Nat)+1 ≤ (exposedTree rootTag).locations.size.bytes.toNat := by change (0 : Nat)+1 ≤ 1;omega
  have modifyOK := GeneralBorrowFreshRange.modify_success (exposedTree rootTag).locations Size.ZERO (Size.ofBytes 1) modify well bounds
  have modified : ((exposedTree rootTag).locations.modifyRange Size.ZERO (Size.ofBytes 1) modify).state = homogeneous 1 location := by
    have exactState := GeneralBorrowFreshModify.state_exact (homogeneous (1 : UInt64) exposedLocation)
      Size.ZERO (Size.ofBytes 1) modify well bounds
    rw [iter_mut_homogeneous_full (1 : UInt64) exposedLocation (by decide)] at exactState
    simpa [GeneralBorrowFreshModify.atPosition,modify,homogeneous,exposedTree,location,exposedLocation,unique,
      second,UniValMap.insert,UniValMap.extendTo,UniIndex.toNat] using exactState
  have zeroAdd : ({bytes := 0} : Size).add Size.ZERO = .ok Size.ZERO := by decide +kernel
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
    Bool.not_true,Id.run,bind,pure]
  simp only [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes,unique,show ((1 : UInt64)==0)=false from rfl,beq_self_eq_true,Bool.false_eq_true,↓reduceIte,
    ←Array.forIn_toList,List.forIn_cons,List.forIn_nil,Id.run,bind,pure,
    Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,Bool.not_true,bne_self_eq_false,↓reduceIte]
  try simp only [UInt64.sub_zero,zeroAdd,Id.run,bind,pure]
  dsimp only [modify,unique,Size.ofBytes] at modifyOK modified
  erw [modifyOK,modified]
  with_unfolding_all rfl


set_option autoImplicit false in
/-- The exposed first root remains a leaf with an exact mutable exposure cache
and checked tag upper bound after the real wildcard construction. -/
theorem foreign_data (rootTag newTag : BorTag) (ordered : rootTag.value ≤ newTag.value) :
    GeneralBorrowWildcardLeaf.Data (tree rootTag newTag) location first (rootNode rootTag true) newTag :=
  ⟨rfl,rfl,rfl,rfl,rfl,ordered⟩

set_option autoImplicit false in
/-- Both exact operation results originate at BorrowTree.new, rather than an
assumed final graph. This is a raw-operation seed, not a preceding-retag or
Rust-history reachability theorem. -/
theorem construct (rootTag newTag : BorTag) (ordered : rootTag.value < newTag.value) :
    let exposed := (BorrowTree.new rootTag (Size.ofBytes 1)).exposeTag {} rootTag
    exposed.outcome = .ok () ∧
      exposed.tree.newChild Size.ZERO .wildcard newTag (DedupRangeMap.new (Size.ofBytes 1) unique) .Frozen false =
        ⟨tree rootTag newTag,.ok ()⟩ ∧
      GeneralBorrowWildcardLeaf.Data (tree rootTag newTag) location first (rootNode rootTag true) newTag ∧
      (tree rootTag newTag).roots = #[first,second] ∧
      (tree rootTag newTag).nodeAt second = some (parentNode newTag) ∧
      (parentNode newTag).parent = none ∧ (parentNode newTag).isExposed = false ∧
      location.perms.get second = some unique := by
  have different : rootTag ≠ newTag := by
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    have lower := UInt64.lt_iff_toNat_lt.mp ordered
    omega
  have lower : rootTag.value ≤ newTag.value := UInt64.le_iff_toNat_le.mpr (by have h:=UInt64.lt_iff_toNat_lt.mp ordered;omega)
  dsimp only
  rw [expose_root rootTag {}]
  exact ⟨rfl,wildcard_child rootTag newTag different,foreign_data rootTag newTag lower,rfl,rfl,rfl,rfl,rfl⟩

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
  defaultStates := #[⟨.Disabled,false,.None⟩,⟨.Frozen,false,.Read⟩]
  protectedNodes := []
  locationStates := #[some unique,some unique]
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
        GeneralBorrowPermissions.LocalReadable,normal,unique,LocationState.possible,Permission.isUnique]
  · refine ⟨unique,rfl,?_⟩
    cases kind <;> cases GeneralBorrowAnchor.relation normal second.toNat _ <;>
      simp [GeneralBorrowPermissions.AccessOwned, GeneralBorrowPermissions.Owned,
        GeneralBorrowPermissions.LocalOwned, GeneralBorrowPermissions.ForeignOwned,
        GeneralBorrowPermissions.LocalReadable,normal,unique,LocationState.possible,Permission.isUnique]



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

end DuplicatePrefix.GeneralBorrowTwoRootConstructed

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoRootConstructed.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved constructed two-root dependency {name}: {dependency}"
