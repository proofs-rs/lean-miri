import duplicate_prefix.GeneralBorrowExposedPartitionState
import duplicate_prefix.GeneralBorrowReusableGeneration

namespace DuplicatePrefix.GeneralBorrowRootExposureSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

abbrev root : UniIndex := GeneralBorrowFullSharedSeed.root
def unique : LocationState := ⟨.Unique,true,.None⟩
def initialLocation : LocationTree := ⟨⟨#[some unique]⟩,{}⟩
def exposedLocation : LocationTree := ⟨⟨#[some unique]⟩,⟨⟨#[some ⟨1,1⟩]⟩⟩⟩
def rootNode (tag : BorTag) (exposed : Bool) : TreeNode := ⟨tag,none,#[],.Disabled,.None,exposed,none⟩
def exposedTree (capacity : UInt64) (tag : BorTag) : BorrowTree :=
  ⟨⟨#[(tag,root)],#[]⟩,⟨#[some (rootNode tag true)]⟩,homogeneous capacity exposedLocation,#[root]⟩

private theorem root_cache (nodes : UniValMap TreeNode) (node : TreeNode)
    (present : nodes.get root = some node) (parentless : node.parent = none) :
    ({} : ExposedCache).updateExposure nodes root .None .Write = ⟨exposedLocation.exposedCache,.ok ()⟩ := by
  unfold ExposedCache.updateExposure
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have first : scan () ({},some root,0,.ok (),true) =
      .yield (exposedLocation.exposedCache,none,1,.ok (),false) := by
    simp only [scan,show ¬0>nodes.size from by omega,↓reduceIte,present,parentless,Option.isNone_none]
    rfl
  have last : scan () (exposedLocation.exposedCache,none,1,.ok (),false) =
      .done (exposedLocation.exposedCache,none,1,.ok (),false) := by
    simp only [scan,Bool.false_eq_true,↓reduceIte]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [first,bind]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [last,bind,pure]
  rfl

/-- Real allocation followed by real root exposure forms the exact one-read/
one-write cache, at arbitrary positive capacity. No cache/Ready witness or
successful-operation assumption is supplied. -/
theorem expose (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag) (protections : ProtectedTags) :
    (BorrowTree.new tag (Size.ofBytes capacity)).exposeTag protections tag = ⟨exposedTree capacity tag,.ok ()⟩ := by
  have original : BorrowTree.new tag (Size.ofBytes capacity) =
      ⟨⟨#[(tag,root)],#[]⟩,⟨#[some (rootNode tag false)]⟩,homogeneous capacity initialLocation,#[root]⟩ :=
    GeneralBorrowFullSharedSeed.tree_eq capacity nonzero tag
  have tagged : (BorrowTree.new tag (Size.ofBytes capacity)).indexOfTag tag = some root := by
    rw [original];simp [BorrowTree.indexOfTag,UniKeyMap.get]
  have present : (BorrowTree.new tag (Size.ofBytes capacity)).nodeAt root = some (rootNode tag false) := by
    rw [original];rfl
  let marked := {(BorrowTree.new tag (Size.ofBytes capacity)) with nodes :=
    ((BorrowTree.new tag (Size.ofBytes capacity)).nodes.insert root (rootNode tag true))}
  have markedPresent : marked.nodes.get root = some (rootNode tag true) := by
    dsimp only [marked]
    exact GeneralBorrowFreshLocation.get_same (BorrowTree.new tag (Size.ofBytes capacity)).nodes root (rootNode tag true)
  have update := root_cache marked.nodes (rootNode tag true) markedPresent rfl
  have locations : (BorrowTree.new tag (Size.ofBytes capacity)).locations = homogeneous capacity initialLocation := by rw [original]
  unfold BorrowTree.exposeTag
  simp only [tagged,present,rootNode,Bool.false_eq_true,↓reduceIte]
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,locations,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  simp only [show (homogeneous capacity initialLocation).entries.size = 1 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn'_cons,List.forIn'_nil,bind,pure]
  simp only [index_exact (homogeneous capacity initialLocation) 0 (by change 0<1;decide)]
  simp only [homogeneous,Array.getElem_singleton] at *
  simp only [initialLocation,unique,root,GeneralBorrowFullSharedSeed.root,UniValMap.get,Array.getElem?_singleton,
    Permission.strongestAllowedLocalAccess]
  dsimp only [marked] at update
  erw [update]
  simp only [Except.mapError]
  erw [setAtPos_exact (homogeneous capacity initialLocation) 0 (by change 0<1;decide)]
  rw [original]
  with_unfolding_all rfl

/-- The cache witness is a conclusion of the actual exposure seed, not an
arbitrary handcrafted initial cache. -/
theorem cache_root : exposedLocation.exposedCache.nodes.get root = some (⟨1,1⟩ : ExposedCacheNode) := rfl

theorem cache_other (query : UniIndex) (different : query ≠ root) :
    exposedLocation.exposedCache.nodes.get query = none := by
  have nonzero : query.toNat ≠ 0 := fun equal => different (GeneralBorrowNodeUpdate.index_injective query root equal)
  simp [exposedLocation,UniValMap.get,nonzero]

/-- Actual finite counters after this root exposure need no history budget:
every cache entry is bounded by one. -/
theorem bounded (query : UniIndex) :
    ((exposedLocation.exposedCache.nodes.get query).getD {}).localReads.toNat ≤ 1 ∧
    ((exposedLocation.exposedCache.nodes.get query).getD {}).localWrites.toNat ≤ 1 := by
  by_cases same : query = root
  · subst query;rw [cache_root];decide
  · rw [cache_other query same];decide

/-- The actual newly exposed root supplies both Read and Write local cache
classification; with a virtual wildcard root the source computes EitherAccess. -/
theorem classified (kind : AccessKind) :
    exposedLocation.exposedCache.accessRelatedness root root kind false false = some .LocalAccess ∧
    exposedLocation.exposedCache.accessRelatedness root root kind true false = some .EitherAccess := by
  cases kind <;> decide

/-- Re-exposure executes the real source early return and does not increment
this cache again. -/
theorem again (capacity : UInt64) (tag : BorTag) (protections : ProtectedTags) :
    (exposedTree capacity tag).exposeTag protections tag = ⟨exposedTree capacity tag,.ok ()⟩ := by
  apply GeneralBorrowRootExposureFrame.already _ tag root (rootNode tag true)
  · simp [exposedTree,BorrowTree.indexOfTag,UniKeyMap.get]
  · rfl
  · rfl

/-- The actual exposed allocation seed supplies the recurring partition state
internally. The distinct spare tag is ordinary later-call allocation resource,
not a cache, ownership or operation-success premise. -/
theorem reachable_state (capacity : UInt64) (nonzero : capacity ≠ 0) (tag spare : BorTag)
    (different : tag ≠ spare) :
    Nonempty {post : GeneralBorrowPartitionState.State (exposedTree capacity tag) root capacity //
      post.node.tag = tag ∧ post.node.isExposed = true} := by
  let initial := GeneralBorrowReusableGeneration.seed capacity nonzero tag spare different
  let ready := GeneralBorrowPartitionState.of_reusable _ root capacity initial
  have rootTag : ready.node.tag = tag := rfl
  have completed := GeneralBorrowExposedPartitionState.expose_root _ root capacity ready
  rw [rootTag,expose capacity nonzero tag {}] at completed
  obtain ⟨⟨post,postTag⟩⟩ := completed.2.1
  have present : (exposedTree capacity tag).nodeAt root = some (rootNode tag true) := rfl
  have nodeEq : post.node = rootNode tag true := Option.some.inj (post.star.present.symm.trans present)
  exact ⟨⟨post,postTag,by rw [nodeEq];rfl⟩⟩

/-- Repeat the real source exposure, preserving and returning any first error.
This helper never replaces an error by a successful no-op. -/
def repeated (tag : BorTag) (protections : ProtectedTags) : Nat → BorrowTree → BorrowTree.TreeMutationResult
  | 0,tree => ⟨tree,.ok ()⟩
  | n+1,tree =>
      let step := tree.exposeTag protections tag
      match step.outcome with
      | .error _ => step
      | .ok () => repeated tag protections n step.tree

/-- Any finite repeated exposure of the same real exposed root is idempotent. -/
theorem repeated_after (capacity : UInt64) (tag : BorTag) (protections : ProtectedTags) (count : Nat) :
    repeated tag protections count (exposedTree capacity tag) = ⟨exposedTree capacity tag,.ok ()⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [repeated,again] using ih

/-- Allocation followed by any positive finite number of actual root exposures
has this exact cache and completes. There is no history-length65536 restriction:
only the first exposure increments; subsequent operations take source early return. -/
theorem generated (capacity : UInt64) (nonzero : capacity ≠ 0) (tag : BorTag)
    (protections : ProtectedTags) (count : Nat) :
    repeated tag protections (count+1) (BorrowTree.new tag (Size.ofBytes capacity)) =
      ⟨exposedTree capacity tag,.ok ()⟩ := by
  simp only [repeated,expose capacity nonzero tag protections,repeated_after]

end DuplicatePrefix.GeneralBorrowRootExposureSeed
