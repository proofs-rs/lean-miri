import Miri.Interpreter.AllocationMachine
import Miri.Interpreter.PointerMachine
import Miri.Interpreter.ProvenanceGC
import Miri.Interpreter.TypedRetag
import Std.Tactic.Do

/-!
Exact Tree Borrows preconditions over the interpreter's concrete successors.
The error continuations receive the state retained by the interpreter, including
updates that precede the failed check.
-/
namespace Miri.Verification.TreeBorrowsWP

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Std.WP

-- The resumable machine actions used by the concrete interpreter.
attribute [spec] TypedRetag.newPermission TypedRetag.reborrow TypedRetag.retagPlace
attribute [spec] TypedRetag.retagPtrValue TypedRetag.protectPlace
attribute [spec] TypedRetag.protectInPlaceFunctionArgument TypedRetag.machineRetagPtrValue
attribute [spec] MachineHooks.beforeStackPopWithEnsure PointerMachine.exposeProvenance
attribute [spec] AllocationMachine.beforeDeallocation AllocationMachine.deallocate ProvenanceGC.run

/-- Precondition for a single location after a traversal decides to visit it.
A successful transition records local access. A protected transition to
Disabled reports its updated location, including the new accessed bit. -/
def locationPre (state : Tree.LocationState) (kind : AccessKind)
    (relatedness : AccessRelatedness) (held : Bool)
    (post : Tree.LocationState → PermTransition → Prop)
    (failure : Tree.LocationState.AccessResult → Prop) : Prop :=
  state.resultPre kind relatedness held fun
    | .Success next transition => post next transition
    | other => failure other

theorem location_iff (state : Tree.LocationState) (kind : AccessKind)
    (relatedness : AccessRelatedness) (held : Bool)
    (post : Tree.LocationState → PermTransition → Prop)
    (failure : Tree.LocationState.AccessResult → Prop) :
    (match state.performAccess kind relatedness held with
    | .Success next transition => post next transition
    | other => failure other) ↔ locationPre state kind relatedness held post failure :=
  Tree.LocationState.resultPre_iff state kind relatedness held (fun
    | .Success next transition => post next transition
    | other => failure other)

/-- Retain the complete trace and updated tree on either access outcome.
Concrete and wildcard provenance share the same rule. -/
def accessPre (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (failure : BorrowTree.BorrowTreeAccessStatus →
      BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop) : Prop :=
  BorrowTree.RangeVerification.accessContract tree provenance offset length kind tags mode
    (fun result => match result.status with
      | .Completed => post result.tree result.locations
      | status => failure status result.tree result.locations)

/-- The symbolic precondition is equivalent to checking the exact concrete
successor, including the diagnostic trace and any committed error updates. -/
theorem accessPre_iff (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (failure : BorrowTree.BorrowTreeAccessStatus →
      BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop) :
    accessPre tree provenance offset length kind tags mode post failure ↔
      let result := tree.performBorrowAccessRange provenance offset length kind tags mode
      match result.status with
      | .Completed => post result.tree result.locations
      | status => failure status result.tree result.locations :=
  (BorrowTree.RangeVerification.accessContract_iff tree provenance offset length kind tags mode
    (fun result => match result.status with
      | .Completed => post result.tree result.locations
      | status => failure status result.tree result.locations)).symm

/-- As a state effect, the ranged access keeps the concrete tree even when
a later segment errors. Its error carries the diagnostics for both branches. -/
def access (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    EStateM (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult)
      BorrowTree (Array BorrowTree.BorrowTreeLocationResult) := fun tree =>
  let result := tree.performBorrowAccessRange provenance offset length kind tags mode
  match result.status with
  | .Completed => .ok result.locations result.tree
  | status => .error (status, result.locations) result.tree

@[spec] theorem spec_access (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (failure : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop) :
    Triple (access provenance offset length kind tags mode)
      (fun tree => accessPre tree provenance offset length kind tags mode
        (fun after locations => post locations after)
        (fun status after locations => failure (status, locations) after)) post failure := by
  apply Triple.iff.mpr
  intro tree safe
  simp only [wp, WP.wpTrans, access]
  rw [accessPre_iff] at safe
  generalize tree.performBorrowAccessRange provenance offset length kind tags mode = result at *
  rcases result with ⟨after, locations, status⟩
  cases status <;> exact safe

/-- Lift a result that contains the concrete successor tree whether it
succeeds or fails. -/
def mutation {Error A : Type} (run : BorrowTree → BorrowTree × Except Error A) :
    EStateM Error BorrowTree A := fun tree =>
  let (after, outcome) := run tree
  match outcome with
  | .ok value => .ok value after
  | .error error => .error error after

@[spec] theorem spec_mutation {Error A : Type} (run : BorrowTree → BorrowTree × Except Error A)
    (post : A → BorrowTree → Prop) (failure : Error → BorrowTree → Prop) :
    Triple (mutation run)
      (fun tree => match run tree with
        | (after, .ok value) => post value after
        | (after, .error error) => failure error after)
      post failure := by
  apply Triple.iff.mpr
  intro tree safe
  simp only [wp, WP.wpTrans, mutation]
  rcases h : run tree with ⟨after, result⟩
  cases result <;> simpa only [h] using safe

def insertChild (offset : Size) (parent : ProvenanceExtra) (tag : BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool) :
    EStateM BorrowTree.ChildInsertError BorrowTree Unit :=
  mutation fun tree =>
    let result := tree.newChild offset parent tag inside outside held
    (result.tree, result.outcome)

def expose (tags : ProtectedTags) (tag : BorTag) : EStateM BorrowTree.TreeMutationError BorrowTree Unit :=
  mutation fun tree =>
    let result := tree.exposeTag tags tag
    (result.tree, result.outcome)

def release (tag : BorTag) (tags : ProtectedTags) :
    EStateM BorrowTree.ProtectorReleaseStatus BorrowTree Unit :=
  mutation fun tree =>
    let result := tree.releaseProtector tag tags
    (result.tree, match result.status with
      | .Released => .ok ()
      | status => .error status)

/-- Deallocation begins with the exact ranged write. Its successor feeds the
strong-protector scan only when the write completes. -/
def deallocatePre (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags) (finish : BorrowTree.BorrowTreeDeallocResult → Prop) : Prop :=
  BorrowTree.RangeVerification.accessContract tree provenance offset length .Write tags
    .VisitChildrenOfAccessed fun accessed =>
      BorrowTree.RangeVerification.deallocateAfterWritePre accessed provenance offset length tags finish

theorem deallocatePre_iff (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags) (finish : BorrowTree.BorrowTreeDeallocResult → Prop) :
    deallocatePre tree provenance offset length tags finish ↔
      finish (tree.deallocateBorrowRange provenance offset length tags) := by
  unfold deallocatePre
  rw [← BorrowTree.RangeVerification.accessContract_iff, BorrowTree.deallocateBorrowRange_eq]
  exact (BorrowTree.RangeVerification.deallocateAfterWritePre_iff _ _ _ _ _ _).symm

def deallocate (provenance : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags) : EStateM BorrowTree.BorrowTreeDeallocStatus BorrowTree Unit :=
  mutation fun tree =>
    let result := tree.deallocateBorrowRange provenance offset length tags
    (result.tree, match result.status with
      | .Deallocated => .ok ()
      | status => .error status)

@[spec] theorem spec_deallocate (provenance : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags) (post : Unit → BorrowTree → Prop)
    (failure : BorrowTree.BorrowTreeDeallocStatus → BorrowTree → Prop) :
    Triple (deallocate provenance offset length tags)
      (fun tree => deallocatePre tree provenance offset length tags
        (fun result => match result.status with
          | .Deallocated => post () result.tree
          | status => failure status result.tree)) post failure := by
  apply Triple.iff.mpr
  intro tree safe
  rw [deallocatePre_iff] at safe
  simp only [wp, WP.wpTrans, deallocate, mutation]
  generalize tree.deallocateBorrowRange provenance offset length tags = result at *
  rcases result with ⟨after, status⟩
  cases status <;> exact safe

private def machineDeallocationPre {K U : Type}
    (retain : Allocation Provenance BorrowTree → PlaceMachine.Machine K U → PlaceMachine.Machine K U)
    (allocation : Allocation Provenance BorrowTree) (provenance : ProvenanceExtra) (size : Size)
    (post : Unit → PlaceMachine.Machine K U → Prop)
    (failure : StepError → PlaceMachine.Machine K U → Prop) (before : PlaceMachine.Machine K U) : Prop :=
  match before.borrowTracker with
  | none => post () before
  | some tracker =>
    deallocatePre allocation.extra provenance Size.ZERO size tracker.global.protectedTags fun result =>
      let after := retain (allocation.setExtra result.tree) before
      if result.status != .Deallocated then
        failure (.undefinedBehavior s!"Tree Borrows deallocation: {reprStr result.status}") after
      else post () after

/-- The canonical deallocation hook presents the detached successor on
success and on Tree Borrows failure. -/
@[spec] theorem spec_treeDeallocation {K U : Type}
    (retain : Allocation Provenance BorrowTree → PlaceMachine.Machine K U → PlaceMachine.Machine K U)
    (allocation : Allocation Provenance BorrowTree) (provenance : ProvenanceExtra) (size : Size)
    (post : Unit → PlaceMachine.Machine K U → Prop)
    (failure : StepError → PlaceMachine.Machine K U → Prop) :
    Triple (AllocationMachine.treeDeallocation retain allocation provenance size)
      (machineDeallocationPre retain allocation provenance size post failure) post failure := by
  apply Triple.iff.mpr
  intro before safe
  unfold machineDeallocationPre at safe
  simp only [wp, WP.wpTrans, AllocationMachine.treeDeallocation, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, EStateM.bind]
  cases found : before.borrowTracker with
  | none =>
    rw [found] at safe
    exact safe
  | some tracker =>
    rw [found] at safe
    dsimp only at safe
    rw [deallocatePre_iff] at safe
    dsimp only
    generalize allocation.extra.deallocateBorrowRange provenance Size.ZERO size
      tracker.global.protectedTags = result at *
    rcases result with ⟨after, status⟩
    cases status <;> exact safe

def collect (live : Array BorTag) : EStateM BorrowTree.TreeGcError BorrowTree Unit :=
  mutation fun tree =>
    let result := tree.removeUnreachableTags live
    (result.tree, result.outcome)

attribute [spec] insertChild expose release collect

private theorem access_missing (tree : BorrowTree) (tag : BorTag) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (missing : tree.indexOfTag tag = none) :
    tree.performBorrowAccessRange (.concrete tag) offset length kind tags mode =
      ⟨tree, #[], .MissingTag tag⟩ := by
  simp [BorrowTree.performBorrowAccessRange, missing]

/-- Even a zero-length access still resolves concrete provenance. -/
theorem accessPre_missingTag (tree : BorrowTree) (tag : BorTag) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (failure : BorrowTree.BorrowTreeAccessStatus →
      BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (missing : tree.indexOfTag tag = none) :
    accessPre tree (.concrete tag) offset length kind tags mode post failure ↔
      failure (.MissingTag tag) tree #[] := by
  simp [accessPre_iff, access_missing tree tag offset length kind tags mode missing]

theorem accessPre_zero (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (failure : BorrowTree.BorrowTreeAccessStatus →
      BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (zero : length.bytes = 0) :
    accessPre tree provenance offset length kind tags mode post failure ↔
      match provenance with
      | .concrete tag =>
        if (tree.indexOfTag tag).isNone then failure (.MissingTag tag) tree #[] else post tree #[]
      | .wildcard => post tree #[] := by
  cases provenance with
  | concrete tag =>
    cases found : tree.indexOfTag tag <;>
      simp [accessPre_iff, BorrowTree.performBorrowAccessRange, found, DedupRangeMap.iterMut,
        DedupRangeMap.iterMutWithClone, zero, Id.run, bind, Bind.bind, pure, Pure.pure]
  | wildcard =>
    simp [accessPre_iff, BorrowTree.performBorrowAccessRange, DedupRangeMap.iterMut,
      DedupRangeMap.iterMutWithClone, zero, Id.run, bind, Bind.bind, pure, Pure.pure]

/-- Map preparation can split the location map before reporting failure. -/
theorem access_range_failure (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (source : match provenance with
      | .concrete tag => (tree.indexOfTag tag).isSome
      | .wildcard => True)
    (error : DedupRangeMapError)
    (failed : (tree.locations.iterMut offset length).outcome = .error error) :
    tree.performBorrowAccessRange provenance offset length kind tags mode =
      ⟨{ tree with locations := (tree.locations.iterMut offset length).state }, #[],
        .RangeMapFailure error⟩ := by
  cases provenance with
  | concrete tag =>
    cases found : tree.indexOfTag tag with
    | none => simp [found] at source
    | some index => simp [BorrowTree.performBorrowAccessRange, found, failed]
  | wildcard => simp [BorrowTree.performBorrowAccessRange, failed]

/-- A write covering a fresh allocation through its root requires no conditions
on the existing global protector table. The original visit trace remains
available to the caller. -/
theorem accessPre_fresh_full_write (tag : BorTag) (size : Size) (tags : ProtectedTags)
    (post : BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (failure : BorrowTree.BorrowTreeAccessStatus →
      BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop) :
    accessPre (BorrowTree.new tag size) (.concrete tag) Size.ZERO size .Write tags
      .VisitChildrenOfAccessed post failure ↔
    post (BorrowTree.new tag size)
      ((BorrowTree.new tag size).performBorrowAccessRange (.concrete tag) Size.ZERO size
        .Write tags .VisitChildrenOfAccessed).locations := by
  obtain ⟨completed, preserved⟩ := BorrowTree.fresh_root_full_write tag size tags
  rw [accessPre_iff]
  dsimp only
  rw [completed, preserved]

/-- Duplicate insertion can already have replaced the key mapping before
reporting the failed retag. -/
theorem insertChild_duplicate (tree : BorrowTree) (offset : Size) (parent : ProvenanceExtra)
    (tag : BorTag) (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (duplicate : tree.tagMapping.insert tag = .DuplicateKeyAfterReplacement mapping index) :
    tree.newChild offset parent tag inside outside held =
      ⟨{ tree with tagMapping := mapping }, .error (.DuplicateTag tag)⟩ := by
  simp [BorrowTree.newChild, duplicate]

theorem expose_missing (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (missing : tree.indexOfTag tag = none) :
    tree.exposeTag tags tag = ⟨tree, .error (.MissingTag tag)⟩ := by
  simp [BorrowTree.exposeTag, missing]

theorem expose_already (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (index : UniIndex) (node : TreeNode)
    (found : tree.indexOfTag tag = some index) (getNode : tree.nodeAt index = some node)
    (exposed : node.isExposed = true) :
    tree.exposeTag tags tag = ⟨tree, .ok ()⟩ := by
  simp [BorrowTree.exposeTag, found, getNode, exposed]

theorem release_missing (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (missing : tree.indexOfTag tag = none) :
    tree.releaseProtector tag tags = ⟨tree, .MissingTag tag⟩ := by
  simp [BorrowTree.releaseProtector, missing]

/-- Deallocation cannot proceed to its strong-protector scan if the initial
write fails. The original access status and mutated tree are retained. -/
theorem deallocate_access_failure (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (tags : ProtectedTags)
    (failed : (tree.performBorrowAccessRange provenance offset length .Write tags
      .VisitChildrenOfAccessed).status ≠ .Completed) :
    tree.deallocateBorrowRange provenance offset length tags =
      let accessed := tree.performBorrowAccessRange provenance offset length .Write tags
        .VisitChildrenOfAccessed
      ⟨accessed.tree, .AccessFailure accessed.status⟩ := by
  simp [BorrowTree.deallocateBorrowRange, BorrowTree.deallocateAfterWrite, bne_iff_ne, failed]

end Miri.Verification.TreeBorrowsWP
