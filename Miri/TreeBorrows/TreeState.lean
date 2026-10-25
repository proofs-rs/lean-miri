import Miri.TreeBorrows.UniMap
import Miri.TreeBorrows.LocationState
import Miri.TreeBorrows.NormalTree
import Miri.TreeBorrows.GlobalState
import Miri.DataStructures.DedupRangeMap
import Miri.ABI.Size
import Miri.Memory.Identity

/-!
The allocation-local state layout from Miri's `tree_borrows/tree.rs`:
tag-to-index map, indexed nodes, per-range location data, and ordered roots.
The first constructor is the exact `Tree::new` root state. Diagnostic-only
node history is intentionally omitted. Child insertion and access traversal
are separate operations.
-/

namespace Miri.TreeBorrows

open Miri.ABI
open Miri.DataStructures

/-- Per-node information consumed by tree traversal and permission defaults.
The source's `NodeDebugInfo` name is retained because `miri_pointer_name` and
`miri_print_borrow_state` expose it. Access history is diagnostic-only and is
not needed to print the current tree.
-/
structure TreeNode where
  tag : Miri.Memory.BorTag
  parent : Option UniIndex
  children : Array UniIndex := #[]
  defaultInitialPermission : Permission
  defaultInitialSifa : IdempotentForeignAccess
  isExposed : Bool := false
  debugName : Option String := none
  deriving DecidableEq, Repr

namespace TreeNode

def defaultLocationState (node : TreeNode) : Tree.LocationState :=
  ⟨node.defaultInitialPermission, false, node.defaultInitialSifa⟩

end TreeNode

/-- Willard-cache counters for one node at one homogeneous byte range.
Counters keep the source's `u16` width.
-/
structure ExposedCacheNode where
  localWrites : UInt16 := 0
  localReads : UInt16 := 0
  deriving DecidableEq, Repr, Inhabited

inductive WildcardAccessRelatedness where
  | LocalAccess
  | ForeignAccess
  | EitherAccess
  deriving DecidableEq, Repr, Inhabited

/-- Wildcard-relatedness cache for one location range. -/
structure ExposedCache where
  nodes : UniValMap ExposedCacheNode := {}
  deriving DecidableEq, Repr, Inhabited

inductive ExposedCacheError where
  | MissingNode (index : UniIndex)
  | InvalidIndex (index : Nat)
  | ParentCycle (index : UniIndex)
  deriving DecidableEq, Repr

structure ExposedCacheUpdate where
  cache : ExposedCache
  outcome : Except ExposedCacheError Unit
  deriving DecidableEq, Repr

namespace ExposedCache

def accessRelatedness (cache : ExposedCache) (root id : UniIndex)
    (kind : AccessKind) (isWildcardTree onlyForeign : Bool) :
    Option WildcardAccessRelatedness := Id.run do
  let rootState := cache.nodes.get root |>.getD {}
  let nodeState := cache.nodes.get id |>.getD {}
  let (total, localCount) := match kind with
    | .Read => (rootState.localReads.toNat, nodeState.localReads.toNat)
    | .Write => (rootState.localWrites.toNat, nodeState.localWrites.toNat)
  let total := total + (if isWildcardTree then 1 else 0)
  let relatedness :=
    if total == 0 then none
    else if total == localCount then some .LocalAccess
    else if localCount == 0 then some .ForeignAccess
    else some .EitherAccess
  if onlyForeign then
    match relatedness with
    | some .LocalAccess | none => return none
    | some .ForeignAccess | some .EitherAccess => return some .ForeignAccess
  else
    return relatedness

private def hasReadExposure : WildcardAccessLevel → Bool
  | .None => false
  | .Read | .Write => true

private def hasWriteExposure : WildcardAccessLevel → Bool
  | .Write => true
  | .None | .Read => false

/-- Source `ExposedCache::update_exposure`: update the node's counters and
propagate the same exposure delta through each ancestor. On malformed node
indices/cycles, preserve all earlier counter mutations in the returned cache.
-/
def updateExposure (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (id : UniIndex) (oldLevel newLevel : WildcardAccessLevel) : ExposedCacheUpdate := Id.run do
  if oldLevel == newLevel then return { cache, outcome := .ok () }
  let mut current := cache
  let mut next := some id
  let mut steps := 0
  let mut outcome : Except ExposedCacheError Unit := .ok ()
  let mut active := true
  while active do
    if steps > nodes.size then
      outcome := .error (.ParentCycle (next.getD id))
      active := false
    else
      match next with
      | none => active := false
      | some index =>
          match nodes.get index with
          | none =>
              outcome := .error (.MissingNode index)
              active := false
          | some node =>
              let old := current.nodes.get index |>.getD {}
              let incrementWrites := !hasWriteExposure oldLevel && hasWriteExposure newLevel
              let decrementWrites := hasWriteExposure oldLevel && !hasWriteExposure newLevel
              let incrementReads := !hasReadExposure oldLevel && hasReadExposure newLevel
              let decrementReads := hasReadExposure oldLevel && !hasReadExposure newLevel
              let updated := {
                localWrites :=
                  if incrementWrites then old.localWrites + 1
                  else if decrementWrites then old.localWrites - 1
                  else old.localWrites
                localReads :=
                  if incrementReads then old.localReads + 1
                  else if decrementReads then old.localReads - 1
                  else old.localReads
              }
              current := { current with nodes := current.nodes.insert index updated }
              next := node.parent
              steps := steps + 1
              if next.isNone then active := false
  return { cache := current, outcome }

def remove (cache : ExposedCache) (idx : UniIndex) : ExposedCache :=
  { cache with nodes := cache.nodes.remove idx }

end ExposedCache

/-- The source's `LocationTree`: lazily stored permission state and one
exposed-node cache per homogeneous range. -/
structure LocationTree where
  perms : UniValMap Tree.LocationState := {}
  exposedCache : ExposedCache := {}
  deriving DecidableEq, Repr, Inhabited

/-- Allocation-local tree state. `roots` begins with the allocation's unique
root and may later contain ordered wildcard roots.
-/
structure BorrowTree where
  tagMapping : UniKeyMap Miri.Memory.BorTag
  nodes : UniValMap TreeNode
  locations : DedupRangeMap LocationTree
  roots : Array UniIndex
  deriving DecidableEq, Repr

inductive DebugNameError where
  | missingTag (tag : Miri.Memory.BorTag)
  | missingNode (index : UniIndex)
  | missingParent (tag : Miri.Memory.BorTag) (distance : Nat)
  deriving DecidableEq, Repr

namespace BorrowTree

/-- Source `Tree::nth_parent`, with malformed/exhausted ancestry retained as a
checked machine error by diagnostic callers instead of an unchecked unwrap. -/
def nthParent (tree : BorrowTree) (tag : Miri.Memory.BorTag) (distance : Nat) :
    Except DebugNameError Miri.Memory.BorTag := do
  let some index := tree.tagMapping.get tag
    | throw (.missingTag tag)
  let mut current := index
  for step in [:distance] do
    let some node := tree.nodes.get current
      | throw (.missingNode current)
    let some parent := node.parent
      | throw (.missingParent tag (step + 1))
    current := parent
  let some node := tree.nodes.get current
    | throw (.missingNode current)
  return node.tag

/-- Source `NodeDebugInfo::add_name`: several names for one tag are joined
with `", "` in their insertion order. -/
def addDebugName (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (name : String) : Except DebugNameError BorrowTree := do
  let some index := tree.tagMapping.get tag
    | throw (.missingTag tag)
  let some node := tree.nodes.get index
    | throw (.missingNode index)
  let debugName := match node.debugName with
    | none => name
    | some previous => previous ++ ", " ++ name
  return {tree with nodes := tree.nodes.insert index {node with debugName := some debugName}}

/-- Source `Tree::give_pointer_debug_name`, including ancestor selection. -/
def givePointerDebugName (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (distance : Nat) (name : String) : Except DebugNameError BorrowTree := do
  let ancestor ← tree.nthParent tag distance
  tree.addDebugName ancestor name

private def trimLocationForRangeEquality (location : LocationTree) : LocationTree :=
  { location with
    perms := location.perms.trimTrailingNone
    exposedCache := { nodes := location.exposedCache.nodes.trimTrailingNone } }

private def rootIndex : UniIndex := ⟨0⟩

/-- Source `Tree::new`: disabled default at out-of-bounds/uninitialized
locations, one non-exposed root, and an accessed Unique permission throughout
the allocation's in-bounds bytes.
-/
def new (rootTag : Miri.Memory.BorTag) (size : Size) : BorrowTree := Id.run do
  let root := rootIndex
  let rootDefault := Permission.newDisabled
  let mapping : UniKeyMap Miri.Memory.BorTag :=
    { mapping := #[(rootTag, root)], deassigned := #[] }
  let rootNode : TreeNode := {
    tag := rootTag
    parent := none
    children := #[]
    defaultInitialPermission := rootDefault
    defaultInitialSifa := .None
    isExposed := false
  }
  let mut perms : UniValMap Tree.LocationState := {}
  perms := perms.insert root ⟨Permission.newUnique, true, .None⟩
  let initialLocation : LocationTree := { perms, exposedCache := {} }
  let locations := DedupRangeMap.new size initialLocation
  let mut nodes : UniValMap TreeNode := {}
  nodes := nodes.insert root rootNode
  return {
    tagMapping := mapping
    nodes
    locations
    roots := #[root]
  }

def indexOfTag (tree : BorrowTree) (tag : Miri.Memory.BorTag) : Option UniIndex :=
  tree.tagMapping.get tag

def nodeAt (tree : BorrowTree) (idx : UniIndex) : Option TreeNode :=
  tree.nodes.get idx

/-- Current or lazily initialized per-location state for a node. -/
def locationStateAt (tree : BorrowTree) (location : LocationTree) (idx : UniIndex) :
    Option Tree.LocationState := do
  let node ← tree.nodeAt idx
  return (location.perms.get idx).getD node.defaultLocationState

private def traversalProjection (tree : BorrowTree) : Tree.TraversalTree :=
  ⟨tree.nodes.data.map fun entry =>
    match entry with
    | none => ⟨none, []⟩
    | some node =>
        ⟨node.parent.map UniIndex.toNat, node.children.toList.map UniIndex.toNat⟩⟩

/-- Source LocationTree::get_min_exposed_child. This deliberately scans node
topology rather than relying on enabled-only cache counts.
-/
private def minExposedChild (tree : BorrowTree) (start : UniIndex) : Option Miri.Memory.BorTag :=
  Id.run do
    let mut stack := #[start]
    let mut steps := 0
    let mut minimum : Option Miri.Memory.BorTag := none
    while !stack.isEmpty && steps ≤ tree.nodes.size do
      steps := steps + 1
      let some index := stack.back? | return minimum
      stack := stack.pop
      match tree.nodes.get index with
      | none => pure ()
      | some node =>
          let alreadySmaller := minimum.any fun tag => tag.value < node.tag.value
          if !alreadySmaller then
            for child in node.children do
              stack := stack.push child
            if node.isExposed &&
                (minimum.isNone || minimum.any (fun tag => node.tag.value < tag.value)) then
              minimum := some node.tag
    return minimum

private def normalProjection (tree : BorrowTree) (location : LocationTree)
    (protectedTags : ProtectedTags) : Tree.NormalTreeState :=
  let defaults := tree.nodes.data.map fun entry =>
    match entry with
    | some node => node.defaultLocationState
    | none => ⟨.Disabled, false, .None⟩
  let locationStates := tree.nodes.data.mapIdx fun position _ =>
    match UniIndex.ofNat? position with
    | none => none
    | some index => location.perms.get index
  let protectedNodes := tree.nodes.entries.toList.filterMap fun (index, node) =>
    if protectedTags.contains node.tag then some index.toNat else none
  {
    topology := traversalProjection tree
    defaultStates := defaults
    protectedNodes
    locationStates
  }

structure NormalLocationAccessResult where
  location : LocationTree
  access : Tree.NormalAccessResult
  outcome : Except ExposedCacheError Unit
  deriving DecidableEq, Repr

inductive TreeMutationError where
  | MissingTag (tag : Miri.Memory.BorTag)
  | MissingNode (index : UniIndex)
  | ExposedCache (error : ExposedCacheError)
  | RangeMap (error : DedupRangeMapError)
  deriving DecidableEq, Repr

structure TreeMutationResult where
  tree : BorrowTree
  outcome : Except TreeMutationError Unit
  deriving DecidableEq, Repr

inductive ChildInsertError where
  | DuplicateTag (tag : Miri.Memory.BorTag)
  | TagIndexExhausted (active : Nat)
  | MissingParentTag (tag : Miri.Memory.BorTag)
  | OutsidePermissionNotInitial (permission : Permission)
  | OutsideUniquePermission
  | ProtectedReservedIM
  | InsidePermissionNotInitial (permission : Permission)
  | InsideSifaMismatch (permission : Permission)
  | InsidePermissionInvariant (permission : Permission)
  | SizeError (error : SizeError)
  | RangeMapError (error : DedupRangeMapError)
  | MissingNode (index : UniIndex)
  | ParentCycle (index : UniIndex)
  deriving DecidableEq, Repr

structure ChildInsertResult where
  tree : BorrowTree
  outcome : Except ChildInsertError Unit
  deriving DecidableEq, Repr

inductive TreeGcError where
  | MissingNode (index : UniIndex)
  | MissingChildPosition (parent : UniIndex) (position : Nat)
  | MissingReplacementChild (index : UniIndex)
  | EmptyTraversalStack (root : UniIndex)
  | ParentCycle (root : UniIndex)
  | RangeMerge (error : DedupRangeMapError)
  deriving DecidableEq, Repr

structure TreeGcResult where
  tree : BorrowTree
  outcome : Except TreeGcError Unit
  deriving DecidableEq, Repr

private def failingNode? : Tree.NormalAccessStatus → Option Nat
  | .Completed => none
  | .TransitionError node _
  | .RecordDebugAssertion node
  | .PermissionInvariantFailure node
  | .TransitionApplicationInvariantFailure node
  | .PossibleInvariantFailure node
  | .MissingLocationState node => some node

inductive WildcardAccessStatus where
  | Completed
  | EmptyTraversalStack (root : UniIndex)
  | NoValidExposedReferences (root : UniIndex) (node : Option UniIndex)
  | MissingNode (index : UniIndex)
  | RecordDebugAssertion (index : UniIndex)
  | TransitionError (index : UniIndex) (error : Diagnostics.TransitionError)
  | CacheFailure (error : ExposedCacheError)
  | PermissionInvariantFailure (index : UniIndex)
  | TransitionApplicationInvariantFailure (index : UniIndex)
  | PossibleInvariantFailure (index : UniIndex)
  | ParentCycle (root : UniIndex)
  deriving DecidableEq, Repr

structure WildcardLocationAccessResult where
  location : LocationTree
  status : WildcardAccessStatus
  deriving DecidableEq, Repr

private def wildcardRelatedness (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (isWildcardTree onlyForeign : Bool) :
    Option WildcardAccessRelatedness :=
  cache.accessRelatedness root index kind isWildcardTree onlyForeign

private def exactRelatedness? : WildcardAccessRelatedness → Option AccessRelatedness
  | .LocalAccess => some .LocalAccess
  | .ForeignAccess => some .ForeignAccess
  | .EitherAccess => none

/-- Source `LocationTree::perform_wildcard_access`. The stack implements the
source visitor's child-first, postorder traversal. Relatedness and SIFA skip
decisions are recomputed against the cache as child transitions change it.
-/
def performWildcardAccessAt (tree : BorrowTree) (initialLocation : LocationTree)
    (root : UniIndex) (maxLocalTag : Option Miri.Memory.BorTag)
    (kind : AccessKind) (protectedTags : ProtectedTags) (isWildcardTree : Bool) :
    WildcardLocationAccessResult := Id.run do
  let mut location := initialLocation
  let mut hasValidExposed := false
  let mut status := WildcardAccessStatus.Completed
  let mut stack : Array (UniIndex × Bool) := #[(root, false)]
  let mut steps := 0
  while !stack.isEmpty && status == .Completed do
    steps := steps + 1
    if steps > tree.nodes.size * 2 + 1 then
      status := .ParentCycle root
    else
      let some (index, afterChildren) := stack.back?
        | status := .EmptyTraversalStack root
          continue
      if !afterChildren then
        let some node := tree.nodes.get index
          | status := .MissingNode index
            continue
        let onlyForeign := match maxLocalTag with
          | some maximum => maximum.value < node.tag.value
          | none => false
        let relatedness := wildcardRelatedness location.exposedCache root index kind
          isWildcardTree onlyForeign
        let state := location.perms.get index |>.getD node.defaultLocationState
        let skip := match relatedness.bind exactRelatedness? with
          | some rel =>
              match state.skipIfKnownNoop kind rel with
              | .SkipSelfAndChildren => true
              | .Recurse => false
          | none => false
        if skip then
          stack := stack.pop
        else
          stack := stack.pop.push (index, true)
          for child in node.children do
            stack := stack.push (child, false)
      else
        stack := stack.pop
        let some node := tree.nodes.get index
          | status := .MissingNode index
            continue
        let onlyForeign := match maxLocalTag with
          | some maximum => maximum.value < node.tag.value
          | none => false
        let relatedness := wildcardRelatedness location.exposedCache root index kind
          isWildcardTree onlyForeign
        match relatedness with
        | none =>
            status := .NoValidExposedReferences root (some index)
        | some related =>
            let isProtected := protectedTags.contains node.tag
            let oldState := location.perms.get index |>.getD node.defaultLocationState
            if node.isExposed &&
                (oldState.permission.strongestAllowedLocalAccess isProtected).allows kind &&
                (maxLocalTag.isNone || maxLocalTag.any
                  (fun maximum => maximum.value >= node.tag.value)) then
              hasValidExposed := true
            let (withState, state) := location.perms.orInsert index node.defaultLocationState
            location := { location with perms := withState }
            match exactRelatedness? related with
            | none => pure ()
            | some rel =>
                match state.recordNewAccess kind rel with
                | .DebugAssertion => status := .RecordDebugAssertion index
                | .Recorded recorded =>
                    location := { location with perms := location.perms.insert index recorded }
                    let access := recorded.performAccess kind rel isProtected
                    let updatedState := access.resultingState
                    location := { location with perms := location.perms.insert index updatedState }
                    match access with
                    | .Success _ transition =>
                        if node.isExposed && !transition.isNoop then
                          let oldLevel := oldState.permission.strongestAllowedLocalAccess isProtected
                          let newLevel := updatedState.permission.strongestAllowedLocalAccess isProtected
                          let update := location.exposedCache.updateExposure tree.nodes index
                            oldLevel newLevel
                          location := { location with exposedCache := update.cache }
                          match update.outcome with
                          | .error error => status := .CacheFailure error
                          | .ok _ => pure ()
                    | .Error _ error => status := .TransitionError index error
                    | .PermissionInvariantFailure _ => status := .PermissionInvariantFailure index
                    | .TransitionApplicationInvariantFailure _ =>
                        status := .TransitionApplicationInvariantFailure index
                    | .PossibleInvariantFailure _ => status := .PossibleInvariantFailure index
  if status == .Completed && !hasValidExposed && !isWildcardTree then
    status := .NoValidExposedReferences root none
  return { location, status }

/-- Perform the source normal-tree component at one actual tree location.
Permission transitions are delegated to `NormalTreeState`; this operation
projects the source `UniValMap` topology and lazy defaults, writes state back
to the real maps, and applies exposed-cache deltas in visit order. Additional
wildcard roots are handled by the separate wildcard-access component.
-/
def performNormalAccessAt (tree : BorrowTree) (location : LocationTree)
    (start : UniIndex) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : NormalLocationAccessResult := Id.run do
  let access := Tree.NormalTreeState.performAccess
    (normalProjection tree location protectedTags) start.toNat kind mode
  let mut nextLocation := location
  for position in [:access.tree.locationStates.size] do
    match access.tree.locationStates[position]? with
    | some (some state) =>
        match UniIndex.ofNat? position with
        | some index =>
            nextLocation := { nextLocation with perms := nextLocation.perms.insert index state }
        | none => pure ()
    | _ => pure ()
  let mut cacheOutcome : Except ExposedCacheError Unit := .ok ()
  for event in access.visited do
    if cacheOutcome matches .ok _ then
      match UniIndex.ofNat? event.node with
      | none => cacheOutcome := .error (.InvalidIndex event.node)
      | some index =>
        match tree.nodeAt index with
        | none => cacheOutcome := .error (.MissingNode index)
        | some node =>
          if node.isExposed && failingNode? access.status != some event.node then
            match tree.locationStateAt location index, access.tree.stateAt event.node with
            | some oldState, some newState =>
                match performAccessTransition kind event.relatedness oldState.permission
                    (protectedTags.contains node.tag) with
                | .Transition transition =>
                    if !transition.isNoop then
                      let oldLevel := oldState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let newLevel := newState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let update := nextLocation.exposedCache.updateExposure tree.nodes index
                        oldLevel newLevel
                      nextLocation := { nextLocation with exposedCache := update.cache }
                      cacheOutcome := update.outcome
                | .UndefinedBehavior | .ImpossibleProtectedReservedIM => pure ()
            | _, _ => cacheOutcome := .error (.MissingNode index)
  return { location := nextLocation, access, outcome := cacheOutcome }

private def updateEveryLocation (tree : BorrowTree)
    (update : LocationTree → LocationTree × Except TreeMutationError Unit) :
    TreeMutationResult := Id.run do
  let mut current := tree
  for position in [:tree.locations.entries.size] do
    match current.locations.index position with
    | .error error =>
        return { tree := current, outcome := .error (.RangeMap error) }
    | .ok segment =>
        let (nextLocation, outcome) := update segment.data
        let mutation := current.locations.setAtPos position nextLocation
        current := { current with locations := mutation.state }
        match outcome, mutation.outcome with
        | .error error, _ => return { tree := current, outcome := .error error }
        | .ok (), .error error =>
            return { tree := current, outcome := .error (.RangeMap error) }
        | .ok (), .ok () => pure ()
  return { tree := current, outcome := .ok () }

/-- Source `Tree::expose_tag`, including the per-range Willard-cache update.
The global protected-tag table determines which local accesses remain valid
through this exposed tag.
-/
def exposeTag (tree : BorrowTree) (protectedTags : ProtectedTags)
    (tag : Miri.Memory.BorTag) : TreeMutationResult := Id.run do
  let some index := tree.indexOfTag tag
    | return { tree, outcome := .error (.MissingTag tag) }
  let some node := tree.nodeAt index
    | return { tree, outcome := .error (.MissingNode index) }
  if node.isExposed then return { tree, outcome := .ok () }
  let exposedTree := { tree with nodes := tree.nodes.insert index { node with isExposed := true } }
  let update := updateEveryLocation exposedTree fun location =>
    let state := location.perms.get index |>.getD node.defaultLocationState
    let accessLevel := state.permission.strongestAllowedLocalAccess
      (protectedTags.contains tag)
    let cacheUpdate := location.exposedCache.updateExposure exposedTree.nodes index
      .None accessLevel
    let nextLocation := { location with exposedCache := cacheUpdate.cache }
    let outcome := cacheUpdate.outcome.mapError TreeMutationError.ExposedCache
    (nextLocation, outcome)
  return update

/-- Source `update_exposure_for_protector_release`: exposed nodes retain their
exposure, while the cache counters change from protected to unprotected local
permission strength.
-/
def updateExposureForProtectorRelease (tree : BorrowTree)
    (tag : Miri.Memory.BorTag) : TreeMutationResult := Id.run do
  let some index := tree.indexOfTag tag
    | return { tree, outcome := .error (.MissingTag tag) }
  let some node := tree.nodeAt index
    | return { tree, outcome := .error (.MissingNode index) }
  if !node.isExposed then return { tree, outcome := .ok () }
  return updateEveryLocation tree fun location =>
    let state := location.perms.get index |>.getD node.defaultLocationState
    let wasAllowed := state.permission.strongestAllowedLocalAccess true
    let nowAllowed := state.permission.strongestAllowedLocalAccess false
    let cacheUpdate := location.exposedCache.updateExposure tree.nodes index
      wasAllowed nowAllowed
    let nextLocation := { location with exposedCache := cacheUpdate.cache }
    let outcome := cacheUpdate.outcome.mapError TreeMutationError.ExposedCache
    (nextLocation, outcome)

private def weakerSifa (left right : IdempotentForeignAccess) : IdempotentForeignAccess :=
  if left.rank ≤ right.rank then left else right

/-- Restore the source parent-weaker/child-stronger SIFA invariant after a
retag, including lazy defaults and all already materialized location states.
-/
private def updateSifaAfterRetag (tree : BorrowTree) (start : UniIndex)
    (strongestAllowed : IdempotentForeignAccess) :
    BorrowTree × Except ChildInsertError Unit := Id.run do
  if strongestAllowed == .Write then return (tree, .ok ())
  let mut current := tree
  let mut cursor := some start
  let mut steps := 0
  let mut active := true
  while active do
    if steps > current.nodes.size then
      return (current, .error (.ParentCycle (cursor.getD start)))
    match cursor with
    | none => active := false
    | some index =>
        let some node := current.nodes.get index
          | return (current, .error (.MissingNode index))
        let (defaultSifa, defaultChanged) :=
          node.defaultInitialSifa.ensureNoStrongerThan strongestAllowed
        let mut anyChanged := defaultChanged
        for segment in current.locations.iterAll do
          if let some locationState := segment.data.perms.get index then
            let (_, changed) := locationState.idempotentForeignAccess
              |>.ensureNoStrongerThan strongestAllowed
            anyChanged := anyChanged || changed
        let locations := current.locations.modifyAll fun _ location =>
          match location.perms.get index with
          | none => location
          | some locationState =>
              let (sifa, _) := locationState.idempotentForeignAccess
                |>.ensureNoStrongerThan strongestAllowed
              let updatedState := { locationState with idempotentForeignAccess := sifa }
              { location with perms := location.perms.insert index updatedState }
        current := {
          current with
          locations
          nodes := current.nodes.insert index
            ({ node with defaultInitialSifa := defaultSifa })
        }
        if anyChanged then
          cursor := node.parent
          steps := steps + 1
        else
          active := false
  return (current, .ok ())

/-- Source `Tree::new_child`: allocate the tag index, attach a concrete child
or ordered wildcard root, store lazy defaults, materialize inside-range
permissions, and weaken ancestor SIFAs until the retag invariant is restored.
Mutation and invariant failures retain earlier source-ordered state changes.
-/
def newChild (tree : BorrowTree) (baseOffset : Size)
    (parentProvenance : Miri.Memory.ProvenanceExtra)
    (newTag : Miri.Memory.BorTag) (insidePermissions : DedupRangeMap Tree.LocationState)
    (outsidePermission : Permission) (isProtected : Bool) : ChildInsertResult := Id.run do
  let (mapping, newIndex, duplicate) := match tree.tagMapping.insert newTag with
    | .Inserted mapping index => (mapping, some index, false)
    | .DuplicateKeyAfterReplacement mapping index => (mapping, some index, true)
    | .Error mapping _ => (mapping, none, false)
  let mut current := { tree with tagMapping := mapping }
  if duplicate then return { tree := current, outcome := .error (.DuplicateTag newTag) }
  let some newIndex := newIndex
    | return { tree := current, outcome := .error (.TagIndexExhausted mapping.size) }
  let parentIndex := match parentProvenance with
    | .wildcard => some none
    | .concrete parentTag => (tree.tagMapping.get parentTag).map some
  let some parentIndex := parentIndex
    | return { tree := current, outcome := .error (.MissingParentTag (match parentProvenance with
        | .concrete tag => tag
        | .wildcard => newTag)) }
  if !outsidePermission.isInitial then
    return { tree := current, outcome := .error (.OutsidePermissionNotInitial outsidePermission) }
  if outsidePermission.isUnique then
    return { tree := current, outcome := .error .OutsideUniquePermission }
  let defaultSifa := match outsidePermission.strongestIdempotentForeignAccess isProtected with
    | .Access sifa => some sifa
    | .ImpossibleProtectedReservedIM => none
  let some defaultSifa := defaultSifa
    | return { tree := current, outcome := .error .ProtectedReservedIM }
  let node : TreeNode := {
    tag := newTag
    parent := parentIndex
    children := #[]
    defaultInitialPermission := outsidePermission
    defaultInitialSifa := defaultSifa
    isExposed := false
  }
  current := { current with nodes := current.nodes.insert newIndex node }
  match parentIndex with
  | none => current := { current with roots := current.roots.push newIndex }
  | some parent =>
      match current.nodes.get parent with
      | none => return { tree := current, outcome := .error (.MissingNode parent) }
      | some parentNode =>
          let updatedParent := { parentNode with children := parentNode.children.push newIndex }
          current := { current with nodes := current.nodes.insert parent updatedParent }
  let mut minimumSifa := defaultSifa
  for segment in insidePermissions.iterAll do
    let initial := segment.data.permission
    if !initial.isInitial then
      return { tree := current, outcome := .error (.InsidePermissionNotInitial initial) }
    let expectedSifa := match initial.strongestIdempotentForeignAccess isProtected with
      | .Access sifa => some sifa
      | .ImpossibleProtectedReservedIM => none
    let some expectedSifa := expectedSifa
      | return { tree := current, outcome := .error (.InsidePermissionInvariant initial) }
    if segment.data.idempotentForeignAccess != expectedSifa then
      return { tree := current, outcome := .error (.InsideSifaMismatch initial) }
    minimumSifa := weakerSifa minimumSifa segment.data.idempotentForeignAccess
    let start ← match Size.add (Size.ofBytes segment.range.start) baseOffset with
      | .ok start => pure start
      | .error error =>
          return { tree := current, outcome := .error (.SizeError error) }
    let rangeUpdate := current.locations.modifyRange start
      (Size.ofBytes (segment.range.stop - segment.range.start)) fun _ location =>
        { location with perms := location.perms.insert newIndex segment.data }
    current := { current with locations := rangeUpdate.state }
    match rangeUpdate.outcome with
    | .error error => return { tree := current, outcome := .error (.RangeMapError error) }
    | .ok () => pure ()
  match parentIndex with
  | none => return { tree := current, outcome := .ok () }
  | some parent =>
      let (updated, outcome) := updateSifaAfterRetag current parent minimumSifa
      return { tree := updated, outcome }

private def nodeIsUseless (tree : BorrowTree) (index : UniIndex)
    (liveTags : Array Miri.Memory.BorTag) : Bool :=
  match tree.nodes.get index with
  | none => false
  | some node => node.children.isEmpty && !liveTags.contains node.tag

/-- Source `Tree::can_be_replaced_by_single_child`: dead non-root nodes with
one child may be collapsed only when the parent's and child's permissions are
compatible at every represented byte range. -/
private def replacementChild? (tree : BorrowTree) (index : UniIndex)
    (liveTags : Array Miri.Memory.BorTag) : Option UniIndex := Id.run do
  let some node := tree.nodes.get index | return none
  if liveTags.contains node.tag || node.parent.isNone || node.children.size != 1 then
    return none
  let some childIndex := node.children[0]? | return none
  let some child := tree.nodes.get childIndex | return none
  let mut compatible := true
  for segment in tree.locations.iterAll do
    let parentPermission := (segment.data.perms.get index).map Tree.LocationState.permission
      |>.getD node.defaultInitialPermission
    let childPermission := (segment.data.perms.get childIndex).map Tree.LocationState.permission
      |>.getD child.defaultInitialPermission
    if !Permission.canBeReplacedByChild parentPermission childPermission then
      compatible := false
  if compatible then return some childIndex else return none

/-- Source `Tree::remove_useless_node`, removing the index from the node map,
every range's permission and exposure maps, then the reusable tag map. -/
private def removeUselessNode (tree : BorrowTree) (index : UniIndex) :
    BorrowTree × Except TreeGcError Unit := Id.run do
  let some node := tree.nodes.get index
    | return (tree, .error (.MissingNode index))
  let nodes := tree.nodes.remove index
  let locations := tree.locations.modifyAll fun _ location => {
    location with
    perms := location.perms.remove index
    exposedCache := location.exposedCache.remove index
  }
  let tagMapping := tree.tagMapping.remove node.tag
  return ({ tree with nodes, locations, tagMapping }, .ok ())

/-- Iterative postorder counterpart of `Tree::remove_useless_children`. The
explicit stack avoids Lean recursion limits and retains source child order.
Malformed indexes/cycles become results, preserving prior mutations. -/
private def removeUselessChildren (tree : BorrowTree) (root : UniIndex)
    (liveTags : Array Miri.Memory.BorTag) : TreeGcResult := Id.run do
  let mut current := tree
  let mut stack : Array (UniIndex × Nat) := #[(root, 0)]
  let mut steps := 0
  while !stack.isEmpty do
    steps := steps + 1
    if steps > current.nodes.size * 2 + 1 then
      return { tree := current, outcome := .error (.ParentCycle root) }
    let some (index, nthChild) := stack.back?
      | return { tree := current, outcome := .error (.EmptyTraversalStack root) }
    let some node := current.nodes.get index
      | return { tree := current, outcome := .error (.MissingNode index) }
    if nthChild < node.children.size then
      let some child := node.children[nthChild]?
        | return { tree := current, outcome := .error (.MissingChildPosition index nthChild) }
      let rest := stack.pop.push (index, nthChild + 1)
      stack := rest.push (child, 0)
    else
      let originalChildren := node.children
      let mut keptChildren : Array UniIndex := #[]
      for childIndex in originalChildren do
        if nodeIsUseless current childIndex liveTags then
          let (next, outcome) := removeUselessNode current childIndex
          current := next
          match outcome with
          | .error error => return { tree := current, outcome := .error error }
          | .ok () => pure ()
        else
          match replacementChild? current childIndex liveTags with
          | none => keptChildren := keptChildren.push childIndex
          | some replacement =>
              let (next, outcome) := removeUselessNode current childIndex
              current := next
              match outcome with
              | .error error => return { tree := current, outcome := .error error }
              | .ok () => pure ()
              let some replacementNode := current.nodes.get replacement
                | return { tree := current, outcome := .error (.MissingReplacementChild replacement) }
              let replacementNode := { replacementNode with parent := some index }
              let updatedNodes := current.nodes.insert replacement replacementNode
              current := { current with nodes := updatedNodes }
              keptChildren := keptChildren.push replacement
      let some currentNode := current.nodes.get index
        | return { tree := current, outcome := .error (.MissingNode index) }
      let currentNode := { currentNode with children := keptChildren }
      let updatedNodes := current.nodes.insert index currentNode
      current := { current with nodes := updatedNodes }
      stack := stack.pop
  return { tree := current, outcome := .ok () }

/-- Tags reported by source `VisitProvenance for Tree`: all roots and every
exposed node whose provenance may still permit an access. -/
def provenanceTags (tree : BorrowTree) : Array Miri.Memory.BorTag := Id.run do
  let mut tags := #[]
  for root in tree.roots do
    if let some node := tree.nodes.get root then tags := tags.push node.tag
  for (_, node) in tree.nodes.entries do
    if node.isExposed then tags := tags.push node.tag
  return tags

/-- Source `Tree::remove_unreachable_tags`: process each ordered root with
postorder leaf removal and safe single-child collapse, then thoroughly merge
adjacent equal location ranges. -/
def removeUnreachableTags (tree : BorrowTree)
    (liveTags : Array Miri.Memory.BorTag) : TreeGcResult := Id.run do
  let mut current := tree
  for root in tree.roots do
    let result := removeUselessChildren current root liveTags
    current := result.tree
    match result.outcome with
    | .error error => return { tree := current, outcome := .error error }
    | .ok () => pure ()
  -- Rust's `UniValMap::PartialEq` ignores trailing `None` values. Canonicalize
  -- the nested maps before the range map's structural equality check.
  current := { current with locations := current.locations.modifyAll fun _ loc =>
    trimLocationForRangeEquality loc }
  let merged := current.locations.mergeAdjacentThorough
  current := { current with locations := merged.state }
  match merged.outcome with
  | .error error => return { tree := current, outcome := .error (.RangeMerge error) }
  | .ok () => return { tree := current, outcome := .ok () }

structure BorrowTreeLocationResult where
  range : ByteRange
  normalAccess : Option Tree.NormalAccessResult
  deriving DecidableEq, Repr

inductive BorrowTreeAccessStatus where
  | Completed
  | MissingTag (tag : Miri.Memory.BorTag)
  | MultipleRoots (count : Nat)
  | RangeMapFailure (error : DedupRangeMapError)
  | LocationMapFailure (range : ByteRange) (error : DedupRangeMapError)
  | CacheFailure (range : ByteRange) (error : ExposedCacheError)
  | AccessFailure (range : ByteRange) (status : Tree.NormalAccessStatus)
  | WildcardFailure (range : ByteRange) (status : WildcardAccessStatus)
  deriving DecidableEq, Repr

structure BorrowTreeAccessResult where
  tree : BorrowTree
  locations : Array BorrowTreeLocationResult
  status : BorrowTreeAccessStatus
  deriving DecidableEq, Repr

inductive BorrowTreeDeallocStatus where
  | Deallocated
  | AccessFailure (status : BorrowTreeAccessStatus)
  | MultipleRoots (count : Nat)
  | MissingTag (tag : Miri.Memory.BorTag)
  | RangeMapFailure (error : DedupRangeMapError)
  | ProtectedDealloc (range : ByteRange) (node : UniIndex)
  deriving DecidableEq, Repr

structure BorrowTreeDeallocResult where
  tree : BorrowTree
  status : BorrowTreeDeallocStatus
  deriving DecidableEq, Repr

private structure TreeLocationAccessAtResult where
  location : LocationTree
  normalAccess : Option Tree.NormalAccessResult
  status : Option BorrowTreeAccessStatus

/-- Apply the source LocationTree::perform_access order: first the concrete
source tree, then each other root as a wildcard subtree. None provenance
starts with wildcard accesses on all roots.
-/
private def performTreeAccessAt (tree : BorrowTree) (location : LocationTree)
    (source? : Option UniIndex) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange) : TreeLocationAccessAtResult := Id.run do
  let mut currentLocation := location
  let mut normalAccess : Option Tree.NormalAccessResult := none
  let mut accessedRoot? : Option UniIndex := none
  let mut status : Option BorrowTreeAccessStatus := none
  if let some source := source? then
    let normal := tree.performNormalAccessAt currentLocation source kind protectedTags mode
    currentLocation := normal.location
    normalAccess := some normal.access
    match normal.outcome with
    | .error error =>
        return ⟨currentLocation, normalAccess, some (.CacheFailure range error)⟩
    | .ok () =>
        if normal.access.status != .Completed then
          return ⟨currentLocation, normalAccess,
            some (.AccessFailure range normal.access.status)⟩
        match UniIndex.ofNat? normal.access.root with
        | none =>
            return ⟨currentLocation, normalAccess,
              some (.AccessFailure range (.MissingLocationState normal.access.root))⟩
        | some root => accessedRoot? := some root
  let maxLocalTag := accessedRoot?.bind fun root => (tree.nodes.get root).map TreeNode.tag
  let minExposed := if mode == .SkipChildrenOfAccessed then
      source?.bind (minExposedChild tree)
    else none
  let mut stopOtherRoots := false
  for rootPosition in [:tree.roots.size] do
    if status.isNone && !stopOtherRoots then
      match tree.roots[rootPosition]? with
      | none => pure ()
      | some root =>
          let rootTag := (tree.nodes.get root).map TreeNode.tag
          let pastMinExposed := match rootTag, minExposed with
            | some tag, some minimum => tag.value > minimum.value
            | _, _ => false
          if mode == .SkipChildrenOfAccessed && pastMinExposed then
            stopOtherRoots := true
          else if accessedRoot? != some root then
            let wildcard := tree.performWildcardAccessAt currentLocation root
              maxLocalTag kind protectedTags (rootPosition != 0)
            currentLocation := wildcard.location
            if wildcard.status != .Completed then
              status := some (.WildcardFailure range wildcard.status)
  return ⟨currentLocation, normalAccess, status⟩

/-- Ranged access for concrete or wildcard provenance. Tree state and
Willard-cache updates are threaded across homogeneous range segments and all
ordered roots.
-/
def performBorrowAccessRange (tree : BorrowTree)
    (provenance : Miri.Memory.ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : BorrowTreeAccessResult := Id.run do
  let source? := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  match provenance with
  | .concrete tag =>
      if source?.isNone then
        return { tree, locations := #[], status := .MissingTag tag }
  | .wildcard => pure ()
  let prepared := tree.locations.iterMut offset length
  let mut currentMap := prepared.state
  let mut currentTree := tree
  let mut visited : Array BorrowTreeLocationResult := #[]
  let mut status := BorrowTreeAccessStatus.Completed
  match prepared.outcome with
  | .error error => status := .RangeMapFailure error
  | .ok _ =>
      for cursor in [:prepared.positions.size] do
        if status == .Completed then
          match prepared.positions[cursor]?, prepared.segments[cursor]? with
          | some position, some segment =>
              let access := currentTree.performTreeAccessAt segment.data source? kind
                protectedTags mode segment.range
              let mutation := currentMap.setAtPos position access.location
              currentMap := mutation.state
              visited := visited.push ⟨segment.range, access.normalAccess⟩
              match mutation.outcome with
              | .error error => status := .LocationMapFailure segment.range error
              | .ok () =>
                  match access.status with
                  | some failure => status := failure
                  | none => pure ()
          | _, _ =>
              status := .RangeMapFailure
                (.indexOutOfBounds cursor prepared.positions.size)
  currentTree := { currentTree with locations := currentMap }
  return { tree := currentTree, locations := visited, status }

/-- Concrete-tag convenience wrapper over the full source-root access path. -/
def performNormalAccessRange (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (offset length : Size) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : BorrowTreeAccessResult :=
  tree.performBorrowAccessRange (.concrete tag) offset length kind protectedTags mode

inductive ProtectorReleaseStatus where
  | Released
  | MissingTag (tag : Miri.Memory.BorTag)
  | RangeMapFailure (error : DedupRangeMapError)
  | LocationMapFailure (error : DedupRangeMapError)
  | AccessFailure (range : ByteRange) (status : BorrowTreeAccessStatus)
  | ExposureUpdateFailure (error : TreeMutationError)
  deriving DecidableEq, Repr

structure ProtectorReleaseResult where
  tree : BorrowTree
  status : ProtectorReleaseStatus
  deriving DecidableEq, Repr

/-- Source Tree::perform_protector_end_access followed by
update_exposure_for_protector_release. The tag remains protected during its
implicit accessed-location read/write, and the caller removes the global
protector only after this operation succeeds.
-/
def releaseProtector (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (protectedTags : ProtectedTags) : ProtectorReleaseResult := Id.run do
  let some source := tree.indexOfTag tag
    | return { tree, status := .MissingTag tag }
  let mut currentTree := tree
  for position in [:tree.locations.entries.size] do
    match currentTree.locations.index position with
    | .error error =>
        return { tree := currentTree, status := .RangeMapFailure error }
    | .ok segment =>
        match segment.data.perms.get source with
        | none => pure ()
        | some state =>
            match state.permission.associatedAccess with
            | none => pure ()
            | some kind =>
                if state.accessed then
                  let access := currentTree.performTreeAccessAt segment.data (some source) kind
                    protectedTags .SkipChildrenOfAccessed segment.range
                  let mutation := currentTree.locations.setAtPos position access.location
                  currentTree := { currentTree with locations := mutation.state }
                  match mutation.outcome with
                  | .error error =>
                      return { tree := currentTree, status := .LocationMapFailure error }
                  | .ok () =>
                      match access.status with
                      | some status =>
                          return ⟨currentTree, .AccessFailure segment.range status⟩
                      | none => pure ()
  let exposure := currentTree.updateExposureForProtectorRelease tag
  match exposure.outcome with
  | .error error =>
      return { tree := exposure.tree, status := .ExposureUpdateFailure error }
  | .ok () => return { tree := exposure.tree, status := .Released }

/-- Source `Tree::dealloc` for a single concrete root: first perform the write
through the supplied tag, then inspect visited nodes in source tree-visitor
order for accessed strong protectors. Cell permissions are exempt. Weak
protectors are handled by the initial write transition itself.
-/
def deallocateBorrowRange (tree : BorrowTree)
    (provenance : Miri.Memory.ProvenanceExtra)
    (offset length : Size) (protectedTags : ProtectedTags) : BorrowTreeDeallocResult := Id.run do
  let accessed := tree.performBorrowAccessRange provenance offset length .Write protectedTags
    .VisitChildrenOfAccessed
  if accessed.status != .Completed then
    return { tree := accessed.tree, status := .AccessFailure accessed.status }
  -- `Tree::dealloc` checks the concrete provenance tag itself first. The
  -- normal access result's root is deliberately not used here: starting at
  -- the root changes the visitor's local-access prefix and protector error
  -- precedence when the provenance tag is an interior node.
  let startIndex? := match provenance with
    | .concrete tag => accessed.tree.indexOfTag tag
    | .wildcard => none
  if let .concrete tag := provenance then
    if startIndex?.isNone then
      return { tree := accessed.tree, status := .MissingTag tag }
  let prepared := accessed.tree.locations.iterMut offset length
  let mut currentMap := prepared.state
  match prepared.outcome with
  | .error error =>
      let updatedTree := { accessed.tree with locations := currentMap }
      return { tree := updatedTree, status := .RangeMapFailure error }
  | .ok () =>
      for cursor in [:prepared.positions.size] do
        match prepared.positions[cursor]?, prepared.segments[cursor]? with
        | some position, some segment =>
            let topology := traversalProjection accessed.tree
            let mut foundProtected : Option UniIndex := none
            let mut accessedRoot? : Option UniIndex := none
            -- The source visitor first traverses the concrete tag and its
            -- ancestors, then deferred descendants/cousins. Its returned
            -- root is the one excluded from the subsequent reverse-root pass.
            if let some startIndex := startIndex? then
              let traversal := Tree.TraversalTree.traverse topology startIndex.toNat
                .VisitChildrenOfAccessed []
              accessedRoot? := UniIndex.ofNat? traversal.1
              for event in traversal.2 do
                if foundProtected.isNone then
                  match UniIndex.ofNat? event.node with
                  | none => pure ()
                  | some index =>
                      match accessed.tree.nodeAt index with
                      | none => pure ()
                      | some node =>
                          let permission := segment.data.perms.get index
                            |>.getD node.defaultLocationState
                          if protectedTags.get node.tag == some .StrongProtector &&
                              !permission.permission.isCell && permission.accessed then
                            foundProtected := some index
            for root in accessed.tree.roots.reverse do
              if accessedRoot? != some root && foundProtected.isNone then
                let events := (Tree.TraversalTree.traverse topology root.toNat
                  .VisitChildrenOfAccessed []).2
                for event in events do
                  if foundProtected.isNone then
                    match UniIndex.ofNat? event.node with
                    | none => pure ()
                    | some index =>
                        match accessed.tree.nodeAt index with
                        | none => pure ()
                        | some node =>
                            let permission := segment.data.perms.get index
                              |>.getD node.defaultLocationState
                            if protectedTags.get node.tag == some .StrongProtector &&
                                !permission.permission.isCell && permission.accessed then
                              foundProtected := some index
            if let some index := foundProtected then
              let updatedTree := { accessed.tree with locations := currentMap }
              return ⟨updatedTree, .ProtectedDealloc segment.range index⟩
            match currentMap.index position with
            | .error error =>
                let updatedTree := { accessed.tree with locations := currentMap }
                return { tree := updatedTree, status := .RangeMapFailure error }
            | .ok _ => pure ()
        | _, _ =>
            let updatedTree := { accessed.tree with locations := currentMap }
            return ⟨updatedTree,
              .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)⟩
  let updatedTree := { accessed.tree with locations := currentMap }
  return { tree := updatedTree, status := .Deallocated }

/-- Concrete-tag convenience wrapper for source Tree::dealloc. -/
def deallocateRange (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (offset length : Size) (protectedTags : ProtectedTags) : BorrowTreeDeallocResult :=
  tree.deallocateBorrowRange (.concrete tag) offset length protectedTags

@[simp] theorem new_root_node (rootTag : Miri.Memory.BorTag) (size : Size) :
    (BorrowTree.new rootTag size).nodes.get ⟨0⟩ = some {
      tag := rootTag
      parent := none
      children := #[]
      defaultInitialPermission := .newDisabled
      defaultInitialSifa := .None
      isExposed := false
    } := by
  simp [BorrowTree.new, rootIndex, UniValMap.insert, UniValMap.extendTo,
    UniValMap.get, UniIndex.toNat]

@[simp] theorem new_root_is_only_tree_root (rootTag : Miri.Memory.BorTag)
    (size : Size) : (BorrowTree.new rootTag size).roots = #[⟨0⟩] := by
  rfl

theorem new_one_byte_root_is_accessed_unique :
    (((BorrowTree.new Miri.Memory.BorTag.one (Size.ofBytes 1)).locations.iterAll[0]?).map
      fun segment => segment.data.perms.get ⟨0⟩) = some (some ⟨.Unique, true, .None⟩) := by
  decide


end BorrowTree

end Miri.TreeBorrows
