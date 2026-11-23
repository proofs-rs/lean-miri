import Lean
import Init.Internal.Order.While
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

private structure WildcardVisit where
  location : LocationTree
  hasValidExposed : Bool
  status : WildcardAccessStatus
  stack : Array (UniIndex × Bool)

private def WildcardVisit.active (visit : WildcardVisit) : Bool :=
  !visit.stack.isEmpty && visit.status == .Completed

private inductive WildcardPrepared where
  | complete (visit : WildcardVisit)
  | permission (recorded : Tree.LocationState) (relatedness : AccessRelatedness)
      (held : Bool) (commit : Tree.LocationState.AccessResult → WildcardVisit)

private def commitWildcardPermission (tree : BorrowTree) (index : UniIndex)
    (node : TreeNode) (oldState : Tree.LocationState) (isProtected : Bool)
    (visit : WildcardVisit) (access : Tree.LocationState.AccessResult) : WildcardVisit := Id.run do
  let mut location := visit.location
  let mut status := visit.status
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
  return { visit with location, status }

private def prepareWildcardNode (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option Miri.Memory.BorTag) (kind : AccessKind) (protectedTags : ProtectedTags)
    (isWildcardTree : Bool) (visit : WildcardVisit) : WildcardPrepared := Id.run do
  let mut location := visit.location
  let mut hasValidExposed := visit.hasValidExposed
  let mut status := visit.status
  let mut stack := visit.stack
  let some (index, afterChildren) := stack.back?
    | status := .EmptyTraversalStack root
      return .complete ⟨location, hasValidExposed, status, stack⟩
  if !afterChildren then
    let some node := tree.nodes.get index
      | status := .MissingNode index
        return .complete ⟨location, hasValidExposed, status, stack⟩
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
        return .complete ⟨location, hasValidExposed, status, stack⟩
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
            -- Local workaround for https://github.com/rust-lang/miri/issues/5543.
            -- Child transitions can remove the last exposed descendant and
            -- change an entry-time Either access into a Foreign access.
            -- The complete foreign-Write no-op class is read-safe too.
            -- A current SIFA skip therefore leaves every state field
            -- unchanged, including the held-sensitive protected cases.
            -- Retain materialization and all child/cache/witness effects.
            if rel == .ForeignAccess && state.foreignWriteNoop isProtected &&
                state.skipIfKnownNoop kind rel == .SkipSelfAndChildren then
              pure ()
            else
              match state.recordNewAccess kind rel with
              | .DebugAssertion => status := .RecordDebugAssertion index
              | .Recorded recorded =>
                  location := { location with perms := location.perms.insert index recorded }
                  let current : WildcardVisit := ⟨location, hasValidExposed, status, stack⟩
                  return .permission recorded rel isProtected
                    (commitWildcardPermission tree index node oldState isProtected current)
  return .complete ⟨location, hasValidExposed, status, stack⟩

private def visitWildcardNode (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option Miri.Memory.BorTag) (kind : AccessKind) (protectedTags : ProtectedTags)
    (isWildcardTree : Bool) (visit : WildcardVisit) : WildcardVisit :=
  match prepareWildcardNode tree root maxLocalTag kind protectedTags isWildcardTree visit with
  | .complete next => next
  | .permission recorded related held commit => commit (recorded.performAccess kind related held)

private def wildcardScan (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option Miri.Memory.BorTag) (kind : AccessKind) (protectedTags : ProtectedTags)
    (isWildcardTree : Bool) (_ : Unit) (current : WildcardVisit × Nat) :
    Id (ForInStep (WildcardVisit × Nat)) :=
  if current.1.active then
    let steps := current.2 + 1
    if steps > tree.nodes.size * 2 + 1 then
      .yield ({ current.1 with status := .ParentCycle root }, steps)
    else
      .yield (visitWildcardNode tree root maxLocalTag kind protectedTags isWildcardTree current.1, steps)
  else .done current

private def finishWildcardVisit (root : UniIndex) (isWildcardTree : Bool)
    (visit : WildcardVisit) : WildcardLocationAccessResult :=
  ⟨visit.location, if visit.status == .Completed && !visit.hasValidExposed && !isWildcardTree then
    .NoValidExposedReferences root none else visit.status⟩

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
                -- Local workaround for https://github.com/rust-lang/miri/issues/5543.
                -- Child transitions can remove the last exposed descendant and
                -- change an entry-time Either access into a Foreign access.
                -- The complete foreign-Write no-op class is read-safe too.
                -- A current SIFA skip therefore leaves every state field
                -- unchanged, including the held-sensitive protected cases.
                -- Retain materialization and all child/cache/witness effects.
                if rel == .ForeignAccess && state.foreignWriteNoop isProtected &&
                    state.skipIfKnownNoop kind rel == .SkipSelfAndChildren then
                  pure ()
                else
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

private def commitNormalAccessAt (tree : BorrowTree) (location : LocationTree)
    (kind : AccessKind) (protectedTags : ProtectedTags)
    (access : Tree.NormalAccessResult) : NormalLocationAccessResult := Id.run do
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

private theorem performNormalAccessAt_eq_commit (tree : BorrowTree) (location : LocationTree)
    (start : UniIndex) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :
    tree.performNormalAccessAt location start kind protectedTags mode =
      commitNormalAccessAt tree location kind protectedTags
        ((normalProjection tree location protectedTags).performAccess start.toNat kind mode) := rfl

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

structure TreeLocationAccessAtResult where
  location : LocationTree
  normalAccess : Option Tree.NormalAccessResult
  status : Option BorrowTreeAccessStatus

private structure OtherRootProgress where
  location : LocationTree
  status : Option BorrowTreeAccessStatus := none
  stopped : Bool := false

private inductive OtherRootAction where
  | skip
  | stop
  | visit (root : UniIndex)

private def otherRootAction (tree : BorrowTree) (accessedRoot : Option UniIndex)
    (mode : Tree.ChildrenVisitMode) (minExposed : Option Miri.Memory.BorTag)
    (position : Nat) (current : OtherRootProgress) : OtherRootAction :=
  if current.status.isNone && !current.stopped then
    match tree.roots[position]? with
    | none => .skip
    | some root =>
      let rootTag := (tree.nodes.get root).map TreeNode.tag
      let pastMinExposed := match rootTag, minExposed with
        | some tag, some minimum => tag.value > minimum.value
        | _, _ => false
      if mode == .SkipChildrenOfAccessed && pastMinExposed then .stop
      else if accessedRoot != some root then .visit root
      else .skip
  else .skip

private def commitOtherRoot (current : OtherRootProgress) (range : ByteRange)
    (wildcard : WildcardLocationAccessResult) : OtherRootProgress :=
  { current with
    location := wildcard.location
    status := if wildcard.status != .Completed then some (.WildcardFailure range wildcard.status)
      else current.status }

private def advanceOtherRoot (tree : BorrowTree) (accessedRoot : Option UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (minExposed maxLocalTag : Option Miri.Memory.BorTag) (position : Nat)
    (current : OtherRootProgress) : OtherRootProgress :=
  match otherRootAction tree accessedRoot mode minExposed position current with
  | .skip => current
  | .stop => { current with stopped := true }
  | .visit root =>
    commitOtherRoot current range
      (tree.performWildcardAccessAt current.location root maxLocalTag kind tags (position != 0))

private def otherRootBounds (tree : BorrowTree) (source accessedRoot : Option UniIndex)
    (mode : Tree.ChildrenVisitMode) : Option Miri.Memory.BorTag × Option Miri.Memory.BorTag :=
  let minExposed := if mode == .SkipChildrenOfAccessed then source.bind (minExposedChild tree)
    else none
  let maxLocalTag := accessedRoot.bind fun root => (tree.nodes.get root).map TreeNode.tag
  (minExposed, maxLocalTag)

private def performOtherRootsAt (tree : BorrowTree) (location : LocationTree)
    (source accessedRoot : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (normalAccess : Option Tree.NormalAccessResult) : TreeLocationAccessAtResult := Id.run do
  let (minExposed, maxLocalTag) := otherRootBounds tree source accessedRoot mode
  let final ← forIn [:tree.roots.size] ({ location } : OtherRootProgress) fun position current =>
    pure (.yield (advanceOtherRoot tree accessedRoot kind tags mode range minExposed maxLocalTag
      position current))
  return ⟨final.location, normalAccess, final.status⟩

/-- Apply the source LocationTree::perform_access order: first the concrete
source tree, then each other root as a wildcard subtree. None provenance
starts with wildcard accesses on all roots.
-/
def performTreeAccessAt (tree : BorrowTree) (location : LocationTree)
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

private def replayOtherRootsAt (tree : BorrowTree) (location : LocationTree)
    (source? accessedRoot? : Option UniIndex) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (normalAccess : Option Tree.NormalAccessResult) : TreeLocationAccessAtResult := Id.run do
  let mut currentLocation := location
  let mut status : Option BorrowTreeAccessStatus := none
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

private abbrev OtherRootLoopState := LocationTree × Option BorrowTreeAccessStatus × Bool

private def otherRootLoopState (current : OtherRootProgress) : OtherRootLoopState :=
  (current.location, current.status, current.stopped)

private theorem otherRootLoopTransport (scan : Nat → OtherRootLoopState → Id (ForInStep OtherRootLoopState))
    (advance : Nat → OtherRootProgress → OtherRootProgress)
    (transition : ∀ position current, scan position (otherRootLoopState current) =
      .yield (otherRootLoopState (advance position current)))
    (positions : List Nat) (current : OtherRootProgress) :
    Id.run (forIn positions (otherRootLoopState current) scan) =
      otherRootLoopState (Id.run (forIn positions current
        (fun position state => pure (.yield (advance position state))))) := by
  induction positions generalizing current with
  | nil => rfl
  | cons position positions ih =>
    simpa only [List.forIn_cons, transition, bind, Bind.bind, pure, Pure.pure] using
      ih (advance position current)

open Lean Elab Tactic in
elab "name_other_root_loop" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn.forIn)
      | throwError "no ForIn operation found"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan, goal) ← goal.intro1P
    let target ← goal.getType
    return [← goal.change (target.replace fun expr =>
      if expr == body then some (mkFVar scan) else none)]

private theorem otherRootsRuntime_eq (tree : BorrowTree) (location : LocationTree)
    (source accessedRoot : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange) (normal : Option Tree.NormalAccessResult) :
    replayOtherRootsAt tree location source accessedRoot kind tags mode range normal =
      performOtherRootsAt tree location source accessedRoot kind tags mode range normal := by
  unfold replayOtherRootsAt performOtherRootsAt
  dsimp only [Id.run, otherRootBounds]
  name_other_root_loop
  let minExposed := if mode == .SkipChildrenOfAccessed then source.bind (minExposedChild tree) else none
  let maxLocalTag := accessedRoot.bind fun root => (tree.nodes.get root).map TreeNode.tag
  let advance := advanceOtherRoot tree accessedRoot kind tags mode range minExposed maxLocalTag
  have transition (position : Nat) (current : OtherRootProgress) :
      scan position (otherRootLoopState current) =
        .yield (otherRootLoopState (advance position current)) := by
    rcases current with ⟨currentLocation, status, stopped⟩
    simp only [scan, otherRootLoopState, advance, advanceOtherRoot, otherRootAction, minExposed, maxLocalTag]
    by_cases active : (status.isNone && !stopped) = true
    · simp only [active, ↓reduceIte]
      cases rootAt : tree.roots[position]? with
      | none => rfl
      | some root =>
        dsimp only
        by_cases stop : (mode == .SkipChildrenOfAccessed &&
            (match (tree.nodes.get root).map TreeNode.tag, minExposed with
             | some tag, some minimum => tag.value > minimum.value
             | _, _ => false)) = true
        · simp only [minExposed] at stop
          simp only [stop, ↓reduceIte]; rfl
        · simp only [minExposed] at stop
          simp only [stop, Bool.false_eq_true, ↓reduceIte]
          by_cases visit : (accessedRoot != some root) = true
          · simp only [visit, ↓reduceIte, commitOtherRoot]
            by_cases failed : ((tree.performWildcardAccessAt currentLocation root maxLocalTag
                kind tags (position != 0)).status != .Completed) = true
            · simp only [maxLocalTag] at failed
              simp only [failed, ↓reduceIte]; rfl
            · simp only [maxLocalTag] at failed
              simp only [failed, Bool.false_eq_true, ↓reduceIte]; rfl
          · simp only [visit, Bool.false_eq_true, ↓reduceIte]; rfl
    · simp [active, pure, Pure.pure]
  have transport := otherRootLoopTransport scan advance transition
    (List.range' 0 tree.roots.size) { location }
  change _ = _ at transport
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [show otherRootLoopState ({ location } : OtherRootProgress) = (location, none, false) from rfl] at transport
  dsimp only [Id.run] at transport
  rw [transport]
  rfl

private theorem locationRuntime_eq (tree : BorrowTree) (location : LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange) :
    tree.performTreeAccessAt location source kind tags mode range =
      match source with
      | none => performOtherRootsAt tree location none none kind tags mode range none
      | some index =>
        let normal := tree.performNormalAccessAt location index kind tags mode
        let seen := some normal.access
        match normal.outcome with
        | .error error => ⟨normal.location, seen, some (.CacheFailure range error)⟩
        | .ok () =>
          if normal.access.status != .Completed then
            ⟨normal.location, seen, some (.AccessFailure range normal.access.status)⟩
          else match UniIndex.ofNat? normal.access.root with
            | none => ⟨normal.location, seen,
                some (.AccessFailure range (.MissingLocationState normal.access.root))⟩
            | some root =>
              performOtherRootsAt tree normal.location source (some root) kind tags mode range seen := by
  cases source with
  | none => exact otherRootsRuntime_eq tree location none none kind tags mode range none
  | some index =>
    unfold performTreeAccessAt
    dsimp only [Id.run]
    generalize tree.performNormalAccessAt location index kind tags mode = normal
    cases outcome : normal.outcome with
    | error error => rfl
    | ok value =>
      cases value
      by_cases failed : (normal.access.status != .Completed) = true
      · simp only [failed, ↓reduceIte]; rfl
      · simp only [failed, Bool.false_eq_true, ↓reduceIte]
        cases UniIndex.ofNat? normal.access.root with
        | none => rfl
        | some root =>
          exact otherRootsRuntime_eq tree normal.location (some index) (some root)
            kind tags mode range (some normal.access)

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

private def strongProtectorAt (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (event : Tree.TraversalEvent) : Option UniIndex := do
  let index ← UniIndex.ofNat? event.node
  let node ← tree.nodeAt index
  let state := location.perms.get index |>.getD node.defaultLocationState
  if tags.get node.tag == some .StrongProtector && !state.permission.isCell && state.accessed then
    some index
  else none

private def findStrongProtectorInOtherRoots (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (topology : Tree.TraversalTree)
    (accessedRoot : Option UniIndex) : Option UniIndex :=
  tree.roots.reverse.toList.findSome? fun root =>
    if accessedRoot == some root then none
    else
      let events := (topology.traverse root.toNat .VisitChildrenOfAccessed []).2
      events.findSome? (strongProtectorAt tree location tags)

/-- Source visitor order for the terminal protector check. A concrete tag is
visited before its ancestors, then the remaining roots are checked in reverse
root order. The selected root is omitted from that second pass. -/
private def firstStrongProtector (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (start : Option UniIndex) : Option UniIndex :=
  let topology := traversalProjection tree
  match start with
  | none => findStrongProtectorInOtherRoots tree location tags topology none
  | some index =>
    let (root, events) := topology.traverse index.toNat .VisitChildrenOfAccessed []
    match events.findSome? (strongProtectorAt tree location tags) with
    | some protectedIndex => some protectedIndex
    | none => findStrongProtectorInOtherRoots tree location tags topology (UniIndex.ofNat? root)

private def deallocationCursor (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (tags : ProtectedTags) (start : Option UniIndex) (cursor : Nat) : Option BorrowTreeDeallocStatus :=
  match prepared.positions[cursor]?, prepared.segments[cursor]? with
  | some position, some segment =>
    match firstStrongProtector tree segment.data tags start with
    | some index => some (.ProtectedDealloc segment.range index)
    | none =>
      match prepared.state.index position with
      | .error error => some (.RangeMapFailure error)
      | .ok _ => none
  | _, _ => some (.RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size))

/-- The source strong-protector scan following the deallocation write. It
uses the tree committed by the write, including on failure. -/
def deallocateAfterWrite (accessed : BorrowTreeAccessResult)
    (provenance : Miri.Memory.ProvenanceExtra)
    (offset length : Size) (protectedTags : ProtectedTags) : BorrowTreeDeallocResult := Id.run do
  if accessed.status != .Completed then
    return { tree := accessed.tree, status := .AccessFailure accessed.status }
  let start := match provenance with
    | .concrete tag => accessed.tree.indexOfTag tag
    | .wildcard => none
  if let .concrete tag := provenance then
    if start.isNone then
      return { tree := accessed.tree, status := .MissingTag tag }
  let prepared := accessed.tree.locations.iterMut offset length
  let updatedTree := { accessed.tree with locations := prepared.state }
  match prepared.outcome with
  | .error error => return ⟨updatedTree, .RangeMapFailure error⟩
  | .ok () =>
    let failure := (List.range' 0 prepared.positions.size).findSome?
      (deallocationCursor accessed.tree prepared protectedTags start)
    return ⟨updatedTree, failure.getD .Deallocated⟩

/-- Source `Tree::dealloc`: first perform the write through the supplied
provenance, then inspect the resulting locations for accessed strong protectors.
Cell permissions are exempt. The initial write handles weak protectors. -/
def deallocateBorrowRange (tree : BorrowTree) (provenance : Miri.Memory.ProvenanceExtra)
    (offset length : Size) (protectedTags : ProtectedTags) : BorrowTreeDeallocResult :=
  deallocateAfterWrite (tree.performBorrowAccessRange provenance offset length .Write protectedTags
    .VisitChildrenOfAccessed) provenance offset length protectedTags

theorem deallocateBorrowRange_eq (tree : BorrowTree) (provenance : Miri.Memory.ProvenanceExtra)
    (offset length : Size) (protectedTags : ProtectedTags) :
    tree.deallocateBorrowRange provenance offset length protectedTags =
      deallocateAfterWrite (tree.performBorrowAccessRange provenance offset length .Write protectedTags
        .VisitChildrenOfAccessed) provenance offset length protectedTags := rfl

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


/-! Zero-byte protected child construction from finite graph and allocator
invariants. These proof-only declarations do not change the interpreter.
The rank and loop lemmas are adapted from PR35/38 generic Tree Borrows proofs. -/

namespace ZeroProtection
open Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
open Lean Elab Tactic in
elab "name_ancestor_loop" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``Lean.Loop.forIn)
      | throwError "no Loop.forIn found"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan, goal) ← goal.intro1P
    let target ← goal.getType
    let target := target.replace fun expr =>
      if expr == body then some (mkFVar scan) else none
    return [← goal.change target]
/-- A source while-loop invariant with a well-founded data measure. -/
theorem loop_invariant {β : Type} (scan : Unit → β → Id (ForInStep β))
    (measure : β → Nat) (property : β → Prop)
    (step : ∀ state, property state →
      (∃ final, scan () state = .done final ∧ property final) ∨
      ∃ next, scan () state = .yield next ∧ property next ∧ measure next < measure state)
    (initial : β) (valid : property initial) :
    property (Lean.Loop.forIn {} initial scan) := by
  have sound : ∀ bound state, measure state = bound → property state →
      property (Lean.Loop.forIn {} state scan) := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro state measured valid
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rcases step state valid with done | more
      · obtain ⟨final,actual,preserved⟩ := done
        simpa only [actual,bind,pure] using preserved
      · obtain ⟨next,actual,preserved,smaller⟩ := more
        simp only [actual,bind]
        exact ih (measure next) (by omega) next rfl preserved
  exact sound (measure initial) initial rfl valid
structure ParentDepth (nodes : UniValMap TreeNode) where
  depth : UniIndex → Nat
  bounded : ∀ index node, nodes.get index = some node → depth index ≤ nodes.size
  parent : ∀ index node, nodes.get index = some node → ∀ before, node.parent = some before →
    ∃ earlier, nodes.get before = some earlier ∧ depth before < depth index
theorem index_injective (left right : UniIndex) (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      exact congrArg UniIndex.mk (UInt32.toNat_inj.mp same)

theorem lookup_valid {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (present : nodes.get index = some value) : index.toNat < nodes.data.size := by
  unfold UniValMap.get at present
  cases source : nodes.data[index.toNat]? with
  | none => simp [source] at present
  | some old => exact (Array.getElem?_eq_some_iff.mp source).1

theorem insert_existing {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) :
    (nodes.insert index next).data = nodes.data.set index.toNat (some next) (lookup_valid nodes index old present) := by
  have valid := lookup_valid nodes index old present
  have noExtra : index.toNat + 1 - nodes.data.size = 0 := by omega
  simp [UniValMap.insert,UniValMap.extendTo,noExtra,valid,Id.run,pure]

theorem insert_existing_get_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) : (nodes.insert index next).get index = some next := by
  unfold UniValMap.get
  rw [insert_existing nodes index old next present]
  simp

theorem insert_existing_get_other {α : Type} (nodes : UniValMap α) (index query : UniIndex) (old next : α)
    (present : nodes.get index = some old) (different : query ≠ index) :
    (nodes.insert index next).get query = nodes.get query := by
  have differentNat : query.toNat ≠ index.toNat := fun same => different (index_injective query index same)
  unfold UniValMap.get
  rw [insert_existing nodes index old next present]
  simp [Ne.symm differentNat]

theorem insert_existing_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) : (nodes.insert index next).size = nodes.size := by
  unfold UniValMap.size
  rw [insert_existing nodes index old next present]
  simp

/-- Changing non-parent node metadata preserves the real exposed-cache
ancestor certificate and its depth function. -/
def update_depth (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex)
    (old next : TreeNode) (present : nodes.get index = some old) (sameParent : next.parent = old.parent) :
    ParentDepth (nodes.insert index next) where
  depth := depth.depth
  bounded := by
    intro query node lookup
    rw [insert_existing_size nodes index old next present]
    by_cases same : query = index
    · subst query
      rw [insert_existing_get_same nodes index old next present] at lookup
      cases lookup
      exact depth.bounded index old present
    · rw [insert_existing_get_other nodes index query old next present same] at lookup
      exact depth.bounded query node lookup
  parent := by
    intro query node lookup before parentEq
    have original : ∃ original, nodes.get query = some original ∧ original.parent = node.parent := by
      by_cases same : query = index
      · subst query
        rw [insert_existing_get_same nodes index old next present] at lookup
        cases lookup
        exact ⟨old,present,sameParent.symm⟩
      · rw [insert_existing_get_other nodes index query old next present same] at lookup
        exact ⟨node,lookup,rfl⟩
    obtain ⟨original,originalLookup,parentSame⟩ := original
    obtain ⟨ancestor,ancestorLookup,smaller⟩ := depth.parent query original originalLookup before (parentSame.trans parentEq)
    by_cases same : before = index
    · subst before
      exact ⟨next,insert_existing_get_same nodes index old next present,smaller⟩
    · exact ⟨ancestor,(insert_existing_get_other nodes index before old next present same).trans ancestorLookup,smaller⟩
abbrev LoopState := Option (BorrowTree × Except BorrowTree.ChildInsertError Unit) × BorrowTree × Option UniIndex × Nat × Bool

def weakened (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (strongest : IdempotentForeignAccess) : BorrowTree :=
  {tree with
    locations := (tree.locations.modifyAll fun _ location =>
      match location.perms.get index with
      | none => location
      | some state => {location with perms := location.perms.insert index ({state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1})})
    nodes := tree.nodes.insert index
      ({node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1})}

def changed (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (strongest : IdempotentForeignAccess) : Bool := Id.run do
  let mut result := (node.defaultInitialSifa.ensureNoStrongerThan strongest).2
  for segment in tree.locations.iterAll do
    if let some state := segment.data.perms.get index then
      result := result || (state.idempotentForeignAccess.ensureNoStrongerThan strongest).2
  return result

def Good (depth : UniIndex → Nat) (state : LoopState) : Prop :=
  state.1 = none ∧ ∃ certificate : ParentDepth state.2.1.nodes,
    certificate.depth = depth ∧ state.2.2.2.1 ≤ state.2.1.nodes.size ∧
      (state.2.2.2.2 = true → ∀ index, state.2.2.1 = some index → ∃ node,
        state.2.1.nodes.get index = some node ∧ state.2.2.2.1 + depth index < state.2.1.nodes.size)

def Measure (depth : UniIndex → Nat) (state : LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.2.1.map (fun index => depth index + 2)).getD 1 else 0

theorem succeeds (tree : BorrowTree) (depth : ParentDepth tree.nodes) (start : UniIndex)
    (node : TreeNode) (present : tree.nodes.get start = some node)
    (strict : depth.depth start < tree.nodes.size) (strongest : IdempotentForeignAccess) :
    (updateSifaAfterRetag tree start strongest).2 = .ok () := by
  unfold updateSifaAfterRetag
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_ancestor_loop
    have step : ∀ state, Good depth.depth state →
        (∃ final, scan () state = .done final ∧ Good depth.depth final) ∨
        ∃ next, scan () state = .yield next ∧ Good depth.depth next ∧ Measure depth.depth next < Measure depth.depth state := by
      intro state good
      rcases state with ⟨returned,current,cursor,steps,active⟩
      rcases good with ⟨returnedEq,certificate,depthEq,stepsBound,live⟩
      dsimp only at returnedEq stepsBound
      subst returned
      cases active with
      | false => exact .inl ⟨_,rfl,⟨rfl,certificate,depthEq,stepsBound,by simp⟩⟩
      | true =>
        have notPast : ¬ steps > current.nodes.size := by omega
        cases cursor with
        | none =>
          refine .inr ⟨(none,current,none,steps,false),?_,⟨rfl,certificate,depthEq,stepsBound,by simp⟩,?_⟩
          · simp [scan,notPast]
          · simp [Measure]
        | some index =>
          obtain ⟨currentNode,lookup,strictBound⟩ := live rfl index rfl
          dsimp only at strictBound
          let nextNode := {currentNode with defaultInitialSifa := (currentNode.defaultInitialSifa.ensureNoStrongerThan strongest).1}
          let nextTree := weakened current index currentNode strongest
          let nextCertificate := update_depth current.nodes certificate index currentNode nextNode lookup rfl
          have nextDepth : nextCertificate.depth = depth.depth := depthEq
          have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index currentNode nextNode lookup
          have parentPresent : ∀ before, currentNode.parent = some before → ∃ earlier,
              nextTree.nodes.get before = some earlier ∧ depth.depth before < depth.depth index := by
            intro before edge
            obtain ⟨earlier,earlierLookup,smaller⟩ := nextCertificate.parent index nextNode
              (insert_existing_get_same current.nodes index currentNode nextNode lookup) before edge
            rw [nextDepth] at smaller
            exact ⟨earlier,earlierLookup,smaller⟩
          cases actualChanged : changed current index currentNode strongest with
          | false =>
            have actual : scan () (none,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup]
              change (if changed current index currentNode strongest then _ else _) = _
              rw [actualChanged]
              rfl
            refine .inr ⟨_,actual,⟨rfl,nextCertificate,nextDepth,?_,by simp⟩,?_⟩
            · rw [sameSize]; exact stepsBound
            · simp [Measure]
          | true =>
            have actual : scan () (none,current,some index,steps,true) = .yield (none,nextTree,currentNode.parent,steps+1,true) := by
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup]
              change (if changed current index currentNode strongest then _ else _) = _
              rw [actualChanged]
              rfl
            refine .inr ⟨_,actual,⟨rfl,nextCertificate,nextDepth,?_,?_⟩,?_⟩
            · dsimp only; rw [sameSize]; omega
            · intro active before edge
              obtain ⟨earlier,earlierLookup,smaller⟩ := parentPresent before edge
              exact ⟨earlier,earlierLookup,by dsimp; rw [sameSize]; omega⟩
            · cases parentEq : currentNode.parent with
              | none => simp [Measure]
              | some before =>
                have smaller := (parentPresent before parentEq).choose_spec.2
                simp only [Measure,↓reduceIte,Option.map_some,Option.getD_some]
                omega
    have initial : Good depth.depth (none,tree,some start,0,true) := by
      refine ⟨rfl,depth,rfl,by simp,?_⟩
      intro active index same
      have indexEq : index = start := Option.some.inj same.symm
      subst index
      exact ⟨node,present,by simpa using strict⟩
    have maintained := loop_invariant scan (Measure depth.depth) (Good depth.depth) step _ initial
    rw [maintained.1]

namespace Append
/-- The append-index branch of the actual newChild node insertion. Existing
node data and parent depth are arbitrary; free-index reuse is a separate case. -/
theorem insert_append {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) :
 (nodes.insert index value).data = nodes.data.push (some value) := by
 simp [UniValMap.insert,UniValMap.extendTo,atEnd,Id.run,pure,Array.set_push]
theorem append_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) : (nodes.insert index value).size = nodes.size+1 := by
 unfold UniValMap.size
 rw [insert_append nodes index value atEnd]
 simp
theorem append_get_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) : (nodes.insert index value).get index = some value := by
 unfold UniValMap.get
 rw [insert_append nodes index value atEnd]
 simp [atEnd]
theorem append_get_other {α : Type} (nodes : UniValMap α) (index query : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) (different : query ≠ index) :
 (nodes.insert index value).get query = nodes.get query := by
 have notEnd : query.toNat ≠ nodes.data.size := fun same => different (index_injective query index (same.trans atEnd.symm))
 unfold UniValMap.get
 rw [insert_append nodes index value atEnd]
 by_cases valid : query.toNat < nodes.data.size
 · simp [Array.getElem?_push,valid,notEnd]
 · simp [Array.getElem?_push,valid,notEnd]
def append_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
 (index parent : UniIndex) (parentNode newNode : TreeNode)
 (atEnd : index.toNat = nodes.data.size)
 (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent) :
 ParentDepth (nodes.insert index newNode) where
 depth := fun query => if query = index then before.depth parent + 1 else before.depth query
 bounded := by
   intro query node lookup
   rw [append_size nodes index newNode atEnd]
   by_cases same : query = index
   · subst query
     simp only [ite_true]
     have bound := before.bounded parent parentNode parentPresent
     omega
   · simp only [same,ite_false]
     rw [append_get_other nodes index query newNode atEnd same] at lookup
     have bound := before.bounded query node lookup
     omega
 parent := by
   intro query node lookup earlier edge
   have parentNotNew : parent ≠ index := by
     intro same
     have bound := lookup_valid nodes parent parentNode parentPresent
     rw [same,atEnd] at bound
     omega
   by_cases same : query = index
   · subst query
     rw [append_get_same nodes index newNode atEnd] at lookup
     cases lookup
     have earlierEq : earlier = parent := Option.some.inj (edge.symm.trans childParent)
     subst earlier
     refine ⟨parentNode,(append_get_other nodes index parent newNode atEnd parentNotNew).trans parentPresent,?_⟩
     simp only [parentNotNew,ite_false,ite_true]
     omega
   · rw [append_get_other nodes index query newNode atEnd same] at lookup
     obtain ⟨ancestor,present,smaller⟩ := before.parent query node lookup earlier edge
     have earlierNotNew : earlier ≠ index := by
       intro equal
       have bound := lookup_valid nodes earlier ancestor present
       rw [equal,atEnd] at bound
       omega
     refine ⟨ancestor,(append_get_other nodes index earlier newNode atEnd earlierNotNew).trans present,?_⟩
     simpa only [earlierNotNew,same,ite_false] using smaller


/-- The second source-ordered node insertion in newChild attaches the new
index to its parent's children, without changing either node's parent link. -/
def attachedNodes (nodes : UniValMap TreeNode) (index parent : UniIndex)
    (parentNode newNode : TreeNode) : UniValMap TreeNode :=
  (nodes.insert index newNode).insert parent {parentNode with children := parentNode.children.push index}

theorem parent_not_fresh (nodes : UniValMap TreeNode) (index parent : UniIndex) (parentNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode) : parent ≠ index := by
  intro same
  have valid := lookup_valid nodes parent parentNode parentPresent
  rw [same,atEnd] at valid
  omega

def attached_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) : ParentDepth (attachedNodes nodes index parent parentNode newNode) :=
  update_depth (nodes.insert index newNode)
    (append_depth nodes before index parent parentNode newNode atEnd parentPresent childParent)
    parent parentNode {parentNode with children := parentNode.children.push index}
    ((append_get_other nodes index parent newNode atEnd (parent_not_fresh nodes index parent parentNode atEnd parentPresent)).trans parentPresent) rfl

theorem attached_parent_strict (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) :
    (attached_depth nodes before index parent parentNode newNode atEnd parentPresent childParent).depth parent <
      (attachedNodes nodes index parent parentNode newNode).size := by
  have different := parent_not_fresh nodes index parent parentNode atEnd parentPresent
  have lookup := (append_get_other nodes index parent newNode atEnd different).trans parentPresent
  change (if parent = index then before.depth parent+1 else before.depth parent) < _
  simp only [different,ite_false]
  unfold attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ lookup,
    append_size nodes index newNode atEnd]
  have bound := before.bounded parent parentNode parentPresent
  omega

/-- The real ancestor-SIFA stage invoked by newChild succeeds after its two
actual node insertions. The new index and original parent's presence are data
conditions; no successful child insertion or SIFA update is a premise. -/
theorem sifa_after_attach (tree : BorrowTree) (before : ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) (strongest : IdempotentForeignAccess) :
    (updateSifaAfterRetag
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} parent strongest).2 = .ok () := by
  let nodes := tree.nodes.insert index newNode
  let updatedParent := {parentNode with children := parentNode.children.push index}
  have lookup : nodes.get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  let current : BorrowTree := {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
  let certificate : ParentDepth current.nodes := by
    dsimp only [current]
    exact attached_depth tree.nodes before index parent parentNode newNode atEnd parentPresent childParent
  have present : current.nodes.get parent = some updatedParent := by
    dsimp only [current,attachedNodes,updatedParent]
    exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode
      {parentNode with children := parentNode.children.push index} lookup
  have strict : certificate.depth parent < current.nodes.size := by
    dsimp only [certificate,current]
    exact attached_parent_strict tree.nodes before index parent parentNode newNode atEnd parentPresent childParent
  change (updateSifaAfterRetag current parent strongest).2 = .ok ()
  exact ZeroProtection.succeeds current certificate parent updatedParent present strict strongest

end Append

namespace Sparse
/-- Extending a sparse location map with absent entries preserves every lookup,
including queries beyond both its old and new extents. -/
theorem extend_get {α : Type} (map : UniValMap α) (length : Nat) (index : UniIndex) :
    (⟨UniValMap.extendTo map.data length⟩ : UniValMap α).get index = map.get index := by
  unfold UniValMap.get UniValMap.extendTo
  rw [Array.getElem?_append]
  by_cases valid : index.toNat < map.data.size
  · simp only [valid,↓reduceIte]
  · have absent : map.data[index.toNat]? = none := Array.getElem?_eq_none (by omega)
    simp only [valid,↓reduceIte,absent,Array.getElem?_replicate]
    by_cases inside : index.toNat-map.data.size < length-map.data.size <;> simp only [inside,↓reduceIte]

private theorem extended_bound {α : Type} (map : UniValMap α) (index : UniIndex) :
    index.toNat < (UniValMap.extendTo map.data (index.toNat+1)).size := by
  simp only [UniValMap.extendTo,Array.size_append,Array.size_replicate]
  omega

private theorem inserted_data {α : Type} (map : UniValMap α) (index : UniIndex) (value : α) :
    (map.insert index value).data =
      (UniValMap.extendTo map.data (index.toNat+1)).set index.toNat (some value) (extended_bound map index) := by
  simp only [UniValMap.insert,extended_bound map index,↓reduceDIte,Id.run,pure]

/-- The actual sparse-map insertion stores the new child's materialized state. -/
theorem get_same {α : Type} (map : UniValMap α) (index : UniIndex) (value : α) :
    (map.insert index value).get index = some value := by
  unfold UniValMap.get
  rw [inserted_data]
  simp

/-- Inserting the new child state preserves every other node's state even
when the per-location sparse array has a different length from the node table. -/
theorem get_other {α : Type} (map : UniValMap α) (index query : UniIndex) (value : α) (different : query ≠ index) :
    (map.insert index value).get query = map.get query := by
  have differentNat : query.toNat ≠ index.toNat := fun equal => different (index_injective query index equal)
  unfold UniValMap.get
  rw [inserted_data]
  simp only [Array.getElem?_set,Ne.symm differentNat,↓reduceIte]
  exact extend_get map (index.toNat+1) query


end Sparse

namespace Reuse
/-- Insertion at a bounded sparse slot retains the table length. Vacancy is a
separate caller condition: this operation itself also permits overwriting. -/
theorem insert_bounded {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (valid : index.toNat < nodes.data.size) :
    (nodes.insert index value).data = nodes.data.set index.toNat (some value) valid := by
  have noExtra : index.toNat+1-nodes.data.size = 0 := by omega
  simp [UniValMap.insert,UniValMap.extendTo,noExtra,valid,Id.run,pure]

theorem bounded_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (valid : index.toNat < nodes.data.size) : (nodes.insert index value).size = nodes.size := by
  unfold UniValMap.size
  rw [insert_bounded nodes index value valid]
  simp

theorem parent_not_vacant (nodes : UniValMap TreeNode) (index parent : UniIndex) (parentNode : TreeNode)
    (vacant : nodes.get index = none) (parentPresent : nodes.get parent = some parentNode) : parent ≠ index := by
  intro same
  rw [same,vacant] at parentPresent
  cases parentPresent

/-- A bounded vacant slot can hold a fresh child. The explicit rank slack
ensures the child's parent-rank-plus-one fits without enlarging the table.
Every old parent edge remains valid; none can point to the vacant slot. -/
def vacant_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) : ParentDepth (nodes.insert index newNode) where
  depth := fun query => if query = index then before.depth parent+1 else before.depth query
  bounded := by
    intro query node lookup
    rw [bounded_size nodes index newNode valid]
    by_cases same : query = index
    · subst query
      simp only [ite_true]
      omega
    · simp only [same,ite_false]
      rw [Sparse.get_other nodes index query newNode same] at lookup
      exact before.bounded query node lookup
  parent := by
    intro query node lookup earlier edge
    have parentNotNew := parent_not_vacant nodes index parent parentNode vacant parentPresent
    by_cases same : query = index
    · subst query
      rw [Sparse.get_same] at lookup
      cases lookup
      have earlierEq : earlier = parent := Option.some.inj (edge.symm.trans childParent)
      subst earlier
      refine ⟨parentNode,(Sparse.get_other nodes index parent newNode parentNotNew).trans parentPresent,?_⟩
      simp only [parentNotNew,ite_false,ite_true]
      omega
    · rw [Sparse.get_other nodes index query newNode same] at lookup
      obtain ⟨ancestor,present,smaller⟩ := before.parent query node lookup earlier edge
      have earlierNotNew : earlier ≠ index := by
        intro equal
        rw [equal,vacant] at present
        cases present
      refine ⟨ancestor,(Sparse.get_other nodes index earlier newNode earlierNotNew).trans present,?_⟩
      simpa only [earlierNotNew,same,ite_false] using smaller

/-- Both source node insertions preserve the depth certificate on a reusable
slot. No absence of per-location permissions is inferred from node vacancy. -/
def attached_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) :
    ParentDepth (Append.attachedNodes nodes index parent parentNode newNode) :=
  update_depth (nodes.insert index newNode)
    (vacant_depth nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack)
    parent parentNode {parentNode with children := parentNode.children.push index}
    ((Sparse.get_other nodes index parent newNode
      (parent_not_vacant nodes index parent parentNode vacant parentPresent)).trans parentPresent) rfl

theorem attached_parent_strict (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) :
    (attached_depth nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack).depth parent <
      (Append.attachedNodes nodes index parent parentNode newNode).size := by
  have different := parent_not_vacant nodes index parent parentNode vacant parentPresent
  have lookup := (Sparse.get_other nodes index parent newNode different).trans parentPresent
  change (if parent = index then before.depth parent+1 else before.depth parent) < _
  simp only [different,ite_false]
  unfold Append.attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ lookup,bounded_size nodes index newNode valid]
  exact parentSlack

theorem sifa_after_attach (tree : BorrowTree) (before : ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < tree.nodes.size) (strongest : IdempotentForeignAccess) :
    (updateSifaAfterRetag {tree with nodes := Append.attachedNodes tree.nodes index parent parentNode newNode}
      parent strongest).2 = .ok () := by
  let current : BorrowTree := {tree with nodes := Append.attachedNodes tree.nodes index parent parentNode newNode}
  let updatedParent := {parentNode with children := parentNode.children.push index}
  let certificate : ParentDepth current.nodes := by
    dsimp only [current]
    exact attached_depth tree.nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack
  have lookup := (Sparse.get_other tree.nodes index parent newNode
    (parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  have present : current.nodes.get parent = some updatedParent := by
    dsimp only [current,Append.attachedNodes,updatedParent]
    exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ lookup
  have strict : certificate.depth parent < current.nodes.size := by
    dsimp only [certificate,current]
    exact attached_parent_strict tree.nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack
  exact ZeroProtection.succeeds current certificate parent updatedParent present strict strongest

end Reuse

/-- Both concrete allocation branches of a zero-byte protected child complete
from raw parent, allocator and acyclic-graph facts. -/
theorem concrete_child (tree : BorrowTree) (depth : ParentDepth tree.nodes)
    (parentTag tag : Miri.Memory.BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (present : tree.nodes.get parent = some parentNode)
    (fresh : tree.tagMapping.get tag = none)
    (room : tree.tagMapping.mapping.size ≤ 4294967295)
    (appendAligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuseValid : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodes.get index = none)
    (rank : depth.depth parent < tree.nodes.size)
    (offset : Size) (initial : Tree.LocationState) :
    ∃ after, tree.newChild offset (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO initial) (.ReservedFrz false) true = ⟨after, .ok ()⟩ := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap Miri.Memory.BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
      deassigned := tree.tagMapping.deassigned }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, UniIndex.ofNat?, room, fresh, mapping, index]
    have atEnd : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact appendAligned available
    let node : TreeNode := {
      tag := tag, parent := some parent, children := #[]
      defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
    have success := Append.sifa_after_attach {tree with tagMapping := mapping} depth index parent parentNode node
      atEnd present rfl .None
    have different := Append.parent_not_fresh tree.nodes index parent parentNode atEnd present
    have lookup := (Append.append_get_other tree.nodes index parent node atEnd different).trans present
    unfold BorrowTree.newChild
    rw [inserted]
    simp only [tagged,Option.map_some,Bool.false_eq_true,↓reduceIte]
    simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
      Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
    simp only [node] at lookup
    rw [lookup]
    simp only [DedupRangeMap.new, DedupRangeMap.iterAll, Size.ZERO, Size.ofBytes,
      beq_self_eq_true, ↓reduceIte, ← Array.forIn_toList, List.forIn_nil, pure]
    change ∃ after, (let result := (updateSifaAfterRetag
      {tree with tagMapping := mapping, nodes := Append.attachedNodes tree.nodes index parent parentNode node}
      parent .None); (⟨result.1,result.2⟩ : ChildInsertResult)) = ⟨after,.ok ()⟩
    exact ⟨_, congrArg (fun outcome => (⟨_,outcome⟩ : ChildInsertResult)) success⟩
  | some index =>
    let mapping : UniKeyMap Miri.Memory.BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
      deassigned := tree.tagMapping.deassigned.pop }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, fresh, mapping]
    obtain ⟨bounded,vacant⟩ := reuseValid index available
    let node : TreeNode := {
      tag := tag, parent := some parent, children := #[]
      defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
    have success := Reuse.sifa_after_attach {tree with tagMapping := mapping} depth index parent parentNode node
      bounded vacant present rfl rank .None
    have different := Reuse.parent_not_vacant tree.nodes index parent parentNode vacant present
    have lookup := (Sparse.get_other tree.nodes index parent node different).trans present
    unfold BorrowTree.newChild
    rw [inserted]
    simp only [tagged,Option.map_some,Bool.false_eq_true,↓reduceIte]
    simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
      Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
    simp only [node] at lookup
    rw [lookup]
    simp only [DedupRangeMap.new, DedupRangeMap.iterAll, Size.ZERO, Size.ofBytes,
      beq_self_eq_true, ↓reduceIte, ← Array.forIn_toList, List.forIn_nil, pure]
    change ∃ after, (let result := (updateSifaAfterRetag
      {tree with tagMapping := mapping, nodes := Append.attachedNodes tree.nodes index parent parentNode node}
      parent .None); (⟨result.1,result.2⟩ : ChildInsertResult)) = ⟨after,.ok ()⟩
    exact ⟨_, congrArg (fun outcome => (⟨_,outcome⟩ : ChildInsertResult)) success⟩

namespace View
open Miri.Memory
abbrev StateShape := Permission × Bool
abbrev NodeShape := BorTag × Option UniIndex × Array UniIndex × Permission × Bool

def stateShape (state : LocationState) : StateShape := (state.permission,state.accessed)
def nodeShape (node : TreeNode) : NodeShape := (node.tag,node.parent,node.children,node.defaultInitialPermission,node.isExposed)
def locationShape (location : LocationTree) : Array (Option StateShape) := location.perms.data.map (Option.map stateShape)
def treeShape (tree : BorrowTree) :=
  (tree.tagMapping,tree.nodes.data.map (Option.map nodeShape),
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)),tree.roots)

theorem insert_existing_shape {α β : Type} (shape : α → β) (nodes : UniValMap α)
    (index : UniIndex) (old next : α) (present : nodes.get index = some old) (same : shape next = shape old) :
    (nodes.insert index next).data.map (Option.map shape) = nodes.data.map (Option.map shape) := by
  have valid := lookup_valid nodes index old present
  have slot : nodes.data[index.toNat] = some old := by
    simpa only [UniValMap.get,Array.getElem?_eq_getElem valid] using present
  rw [insert_existing nodes index old next present]
  apply Array.ext
  · simp
  · intro position left right
    simp only [Array.getElem_map,Array.getElem_set]
    by_cases equal : index.toNat = position
    · subst position
      simp [slot,same]
    · simp [equal]

def weakenLocation (location : LocationTree) (index : UniIndex) (strongest : IdempotentForeignAccess) : LocationTree :=
  match location.perms.get index with
  | none => location
  | some state => {location with perms := location.perms.insert index ({state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1})}

theorem weaken_location_shape (location : LocationTree) (index : UniIndex) (strongest : IdempotentForeignAccess) :
    locationShape (weakenLocation location index strongest) = locationShape location := by
  unfold weakenLocation
  cases present : location.perms.get index with
  | none => rfl
  | some state => exact insert_existing_shape stateShape location.perms index state _ present rfl

theorem weakened_tree_shape (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (strongest : IdempotentForeignAccess) :
    treeShape (weakened tree index node strongest) = treeShape tree := by
  have nodeEq := insert_existing_shape nodeShape tree.nodes index node
    {node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1} present rfl
  have locationsEq : ((weakened tree index node strongest).locations.entries.map
      (fun segment => (segment.range,locationShape segment.data))) =
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) := by
    apply Array.ext
    · simp [weakened,DedupRangeMap.modifyAll]
    · intro position left right
      have valid : position < tree.locations.entries.size := by simpa only [Array.size_map] using right
      simp only [weakened,DedupRangeMap.modifyAll,Array.getElem_map]
      exact congrArg (fun value => ((tree.locations.entries[position]'valid).range,value))
        (weaken_location_shape (tree.locations.entries[position]'valid).data index strongest)
  have actualNodeEq : (weakened tree index node strongest).nodes.data.map (Option.map nodeShape) =
      tree.nodes.data.map (Option.map nodeShape) := nodeEq
  change (tree.tagMapping,(weakened tree index node strongest).nodes.data.map (Option.map nodeShape),
    (weakened tree index node strongest).locations.entries.map
      (fun segment => (segment.range,locationShape segment.data)),tree.roots) =
    (tree.tagMapping,tree.nodes.data.map (Option.map nodeShape),
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)),tree.roots)
  rw [actualNodeEq,locationsEq]
def Preserves (before : BorrowTree) (state : LoopState) : Prop :=
  treeShape state.2.1 = treeShape before ∧
    ∀ returned, state.1 = some returned → treeShape returned.1 = treeShape before

def Measure (state : LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- Even an error result changes no tag/topology/permission/accessed data in
this SIFA-only stage. This metadata fact is not an assertion of safe execution. -/
theorem preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess) :
    treeShape (updateSifaAfterRetag tree start strongest).1 = treeShape tree := by
  unfold updateSifaAfterRetag
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_ancestor_loop
    have step : ∀ state, Preserves tree state →
        (∃ final, scan () state = .done final ∧ Preserves tree final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves tree next ∧ Measure next < Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : treeShape current = treeShape tree := preserved.1
      cases active with
      | false => exact .inl ⟨_,rfl,⟨currentShape,by simp⟩⟩
      | true =>
        by_cases past : steps > current.nodes.size
        · refine .inl ⟨(some (current,.error (.ParentCycle (cursor.getD start))),current,cursor,steps,true),?_,?_⟩
          · simp [scan,past]
          · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
        · cases cursor with
          | none =>
            refine .inr ⟨(none,current,none,steps,false),?_,⟨currentShape,by simp⟩,?_⟩
            · simp [scan,past]
            · simp [Measure]
          | some index =>
            cases lookup : current.nodes.get index with
            | none =>
              refine .inl ⟨(some (current,.error (.MissingNode index)),current,some index,steps,true),?_,?_⟩
              · simp [scan,past,lookup]
              · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
            | some node =>
              let nextTree := weakened current index node strongest
              have nextShape : treeShape nextTree = treeShape tree :=
                (weakened_tree_shape current index node lookup strongest).trans currentShape
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node strongest with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp [Measure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp only [Measure,↓reduceIte]
                rw [sameSize]
                omega
    have initial : Preserves tree (none,tree,some start,0,true) := ⟨rfl,by simp⟩
    have maintained := loop_invariant scan Measure (Preserves tree) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual

/-- Sparse lookup commutes with the observable metadata projection. -/
theorem mapped_lookup {A B : Type} (shape : A → B) (nodes : UniValMap A) (index : UniIndex) :
    ((nodes.data.map (Option.map shape))[index.toNat]?).getD none =
      (nodes.get index).map shape := by
  simp only [Array.getElem?_map, UniValMap.get]
  cases nodes.data[index.toNat]? <;> rfl

/-- In particular, SIFA weakening preserves any fresh node's tag and exposure. -/
theorem node_fields (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex) (node : TreeNode) (present : before.nodes.get index = some node) :
    ∃ result, after.nodes.get index = some result ∧ result.tag = node.tag ∧ result.isExposed = node.isExposed := by
  have nodesEq := congrArg (fun shape => shape.2.1) same
  change after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) at nodesEq
  have observed := congrArg (fun data => (data[index.toNat]?).getD none) nodesEq
  rw [mapped_lookup, mapped_lookup, present] at observed
  cases found : after.nodes.get index with
  | none => simp [found] at observed
  | some result =>
    have shapeEq : nodeShape result = nodeShape node := by simpa [found] using observed
    exact ⟨result, rfl, congrArg (fun value => value.1) shapeEq,
      congrArg (fun value => value.2.2.2.2) shapeEq⟩

/-- An index absent from every location remains absent after SIFA weakening;
we do not assume that physical node vacancy alone implies permission vacancy. -/
theorem absent_permissions (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex)
    (absent : ∀ position (valid : position < before.locations.entries.size),
      before.locations.entries[position].data.perms.get index = none) :
    ∀ position (valid : position < after.locations.entries.size),
      after.locations.entries[position].data.perms.get index = none := by
  have locationsEq := congrArg (fun shape => shape.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at locationsEq
  have countEq := congrArg Array.size locationsEq
  simp only [Array.size_map] at countEq
  intro position valid
  have beforeValid : position < before.locations.entries.size := by omega
  have observed := congrArg (fun entries => entries[position]?) locationsEq
  simp only [Array.getElem?_map, Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem beforeValid, Option.map_some] at observed
  have permissionsEq := congrArg Prod.snd (Option.some.inj observed)
  have lookup := congrArg (fun data => (data[index.toNat]?).getD none) permissionsEq
  change ((after.locations.entries[position].data.perms.data.map (Option.map stateShape))[index.toNat]?).getD none =
    ((before.locations.entries[position].data.perms.data.map (Option.map stateShape))[index.toNat]?).getD none at lookup
  rw [mapped_lookup, mapped_lookup, absent position beforeValid] at lookup
  cases result : after.locations.entries[position].data.perms.get index with
  | none => rfl
  | some state => simp [result] at lookup

end View

namespace Release
open Lean Elab Tactic
open Miri.Memory

/-- An in-range raw range-map index always supplies its actual stored segment. -/
theorem index_exact {A : Type} (map : DedupRangeMap A) (position : Nat)
    (valid : position < map.entries.size) : map.index position = .ok map.entries[position] := by
  unfold DedupRangeMap.index
  change (match (if h : position < map.entries.size then some map.entries[position] else none) with
    | some segment => Except.ok segment
    | none => Except.error (DedupRangeMapError.indexOutOfBounds position map.entries.size)) = _
  simp [valid]

theorem list_tail {α β : Type} (items : List α) (scan : α → β → Id (ForInStep β))
    (property : List α → β → Prop) (initial : β) (good : property items initial) (distinct : items.Nodup)
    (step : ∀ item rest, item ∉ rest → ∀ state, property (item::rest) state →
      ∃ next, scan item state = .yield next ∧ property rest next) :
    property [] (forIn items initial scan) := by
  induction items generalizing initial with
  | nil => exact good
  | cons item rest ih =>
    obtain ⟨notMember,restDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨next,actual,preserved⟩ := step item rest notMember initial good
    simpa only [List.forIn_cons,actual,bind,pure] using ih next preserved restDistinct

elab "name_fresh_release_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn.forIn)
      | throwError "no actual protector release loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (←Lean.Meta.inferType body) body
    let (scan,goal) ← goal.intro1P
    let target ← goal.getType
    return [←goal.change (target.replace fun expr => if expr == body then some (mkFVar scan) else none)]

/-- Releasing an unexposed zero-sized reservation with no materialized states
really scans all allocation locations, skips each absent permission, and returns
Released. Existing roots, ranges and exposure caches are preserved. -/
theorem release (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (unexposed : node.isExposed = false)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (protections : ProtectedTags) :
    tree.releaseProtector tag protections = ⟨tree,.Released⟩ := by
  have exposure : tree.updateExposureForProtectorRelease tag = ⟨tree,.ok ()⟩ := by
    unfold BorrowTree.updateExposureForProtectorRelease
    simp [tagged,present,unexposed,Id.run,pure]
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state = (none,tree) ∧ ∀ position ∈ remaining, position < tree.locations.entries.size
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases good with ⟨equal,bounded⟩
    subst state
    have valid := bounded position (by simp)
    refine ⟨(none,tree),?_,rfl,?_⟩
    · simp only [scan,index_exact tree.locations position valid,absent position valid]
    · intro query member
      exact bounded query (by simp [member])
  have finished := list_tail (List.range tree.locations.entries.size) scan property (none,tree)
    ⟨rfl,by intro position member;exact List.mem_range.mp member⟩ (List.nodup_range) step
  simp only [List.range_eq_range'] at finished
  rw [finished.1]
  simp only [exposure]


/-- The ancestor SIFA stage preserves the exact facts needed to release a
fresh, lazy, unexposed child, including on every existing byte partition. -/
theorem after_sifa (tree : BorrowTree) (tag : BorTag) (index start : UniIndex)
    (node : TreeNode) (strongest : IdempotentForeignAccess)
    (tagged : tree.indexOfTag tag = some index)
    (present : tree.nodes.get index = some node) (unexposed : node.isExposed = false)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (protections : ProtectedTags) :
    let after := (updateSifaAfterRetag tree start strongest).1
    after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  dsimp only
  let after := (updateSifaAfterRetag tree start strongest).1
  have shape : View.treeShape after = View.treeShape tree := View.preserves tree start strongest
  have maps := congrArg (fun view => view.1) shape
  change after.tagMapping = tree.tagMapping at maps
  have selected : after.indexOfTag tag = some index := by
    unfold indexOfTag
    rw [maps]
    exact tagged
  obtain ⟨next,found,_,sameExposure⟩ := View.node_fields tree after shape index node present
  exact release after tag index next selected found (sameExposure.trans unexposed)
    (View.absent_permissions tree after shape index absent) protections

attribute [local irreducible] updateSifaAfterRetag UniValMap.insert
set_option maxHeartbeats 100000

/-- Implementation-facing source equation for a concrete zero child. The
insertion equation is discharged from raw freshness/pool data by clients. -/
theorem concrete_zero_eq (tree : BorrowTree) (parentTag tag : BorTag) (index parent : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (present : tree.nodes.get parent = some parentNode) (vacant : tree.nodes.get index = none)
    (offset : Size) (initial : LocationState) :
    let node : TreeNode := {
      tag := tag, parent := some parent, children := #[]
      defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
    let staged : BorrowTree := {tree with
      tagMapping := mapping
      nodes := Append.attachedNodes tree.nodes index parent parentNode node}
    let result := updateSifaAfterRetag staged parent .None
    tree.newChild offset (.concrete parentTag) tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨result.1,result.2⟩ := by
  dsimp only
  have different := Reuse.parent_not_vacant tree.nodes index parent parentNode vacant present
  have lookup := (Sparse.get_other tree.nodes index parent
    ({
      tag := tag, parent := some parent, children := #[], defaultInitialPermission := .ReservedFrz false
      defaultInitialSifa := .None, isExposed := false} : TreeNode) different).trans present
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [tagged,Option.map_some,Bool.false_eq_true,↓reduceIte]
  simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  rw [lookup]
  simp only [DedupRangeMap.new,DedupRangeMap.iterAll,Size.ZERO,Size.ofBytes,
    beq_self_eq_true,↓reduceIte,←Array.forIn_toList,List.forIn_nil,pure]
  rfl

/-- The freshly inserted concrete zero child can be released without changing
its post-constructor tree. Initial node vacancy and permission vacancy are
separate facts; no release or byte-access success is assumed. -/
theorem concrete_zero_release (tree : BorrowTree) (parentTag tag : BorTag) (index parent : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (present : tree.nodes.get parent = some parentNode) (vacant : tree.nodes.get index = none)
    (newTag : mapping.get tag = some index)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    let after := (tree.newChild offset (.concrete parentTag) tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true).tree
    after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  rw [concrete_zero_eq tree parentTag tag index parent parentNode mapping inserted tagged present vacant]
  dsimp only
  let node : TreeNode := {
    tag := tag, parent := some parent, children := #[]
    defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
  let staged : BorrowTree := {tree with
    tagMapping := mapping
    nodes := Append.attachedNodes tree.nodes index parent parentNode node}
  have different := Reuse.parent_not_vacant tree.nodes index parent parentNode vacant present
  have newPresent : staged.nodes.get index = some node := by
    change ((tree.nodes.insert index node).insert parent
      {parentNode with children := parentNode.children.push index}).get index = some node
    rw [Sparse.get_other _ parent index _ (Ne.symm different),Sparse.get_same]
  exact after_sifa staged tag index parent node .None newTag newPresent rfl absent protections

/-- Exact lazy-root result for the wildcard zero-size source constructor. -/
theorem wildcard_zero_eq (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (offset : Size) (initial : LocationState) :
    tree.newChild offset .wildcard tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true =
      ⟨{tree with
        tagMapping := mapping
        nodes := tree.nodes.insert index {
          tag := tag, parent := none, children := #[]
          defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
        roots := tree.roots.push index}, .ok ()⟩ := by
  simp [BorrowTree.newChild, inserted, DedupRangeMap.new, DedupRangeMap.iterAll,
    Permission.isInitial, Permission.isUnique, Permission.strongestIdempotentForeignAccess,Size.ZERO,Size.ofBytes]

/-- Ending the fresh wildcard-root protector leaves its zero-size constructor
result unchanged. Node vacancy and permission vacancy are kept independent. -/
theorem wildcard_zero_release (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (newTag : mapping.get tag = some index)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    let after := (tree.newChild offset .wildcard tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true).tree
    after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  rw [wildcard_zero_eq tree tag index mapping inserted]
  dsimp only
  apply release
  · exact newTag
  · exact Sparse.get_same _ _ _
  · rfl
  · exact absent

end Release

end ZeroProtection

end BorrowTree

end Miri.TreeBorrows

namespace Miri.TreeBorrows.BorrowTree
open Miri.ABI Miri.Memory Miri.DataStructures
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private def freshLocation : LocationTree :=
  ⟨⟨#[some ⟨.Unique,true,.None⟩]⟩,{}⟩
private def freshNormal (held : Bool) : Tree.NormalTreeState :=
  ⟨⟨#[⟨none,[]⟩]⟩,#[⟨.Disabled,false,.None⟩],if held then [0] else [],#[some ⟨.Unique,true,.None⟩]⟩
private theorem fresh_normal (held : Bool) :
    Tree.NormalTreeState.performAccess (freshNormal held) 0 .Write .VisitChildrenOfAccessed =
      ⟨freshNormal held,0,[⟨0,.LocalAccess⟩],.Completed⟩ := by
  cases held <;> decide

private theorem fresh_projection (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) :
    normalProjection (BorrowTree.new tag size) freshLocation protectedTags =
      freshNormal (protectedTags.contains tag) := by
  simp [normalProjection,BorrowTree.new,freshLocation,freshNormal,rootIndex,
    traversalProjection,UniValMap.entries,UniValMap.insert,UniValMap.get,TreeNode.defaultLocationState,
    UniIndex.ofNat?,UniIndex.toNat,Id.run,bind,Bind.bind,pure,Pure.pure,
    UniValMap.extendTo,Permission.newDisabled,Permission.newUnique]
  cases held : protectedTags.contains tag <;> simp [List.filterMap,held]

private theorem fresh_normal_at (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) :
    (BorrowTree.new tag size).performNormalAccessAt freshLocation rootIndex .Write protectedTags .VisitChildrenOfAccessed =
      ⟨freshLocation,⟨freshNormal (protectedTags.contains tag),0,[⟨0,.LocalAccess⟩],.Completed⟩,.ok ()⟩ := by
  unfold performNormalAccessAt
  rw [fresh_projection]
  simp only [rootIndex,UniIndex.toNat,UInt32.toNat_zero,fresh_normal]
  simp [freshNormal,freshLocation,BorrowTree.new,rootIndex,nodeAt,UniIndex.ofNat?,UniIndex.toNat,
    UniValMap.insert,UniValMap.get,UniValMap.extendTo,Id.run,bind,Bind.bind,pure,Pure.pure,
    ←Array.forIn_toList]

private theorem fresh_tree_at (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) (range : ByteRange) :
    (BorrowTree.new tag size).performTreeAccessAt freshLocation (some rootIndex) .Write protectedTags
      .VisitChildrenOfAccessed range =
      ⟨freshLocation,some ⟨freshNormal (protectedTags.contains tag),0,[⟨0,.LocalAccess⟩],.Completed⟩,none⟩ := by
  unfold performTreeAccessAt
  dsimp only [Id.run]
  rw [fresh_normal_at]
  simp [BorrowTree.new,rootIndex,nodeAt,UniIndex.ofNat?,UniIndex.toNat,
    UniValMap.insert,UniValMap.get,UniValMap.extendTo,Id.run,bind,Bind.bind,pure,Pure.pure,
    ←Array.forIn_toList]

/-- The actual first full-range write on fresh allocation-owned provenance.
The existing global protector map is arbitrary. -/
theorem fresh_root_full_write (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) :
    let result := (BorrowTree.new tag size).performBorrowAccessRange (.concrete tag)
      Size.ZERO size .Write protectedTags .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = BorrowTree.new tag size := by
  have source : (BorrowTree.new tag size).indexOfTag tag = some rootIndex := by
    simp [BorrowTree.indexOfTag,BorrowTree.new,rootIndex,UniKeyMap.get,Id.run,
      bind,Bind.bind,pure,Pure.pure]
  have locations : (BorrowTree.new tag size).locations = DedupRangeMap.new size freshLocation := rfl
  dsimp only
  unfold performBorrowAccessRange
  dsimp only [Id.run]
  rw [source]
  rw [locations]
  by_cases zero : size.bytes = 0
  · simp [DedupRangeMap.iterMut,DedupRangeMap.iterMutWithClone,zero,
      Id.run,bind,Bind.bind,pure,Pure.pure]
    rfl
  · rw [DedupRangeMap.iterMut_new_full size freshLocation zero]
    simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Array.size_singleton,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    simp only [List.range',List.forIn_cons,List.forIn_nil,bind,Bind.bind,pure,Pure.pure]
    simp only [Option.isNone_some,beq_self_eq_true,Bool.false_eq_true,↓reduceIte,Array.getElem?_singleton]
    rw [fresh_tree_at]
    simp only [bind,Bind.bind,pure,Pure.pure]
    have same : (DedupRangeMap.new size freshLocation).setAtPos 0 freshLocation =
        ⟨DedupRangeMap.new size freshLocation,.ok ()⟩ := by
      simp only [DedupRangeMap.new,zero,beq_iff_eq,↓reduceIte]
      rfl
    rw [same]
    simp [locations,Id.run,bind,Bind.bind,pure,Pure.pure]
    rfl

end Miri.TreeBorrows.BorrowTree

namespace Miri.TreeBorrows.BorrowTree
namespace RangeVerification

open Miri.ABI Miri.DataStructures Miri.Memory

private def wildcardMeasure (limit : Nat) (cursor : WildcardVisit × Nat) : Nat :=
  if cursor.1.active then limit - cursor.2 + 1 else 0

private theorem wildcardScan_decreases (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags)
    (isWildcardTree : Bool) (current next : WildcardVisit × Nat)
    (more : wildcardScan tree root maxLocalTag kind tags isWildcardTree () current = .yield next) :
    wildcardMeasure (tree.nodes.size * 2 + 1) next <
      wildcardMeasure (tree.nodes.size * 2 + 1) current := by
  unfold wildcardScan at more
  by_cases active : current.1.active = true
  · simp only [active, ↓reduceIte] at more
    by_cases above : tree.nodes.size * 2 + 1 < current.2 + 1
    · simp only [above, ↓reduceIte] at more
      have same := ForInStep.yield.inj more
      subst next
      have inactive : ({ current.1 with status := .ParentCycle root } : WildcardVisit).active =
          false := by simp [WildcardVisit.active]
      simp [wildcardMeasure, active, inactive]
    · simp only [above, ↓reduceIte] at more
      have same := ForInStep.yield.inj more
      subst next
      unfold wildcardMeasure
      simp only [active, ↓reduceIte]
      split <;> omega
  · simp [active] at more

private abbrev WildcardLoopState :=
  LocationTree × Bool × WildcardAccessStatus × Array (UniIndex × Bool) × Nat

private def wildcardLoopState (cursor : WildcardVisit × Nat) : WildcardLoopState :=
  (cursor.1.location, cursor.1.hasValidExposed, cursor.1.status, cursor.1.stack, cursor.2)

private def wildcardLoopStep : ForInStep (WildcardVisit × Nat) → ForInStep WildcardLoopState
  | .done cursor => .done (wildcardLoopState cursor)
  | .yield cursor => .yield (wildcardLoopState cursor)

private theorem wildcardLoopTransport (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags)
    (isWildcardTree : Bool) (scan : Unit → WildcardLoopState → Id (ForInStep WildcardLoopState))
    (transition : ∀ cursor, scan () (wildcardLoopState cursor) =
      wildcardLoopStep (wildcardScan tree root maxLocalTag kind tags isWildcardTree () cursor))
    (cursor : WildcardVisit × Nat) :
    Lean.Loop.forIn (m := Id) {} (wildcardLoopState cursor) scan =
      wildcardLoopState (Lean.Loop.forIn (m := Id) {} cursor
        (wildcardScan tree root maxLocalTag kind tags isWildcardTree)) := by
  have transport (bound : Nat) (cursor : WildcardVisit × Nat)
      (measure : wildcardMeasure (tree.nodes.size * 2 + 1) cursor = bound) :
      Lean.Loop.forIn (m := Id) {} (wildcardLoopState cursor) scan =
        wildcardLoopState (Lean.Loop.forIn (m := Id) {} cursor
          (wildcardScan tree root maxLocalTag kind tags isWildcardTree)) := by
    induction bound using Nat.strongRecOn generalizing cursor with
    | ind bound ih =>
      rw [Lean.Loop.forIn_eq_of_monadTail, transition]
      conv => rhs; rw [Lean.Loop.forIn_eq_of_monadTail]
      cases result : wildcardScan tree root maxLocalTag kind tags isWildcardTree () cursor with
      | done next => rfl
      | yield next =>
        simp only [result, wildcardLoopStep, bind, Bind.bind]
        exact ih _ (by
          rw [← measure]
          exact wildcardScan_decreases tree root maxLocalTag kind tags isWildcardTree cursor next result)
          next rfl
  exact transport _ cursor rfl

set_option maxHeartbeats 8000000 in
private theorem wildcardRuntime_eq (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags)
    (isWildcardTree : Bool) :
    tree.performWildcardAccessAt location root maxLocalTag kind tags isWildcardTree =
      finishWildcardVisit root isWildcardTree (Lean.Loop.forIn (m := Id) {}
        (⟨location, false, .Completed, #[(root, false)]⟩, 0)
        (wildcardScan tree root maxLocalTag kind tags isWildcardTree)).1 := by
  unfold performWildcardAccessAt
  simp only [Id.run, bind, pure, ForIn.forIn]
  name_ancestor_loop
  have transition (cursor : WildcardVisit × Nat) :
      scan () (wildcardLoopState cursor) =
        wildcardLoopStep (wildcardScan tree root maxLocalTag kind tags isWildcardTree () cursor) := by
    rcases cursor with ⟨⟨location, exposed, status, stack⟩, steps⟩
    simp only [scan, wildcardLoopState, wildcardScan, WildcardVisit.active]
    by_cases active : (!stack.isEmpty && status == .Completed) = true
    · simp only [active, ↓reduceIte]
      by_cases past : tree.nodes.size * 2 + 1 < steps + 1
      · simp only [past, ↓reduceIte, wildcardLoopStep, wildcardLoopState, pure, Pure.pure]
      · simp only [past, ↓reduceIte]
        unfold visitWildcardNode prepareWildcardNode
        simp only [Id.run]
        cases head : stack.back? with
        | none => simp [head, wildcardLoopState, wildcardLoopStep, pure, Pure.pure]
        | some value =>
          rcases value with ⟨index, afterChildren⟩
          cases afterChildren
          all_goals
            simp only [head, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
            cases nodeAt : tree.nodes.get index with
            | none => simp [nodeAt, wildcardLoopState, wildcardLoopStep, pure, Pure.pure]
            | some node =>
              dsimp only
              repeat' first
                | rfl
                | split <;>
                  simp_all only [commitWildcardPermission, wildcardLoopState, wildcardLoopStep,
                    bind, Bind.bind, pure, Pure.pure, Id.run, ↓reduceIte]
              all_goals
                rename_i relatedness related relation
                by_cases witness : (node.isExposed &&
                    (Permission.strongestAllowedLocalAccess ((location.perms.get index).getD node.defaultLocationState).permission
                      (tags.contains node.tag)).allows kind &&
                    (maxLocalTag.isNone || maxLocalTag.any
                      (fun maximum => maximum.value >= node.tag.value))) = true
                <;> simp_all only [wildcardLoopState, wildcardLoopStep, Bool.false_eq_true, ↓reduceIte]
              all_goals
                cases exactPosition : exactRelatedness? related
                case' none => rfl
                case' some rel =>
                  dsimp only
                  by_cases skip : (rel == .ForeignAccess &&
                      (location.perms.orInsert index node.defaultLocationState).2.foreignWriteNoop
                        (tags.contains node.tag) &&
                      (location.perms.orInsert index node.defaultLocationState).2.skipIfKnownNoop kind rel ==
                        .SkipSelfAndChildren) = true
                  · simp only [skip, ↓reduceIte]
                  · simp only [skip, Bool.false_eq_true, ↓reduceIte]
                    cases recordedAt : (location.perms.orInsert index node.defaultLocationState).2
                        |>.recordNewAccess kind rel
                    case' DebugAssertion => rfl
                    case' Recorded recorded =>
                      dsimp only [commitWildcardPermission, Id.run]
                      generalize recorded.performAccess kind rel (tags.contains node.tag) = result
                      cases result <;> try rfl
                      all_goals
                        rename_i state transition
                        dsimp only [Tree.LocationState.AccessResult.resultingState]
                        by_cases refresh : (node.isExposed && !transition.isNoop) = true
                        · simp only [refresh, ↓reduceIte]
                          let oldLevel := ((location.perms.get index).getD node.defaultLocationState).permission
                          let update := location.exposedCache.updateExposure tree.nodes index
                            (oldLevel.strongestAllowedLocalAccess (tags.contains node.tag))
                            (state.permission.strongestAllowedLocalAccess (tags.contains node.tag))
                          cases cache : update.outcome with
                          | error error =>
                            simp only [update, oldLevel] at cache
                            simp only [cache] <;> rfl
                          | ok value =>
                            cases value
                            simp only [update, oldLevel] at cache
                            simp only [cache] <;> rfl
                        · simp only [refresh, Bool.false_eq_true, ↓reduceIte] <;> rfl
    · simp [active, wildcardLoopStep, wildcardLoopState, pure, Pure.pure]
  have transport := wildcardLoopTransport tree root maxLocalTag kind tags isWildcardTree scan
    transition (⟨location, false, .Completed, #[(root, false)]⟩, 0)
  rw [show wildcardLoopState (⟨location, false, .Completed, #[(root, false)]⟩, 0) =
    (location, false, .Completed, #[(root, false)], 0) from rfl] at transport
  rw [transport]
  dsimp only [wildcardLoopState, finishWildcardVisit]
  split <;> simp_all only [Bool.false_eq_true, ↓reduceIte, pure, Pure.pure]

private def wildcardNodePre (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags) (isWildcardTree : Bool)
    (visit : WildcardVisit) (finish : WildcardVisit → Prop) : Prop :=
  match prepareWildcardNode tree root maxLocalTag kind tags isWildcardTree visit with
  | .complete next => finish next
  | .permission recorded related held commit =>
    recorded.resultPre kind related held (fun result => finish (commit result))

private theorem wildcardNodePre_iff (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags) (isWildcardTree : Bool)
    (visit : WildcardVisit) (finish : WildcardVisit → Prop) :
    finish (visitWildcardNode tree root maxLocalTag kind tags isWildcardTree visit) ↔
      wildcardNodePre tree root maxLocalTag kind tags isWildcardTree visit finish := by
  unfold visitWildcardNode wildcardNodePre
  cases prepareWildcardNode tree root maxLocalTag kind tags isWildcardTree visit with
  | complete => rfl
  | permission recorded related held commit =>
    exact Tree.LocationState.resultPre_iff recorded kind related held (fun result => finish (commit result))

private def wildcardScanPre (tree : BorrowTree) (root : UniIndex) (maxLocalTag : Option BorTag)
    (kind : AccessKind) (tags : ProtectedTags) (isWildcardTree : Bool)
    (current : WildcardVisit × Nat) (finish : ForInStep (WildcardVisit × Nat) → Prop) : Prop :=
  if current.1.active then
    let steps := current.2 + 1
    if steps > tree.nodes.size * 2 + 1 then
      finish (.yield ({ current.1 with status := .ParentCycle root }, steps))
    else wildcardNodePre tree root maxLocalTag kind tags isWildcardTree current.1
      (fun visit => finish (.yield (visit, steps)))
  else finish (.done current)

private theorem wildcardScanPre_iff (tree : BorrowTree) (root : UniIndex) (maxLocalTag : Option BorTag)
    (kind : AccessKind) (tags : ProtectedTags) (isWildcardTree : Bool)
    (current : WildcardVisit × Nat) (finish : ForInStep (WildcardVisit × Nat) → Prop) :
    finish (wildcardScan tree root maxLocalTag kind tags isWildcardTree () current) ↔
      wildcardScanPre tree root maxLocalTag kind tags isWildcardTree current finish := by
  unfold wildcardScan wildcardScanPre
  by_cases active : current.1.active = true
  · simp only [active, ↓reduceIte]
    by_cases limit : tree.nodes.size * 2 + 1 < current.2 + 1
    · simp only [limit, ↓reduceIte]
    · simp only [limit, ↓reduceIte]
      exact wildcardNodePre_iff tree root maxLocalTag kind tags isWildcardTree current.1
        (fun visit => finish (.yield (visit, current.2 + 1)))
  · simp only [active, Bool.false_eq_true, ↓reduceIte]

private def wildcardWalkPre {S : Type} (scan : S → (ForInStep S → Prop) → Prop)
    (finish : S → Prop) : Nat → S → Prop
  | 0, cursor => finish cursor
  | fuel + 1, cursor =>
    scan cursor fun
    | .done final => finish final
    | .yield next => wildcardWalkPre scan finish fuel next

private theorem wildcardWalkPre_iff (tree : BorrowTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags)
    (isWildcardTree : Bool) (finish : WildcardVisit × Nat → Prop)
    (fuel : Nat) (cursor : WildcardVisit × Nat)
    (enough : wildcardMeasure (tree.nodes.size * 2 + 1) cursor ≤ fuel) :
    finish (Lean.Loop.forIn (m := Id) {} cursor (wildcardScan tree root maxLocalTag kind tags isWildcardTree)) ↔
      wildcardWalkPre (wildcardScanPre tree root maxLocalTag kind tags isWildcardTree) finish fuel cursor := by
  induction fuel generalizing cursor with
  | zero =>
    have inactive : ¬cursor.1.active = true := by
      intro active
      simp [wildcardMeasure, active] at enough
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [wildcardWalkPre, wildcardScan, inactive, bind, pure]
  | succ fuel ih =>
    rw [Lean.Loop.forIn_eq_of_monadTail, wildcardWalkPre, ← wildcardScanPre_iff]
    cases actual : wildcardScan tree root maxLocalTag kind tags isWildcardTree () cursor with
    | done final => simp [actual, bind, pure]
    | yield next =>
      simp only [actual, bind, Bind.bind]
      have smaller := wildcardScan_decreases tree root maxLocalTag kind tags isWildcardTree
        cursor next actual
      exact ih next (by omega)

/-- Ordered wildcard-node traversal with the interpreter's own cycle limit.
Each yield consumes a visit, including the over-limit failure itself. -/
def wildcardPre (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags)
    (isWildcardTree : Bool) (finish : WildcardLocationAccessResult → Prop) : Prop :=
  let initial : WildcardVisit := ⟨location, false, .Completed, #[(root, false)]⟩
  wildcardWalkPre (wildcardScanPre tree root maxLocalTag kind tags isWildcardTree)
    (fun final => finish (finishWildcardVisit root isWildcardTree final.1))
    (tree.nodes.size * 2 + 2) (initial, 0)

theorem wildcardPre_iff (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (maxLocalTag : Option BorTag) (kind : AccessKind) (tags : ProtectedTags)
    (isWildcardTree : Bool) (finish : WildcardLocationAccessResult → Prop) :
    finish (tree.performWildcardAccessAt location root maxLocalTag kind tags isWildcardTree) ↔
      wildcardPre tree location root maxLocalTag kind tags isWildcardTree finish := by
  rw [wildcardRuntime_eq]
  unfold wildcardPre
  exact wildcardWalkPre_iff tree root maxLocalTag kind tags isWildcardTree
    (fun final => finish (finishWildcardVisit root isWildcardTree final.1))
    (tree.nodes.size * 2 + 2) (⟨location, false, .Completed, #[(root, false)]⟩, 0)
    (by simp [wildcardMeasure, WildcardVisit.active, Nat.add_assoc])

/-- Pull the continuation back through the finite list of source cursor
indices, preserving the cursor-order dependency between segment transitions. -/
def segmentsPre {S : Type} (step : Nat → (S → Prop) → S → Prop) (finish : S → Prop) :
    List Nat → S → Prop
  | [], current => finish current
  | cursor :: rest, current => step cursor (segmentsPre step finish rest) current

private theorem runSegments {S : Type} (cursors : List Nat) (step : Nat → S → S)
    (stepPre : Nat → (S → Prop) → S → Prop) (finish : S → Prop) (before : S)
    (exactStep : ∀ cursor before finish, finish (step cursor before) ↔ stepPre cursor finish before) :
    finish (Id.run (forIn cursors before (fun cursor current => pure (.yield (step cursor current))))) ↔
      segmentsPre stepPre finish cursors before := by
  induction cursors generalizing before with
  | nil => rfl
  | cons cursor rest ih =>
    simpa only [List.forIn_cons, segmentsPre, bind, Bind.bind, pure, Pure.pure] using
      (ih (step cursor before)).trans (exactStep cursor before (segmentsPre stepPre finish rest))

private def otherRootPre (tree : BorrowTree) (accessedRoot : Option UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (minExposed maxLocalTag : Option BorTag) (position : Nat)
    (finish : OtherRootProgress → Prop) (current : OtherRootProgress) : Prop :=
  match otherRootAction tree accessedRoot mode minExposed position current with
  | .skip => finish current
  | .stop => finish { current with stopped := true }
  | .visit root =>
    wildcardPre tree current.location root maxLocalTag kind tags (position != 0)
      (fun wildcard => finish (commitOtherRoot current range wildcard))

private theorem otherRootPre_iff (tree : BorrowTree) (accessedRoot : Option UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (minExposed maxLocalTag : Option BorTag) (position : Nat)
    (finish : OtherRootProgress → Prop) (current : OtherRootProgress) :
    finish (advanceOtherRoot tree accessedRoot kind tags mode range minExposed maxLocalTag
      position current) ↔
      otherRootPre tree accessedRoot kind tags mode range minExposed maxLocalTag position finish current := by
  unfold advanceOtherRoot otherRootPre
  cases otherRootAction tree accessedRoot mode minExposed position current with
  | skip => rfl
  | stop => rfl
  | visit root =>
    dsimp only
    exact wildcardPre_iff tree current.location root maxLocalTag kind tags (position != 0)
      (fun wildcard => finish (commitOtherRoot current range wildcard))

private def otherRootsPre (tree : BorrowTree) (location : LocationTree)
    (source accessedRoot : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (normalAccess : Option Tree.NormalAccessResult) (finish : TreeLocationAccessAtResult → Prop) : Prop :=
  let (minExposed, maxLocalTag) := otherRootBounds tree source accessedRoot mode
  segmentsPre (otherRootPre tree accessedRoot kind tags mode range minExposed maxLocalTag)
    (fun final => finish ⟨final.location, normalAccess, final.status⟩)
    (List.range' 0 tree.roots.size) { location }

private theorem otherRootsPre_iff (tree : BorrowTree) (location : LocationTree)
    (source accessedRoot : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (normalAccess : Option Tree.NormalAccessResult) (finish : TreeLocationAccessAtResult → Prop) :
    finish (performOtherRootsAt tree location source accessedRoot kind tags mode range normalAccess) ↔
      otherRootsPre tree location source accessedRoot kind tags mode range normalAccess finish := by
  unfold performOtherRootsAt otherRootsPre
  dsimp only [Id.run]
  rcases otherRootBounds tree source accessedRoot mode with ⟨minExposed, maxLocalTag⟩
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact runSegments (S := OtherRootProgress) _ _ _
    (fun final => finish ⟨final.location, normalAccess, final.status⟩) _
    (fun position current finish =>
      otherRootPre_iff tree accessedRoot kind tags mode range minExposed maxLocalTag
        position finish current)

/-- Pull one allocation location through the concrete tree's ordered node
visits and cache commits, then through the other roots in source order. -/
def locationContract (tree : BorrowTree) (location : LocationTree) (source : Option UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (finish : TreeLocationAccessAtResult → Prop) : Prop :=
  match source with
  | none => otherRootsPre tree location none none kind tags mode range none finish
  | some index =>
    Tree.NormalTreeState.accessPre (normalProjection tree location tags) index.toNat kind mode
      (fun access =>
        let normal := commitNormalAccessAt tree location kind tags access
        let seen := some normal.access
        match normal.outcome with
        | .error error => finish ⟨normal.location, seen, some (.CacheFailure range error)⟩
        | .ok () =>
          if normal.access.status != .Completed then
            finish ⟨normal.location, seen, some (.AccessFailure range normal.access.status)⟩
          else match UniIndex.ofNat? normal.access.root with
            | none => finish ⟨normal.location, seen,
                some (.AccessFailure range (.MissingLocationState normal.access.root))⟩
            | some root =>
              otherRootsPre tree normal.location (some index) (some root)
                kind tags mode range seen finish)

theorem locationContract_iff (tree : BorrowTree) (location : LocationTree) (source : Option UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (finish : TreeLocationAccessAtResult → Prop) :
    finish (tree.performTreeAccessAt location source kind tags mode range) ↔
      locationContract tree location source kind tags mode range finish := by
  rw [locationRuntime_eq]
  cases source with
  | none => exact otherRootsPre_iff tree location none none kind tags mode range none finish
  | some index =>
    unfold locationContract
    dsimp only
    rw [Tree.NormalTreeState.accessPre_iff, performNormalAccessAt_eq_commit]
    generalize commitNormalAccessAt tree location kind tags
      ((normalProjection tree location tags).performAccess index.toNat kind mode) = normal
    cases outcome : normal.outcome with
    | error error => rfl
    | ok value =>
      cases value
      by_cases failed : (normal.access.status != .Completed) = true
      · simp only [failed, ↓reduceIte]
      · simp only [failed, Bool.false_eq_true, ↓reduceIte]
        cases UniIndex.ofNat? normal.access.root with
        | none => rfl
        | some root =>
          exact otherRootsPre_iff tree normal.location (some index) (some root)
            kind tags mode range (some normal.access) finish

abbrev Progress :=
  DedupRangeMap LocationTree × Array BorrowTreeLocationResult × BorrowTreeAccessStatus

/-- One cursor of the interpreter's ranged access loop. The incoming locations
are the prepared snapshots, and the updated map includes the current commit
even if the transition or map commit failed. -/
def advance (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) (current : Progress) : Progress :=
  if current.2.2 == .Completed then
    match prepared.positions[cursor]?, prepared.segments[cursor]? with
    | some position, some segment =>
      let access := tree.performTreeAccessAt segment.data source kind tags mode segment.range
      let mutation := current.1.setAtPos position access.location
      let visited := current.2.1.push ⟨segment.range, access.normalAccess⟩
      let status := match mutation.outcome with
        | .error error => BorrowTreeAccessStatus.LocationMapFailure segment.range error
        | .ok () => access.status.getD .Completed
      (mutation.state, visited, status)
    | _, _ => (current.1, current.2.1,
      .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size))
  else current

private def advancePre (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) (finish : Progress → Prop) (current : Progress) : Prop :=
  if current.2.2 == .Completed then
    match prepared.positions[cursor]?, prepared.segments[cursor]? with
    | some position, some segment =>
      locationContract tree segment.data source kind tags mode segment.range (fun access =>
        let mutation := current.1.setAtPos position access.location
        let visited := current.2.1.push ⟨segment.range, access.normalAccess⟩
        match mutation.outcome with
        | .error error => finish (mutation.state, visited, .LocationMapFailure segment.range error)
        | .ok () => finish (mutation.state, visited, access.status.getD .Completed))
    | _, _ => finish (current.1, current.2.1,
      .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size))
  else finish current

private theorem advancePre_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) (current : Progress) (finish : Progress → Prop) :
    finish (advance tree prepared source kind tags mode cursor current) ↔
      advancePre tree prepared source kind tags mode cursor finish current := by
  unfold advance advancePre
  by_cases completed : (current.2.2 == .Completed) = true
  · simp only [completed, ↓reduceIte]
    cases prepared.positions[cursor]? with
    | none => rfl
    | some position =>
      cases prepared.segments[cursor]? with
      | none => rfl
      | some segment =>
        dsimp only
        rw [← locationContract_iff]
        generalize tree.performTreeAccessAt segment.data source kind tags mode segment.range = access
        cases (current.1.setAtPos position access.location).outcome <;> rfl
  · simp only [completed, Bool.false_eq_true, ↓reduceIte]

private theorem cursor_equation (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) (current : Progress) :
    (do
      let mut currentMap := current.1
      let mut visited := current.2.1
      let mut status := current.2.2
      if status == .Completed then
        match prepared.positions[cursor]?, prepared.segments[cursor]? with
        | some position, some segment =>
          let access := tree.performTreeAccessAt segment.data source kind tags mode segment.range
          let mutation := currentMap.setAtPos position access.location
          currentMap := mutation.state
          visited := visited.push ⟨segment.range, access.normalAccess⟩
          match mutation.outcome with
          | .error error => status := .LocationMapFailure segment.range error
          | .ok () =>
            match access.status with
            | some failure => status := failure
            | none => pure ()
        | _, _ => status := .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)
      pure (ForInStep.yield (currentMap, visited, status)) : Id (ForInStep Progress)) =
      pure (.yield (advance tree prepared source kind tags mode cursor current)) := by
  rcases current with ⟨map, visited, status⟩
  by_cases completed : status = .Completed
  · subst status
    unfold advance
    simp only [beq_self_eq_true, ↓reduceIte]
    cases prepared.positions[cursor]? with
    | none => rfl
    | some position =>
      cases prepared.segments[cursor]? with
      | none => rfl
      | some segment =>
        dsimp only
        generalize (tree.performTreeAccessAt segment.data source kind tags mode segment.range) = access
        generalize map.setAtPos position access.location = mutation
        cases mutation.outcome with
        | error => rfl
        | ok value =>
          cases value
          cases access.status <;> rfl
  · simp [advance, completed, pure, Pure.pure]

/-- The source guard for a concrete tag precedes range preparation. For
wildcard provenance the cursor rule receives no selected concrete source. -/
def accessContract (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (finish : BorrowTreeAccessResult → Prop) : Prop :=
  let source := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  let prepare :=
    let prepared := tree.locations.iterMut offset length
    let finishProgress : Progress → Prop := fun (map, visited, status) =>
      finish ⟨{ tree with locations := map }, visited, status⟩
    match prepared.outcome with
    | .error error => finishProgress (prepared.state, #[], .RangeMapFailure error)
    | .ok () =>
      segmentsPre (advancePre tree prepared source kind tags mode) finishProgress
        (List.range' 0 prepared.positions.size) (prepared.state, #[], .Completed)
  match provenance with
  | .concrete tag => if source.isNone then finish ⟨tree, #[], .MissingTag tag⟩ else prepare
  | .wildcard => prepare

/-- The precondition follows the actual ordered iterator and its concrete
cursor transitions. It applies to every tree, including malformed maps. -/
theorem accessContract_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (finish : BorrowTreeAccessResult → Prop) :
    finish (tree.performBorrowAccessRange provenance offset length kind tags mode) ↔
      accessContract tree provenance offset length kind tags mode finish := by
  unfold performBorrowAccessRange accessContract
  cases provenance
  case' concrete tag =>
    cases found : tree.indexOfTag tag
    case' none => simp only [found, Option.isNone_none, ↓reduceIte, Id.run]; rfl
    case' some index =>
      simp only [found, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Id.run]
  case' wildcard => simp only [Id.run]
  all_goals
    generalize h : tree.locations.iterMut offset length = prepared
    cases outcome : prepared.outcome with
    | error error => rfl
    | ok value =>
      cases value
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, cursor_equation]
      exact runSegments (S := Progress) _ _ _ (fun progress =>
        finish ⟨{ tree with locations := progress.1 }, progress.2.1, progress.2.2⟩) _
        (advancePre_iff tree prepared _ kind tags mode)

private def findFirstPre {A B : Type} (check : A → (Option B → Prop) → Prop)
    (finish : Option B → Prop) : List A → Prop
  | [] => finish none
  | item :: rest => check item fun
      | some value => finish (some value)
      | none => findFirstPre check finish rest

private theorem findFirstPre_iff {A B : Type} (read : A → Option B)
    (check : A → (Option B → Prop) → Prop)
    (exactCheck : ∀ item finish, finish (read item) ↔ check item finish)
    (finish : Option B → Prop) (items : List A) :
    finish (items.findSome? read) ↔ findFirstPre check finish items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.findSome?_cons, findFirstPre]
    rw [← exactCheck]
    cases read item with
    | none => exact ih
    | some value => rfl

private def protectionEventsPre (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (events : List Tree.TraversalEvent) (finish : Option UniIndex → Prop) : Prop :=
  findFirstPre (fun event next => next (strongProtectorAt tree location tags event)) finish events

private theorem protectionEventsPre_iff (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (events : List Tree.TraversalEvent) (finish : Option UniIndex → Prop) :
    finish (events.findSome? (strongProtectorAt tree location tags)) ↔
      protectionEventsPre tree location tags events finish :=
  findFirstPre_iff _ _ (fun _ _ => Iff.rfl) _ _

private def protectionRootsPre (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (topology : Tree.TraversalTree) (accessedRoot : Option UniIndex)
    (finish : Option UniIndex → Prop) : Prop :=
  findFirstPre (fun root next =>
    if accessedRoot == some root then next none
    else
      let events := (topology.traverse root.toNat .VisitChildrenOfAccessed []).2
      protectionEventsPre tree location tags events next) finish tree.roots.reverse.toList

private theorem protectionRootsPre_iff (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (topology : Tree.TraversalTree) (accessedRoot : Option UniIndex)
    (finish : Option UniIndex → Prop) :
    finish (findStrongProtectorInOtherRoots tree location tags topology accessedRoot) ↔
      protectionRootsPre tree location tags topology accessedRoot finish := by
  unfold findStrongProtectorInOtherRoots protectionRootsPre
  apply findFirstPre_iff
  intro root next
  by_cases same : (accessedRoot == some root) = true
  · simp only [same, ↓reduceIte]
  · simp only [same, Bool.false_eq_true, ↓reduceIte]
    exact protectionEventsPre_iff tree location tags _ next

private def protectorsPre (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (start : Option UniIndex) (finish : Option UniIndex → Prop) : Prop :=
  let topology := traversalProjection tree
  match start with
  | none => protectionRootsPre tree location tags topology none finish
  | some index =>
    let (root, events) := topology.traverse index.toNat .VisitChildrenOfAccessed []
    protectionEventsPre tree location tags events fun
      | some index => finish (some index)
      | none => protectionRootsPre tree location tags topology (UniIndex.ofNat? root) finish

private theorem protectorsPre_iff (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (start : Option UniIndex) (finish : Option UniIndex → Prop) :
    finish (firstStrongProtector tree location tags start) ↔ protectorsPre tree location tags start finish := by
  cases start with
  | none => exact protectionRootsPre_iff tree location tags _ none finish
  | some index =>
    unfold firstStrongProtector protectorsPre
    dsimp only
    generalize (traversalProjection tree).traverse index.toNat .VisitChildrenOfAccessed [] = schedule
    rcases schedule with ⟨root, events⟩
    dsimp only
    rw [← protectionEventsPre_iff]
    cases events.findSome? (strongProtectorAt tree location tags) with
    | some index => rfl
    | none => exact protectionRootsPre_iff tree location tags _ (UniIndex.ofNat? root) finish

private def deallocationCursorPre (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (tags : ProtectedTags) (start : Option UniIndex) (cursor : Nat)
    (finish : Option BorrowTreeDeallocStatus → Prop) : Prop :=
  match prepared.positions[cursor]?, prepared.segments[cursor]? with
  | some position, some segment =>
    protectorsPre tree segment.data tags start fun
      | some index => finish (some (.ProtectedDealloc segment.range index))
      | none =>
        match prepared.state.index position with
        | .error error => finish (some (.RangeMapFailure error))
        | .ok _ => finish none
  | _, _ => finish (some (.RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)))

private theorem deallocationCursorPre_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (tags : ProtectedTags) (start : Option UniIndex) (cursor : Nat)
    (finish : Option BorrowTreeDeallocStatus → Prop) :
    finish (deallocationCursor tree prepared tags start cursor) ↔
      deallocationCursorPre tree prepared tags start cursor finish := by
  unfold deallocationCursor deallocationCursorPre
  cases prepared.positions[cursor]? with
  | none => rfl
  | some position =>
    cases prepared.segments[cursor]? with
    | none => rfl
    | some segment =>
      dsimp only
      rw [← protectorsPre_iff]
      cases firstStrongProtector tree segment.data tags start with
      | some index => rfl
      | none => cases prepared.state.index position <;> rfl

/-- Pull back the postcondition through the source-ordered strong-protector
checks that follow a deallocation write. -/
def deallocateAfterWritePre (accessed : BorrowTreeAccessResult) (provenance : Miri.Memory.ProvenanceExtra)
    (offset length : Size) (tags : ProtectedTags) (finish : BorrowTreeDeallocResult → Prop) : Prop :=
  if accessed.status != .Completed then finish ⟨accessed.tree, .AccessFailure accessed.status⟩
  else
    let start := match provenance with
      | .concrete tag => accessed.tree.indexOfTag tag
      | .wildcard => none
    let scan :=
      let prepared := accessed.tree.locations.iterMut offset length
      let updatedTree := { accessed.tree with locations := prepared.state }
      match prepared.outcome with
      | .error error => finish ⟨updatedTree, .RangeMapFailure error⟩
      | .ok () =>
        findFirstPre (deallocationCursorPre accessed.tree prepared tags start)
          (fun failure => finish ⟨updatedTree, failure.getD .Deallocated⟩)
          (List.range' 0 prepared.positions.size)
    match provenance with
    | .concrete tag => if start.isNone then finish ⟨accessed.tree, .MissingTag tag⟩ else scan
    | .wildcard => scan

theorem deallocateAfterWritePre_iff (accessed : BorrowTreeAccessResult)
    (provenance : Miri.Memory.ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags) (finish : BorrowTreeDeallocResult → Prop) :
    finish (deallocateAfterWrite accessed provenance offset length tags) ↔
      deallocateAfterWritePre accessed provenance offset length tags finish := by
  unfold deallocateAfterWrite deallocateAfterWritePre
  by_cases failed : (accessed.status != .Completed) = true
  · simp only [failed, ↓reduceIte]; rfl
  · simp only [failed, Bool.false_eq_true, ↓reduceIte, Id.run]
    cases provenance
    case' concrete tag =>
      cases found : accessed.tree.indexOfTag tag
      case' none => simp only [found, Option.isNone_none, ↓reduceIte]; rfl
      case' some index => simp only [found, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    case' wildcard => dsimp only
    all_goals
      generalize (accessed.tree.locations.iterMut offset length) = prepared
      cases prepared.outcome with
      | error error => rfl
      | ok value =>
        cases value
        exact findFirstPre_iff _ _ (deallocationCursorPre_iff accessed.tree prepared tags _)
          (fun failure => finish ⟨{ accessed.tree with locations := prepared.state },
            failure.getD .Deallocated⟩) _

end RangeVerification
end Miri.TreeBorrows.BorrowTree

namespace Miri.TreeBorrows.BorrowTree.MutationVerification

open Miri.ABI Miri.DataStructures Miri.Memory

/-- Walk the locations in order, stopping at the first failed update. If an
update changes the cache before failing, the error sees the committed cache. -/
def locationsPre (update : LocationTree → LocationTree × Except TreeMutationError Unit)
    (post : BorrowTree → Prop) (failure : TreeMutationError → BorrowTree → Prop) :
    List Nat → BorrowTree → Prop
  | [], current => post current
  | position :: rest, current =>
    match current.locations.index position with
    | .error error => failure (.RangeMap error) current
    | .ok segment =>
      let (nextLocation, outcome) := update segment.data
      let mutation := current.locations.setAtPos position nextLocation
      let after := { current with locations := mutation.state }
      match outcome, mutation.outcome with
      | .error error, _ => failure error after
      | .ok (), .error error => failure (.RangeMap error) after
      | .ok (), .ok () => locationsPre update post failure rest after

def updateEveryLocationPre (tree : BorrowTree)
    (update : LocationTree → LocationTree × Except TreeMutationError Unit)
    (post : BorrowTree → Prop) (failure : TreeMutationError → BorrowTree → Prop) : Prop :=
  locationsPre update post failure (List.range' 0 tree.locations.entries.size) tree

private theorem updateEveryLocationPre_iff (tree : BorrowTree)
    (update : LocationTree → LocationTree × Except TreeMutationError Unit)
    (post : BorrowTree → Prop) (failure : TreeMutationError → BorrowTree → Prop) :
    updateEveryLocationPre tree update post failure ↔
      let result := updateEveryLocation tree update
      match result.outcome with
      | .error error => failure error result.tree
      | .ok () => post result.tree := by
  unfold updateEveryLocationPre updateEveryLocation
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Id.run]
  generalize List.range' 0 tree.locations.entries.size = positions
  induction positions generalizing tree with
  | nil => rfl
  | cons position rest ih =>
    simp only [locationsPre, List.forIn_cons, bind, Bind.bind, pure, Pure.pure]
    cases found : tree.locations.index position with
    | error => simp only [found]
    | ok segment =>
      rcases effect : update segment.data with ⟨location, outcome⟩
      cases outcome with
      | error => simp only [found, effect]
      | ok value =>
        cases value
        cases written : (tree.locations.setAtPos position location).outcome with
        | error => simp only [found, effect, written]
        | ok value =>
          cases value
          simpa only [found, effect, written, bind, Bind.bind, pure, Pure.pure] using ih
            { tree with locations := (tree.locations.setAtPos position location).state }

/-- Pull back tag exposure through lookup, publishing the exposed node, and
the ordered updates of the location caches. -/
def exposePre (tree : BorrowTree) (protectedTags : ProtectedTags) (tag : BorTag)
    (post : BorrowTree → Prop) (failure : TreeMutationError → BorrowTree → Prop) : Prop :=
  match tree.indexOfTag tag with
  | none => failure (.MissingTag tag) tree
  | some index =>
    match tree.nodeAt index with
    | none => failure (.MissingNode index) tree
    | some node =>
      if node.isExposed then post tree
      else
        let after := { tree with nodes := tree.nodes.insert index { node with isExposed := true } }
        updateEveryLocationPre after (fun location =>
          let state := (location.perms.get index).getD node.defaultLocationState
          let level := state.permission.strongestAllowedLocalAccess (protectedTags.contains tag)
          let updated := location.exposedCache.updateExposure after.nodes index .None level
          ({ location with exposedCache := updated.cache },
            updated.outcome.mapError TreeMutationError.ExposedCache)) post failure

theorem exposePre_iff (tree : BorrowTree) (protectedTags : ProtectedTags) (tag : BorTag)
    (post : BorrowTree → Prop) (failure : TreeMutationError → BorrowTree → Prop) :
    exposePre tree protectedTags tag post failure ↔
      let result := tree.exposeTag protectedTags tag
      match result.outcome with
      | .error error => failure error result.tree
      | .ok () => post result.tree := by
  unfold exposePre exposeTag
  cases indexEq : tree.indexOfTag tag with
  | none => rfl
  | some index =>
    dsimp only [Id.run]
    cases nodeEq : tree.nodeAt index with
    | none => simp only [nodeEq]; rfl
    | some node =>
      simp only [nodeEq]
      split
      · rfl
      · exact updateEveryLocationPre_iff _ _ _ _

/-- An unexposed tag remains unexposed after releasing its protector. For an
exposed tag, pull the continuation back through its per-location cache changes. -/
def releaseExposurePre (tree : BorrowTree) (tag : BorTag) (post : BorrowTree → Prop)
    (failure : TreeMutationError → BorrowTree → Prop) : Prop :=
  match tree.indexOfTag tag with
  | none => failure (.MissingTag tag) tree
  | some index =>
    match tree.nodeAt index with
    | none => failure (.MissingNode index) tree
    | some node =>
      if !node.isExposed then post tree
      else
        updateEveryLocationPre tree (fun location =>
          let state := (location.perms.get index).getD node.defaultLocationState
          let oldLevel := state.permission.strongestAllowedLocalAccess true
          let level := state.permission.strongestAllowedLocalAccess false
          let updated := location.exposedCache.updateExposure tree.nodes index oldLevel level
          ({ location with exposedCache := updated.cache },
            updated.outcome.mapError TreeMutationError.ExposedCache)) post failure

theorem releaseExposurePre_iff (tree : BorrowTree) (tag : BorTag) (post : BorrowTree → Prop)
    (failure : TreeMutationError → BorrowTree → Prop) :
    releaseExposurePre tree tag post failure ↔
      let result := tree.updateExposureForProtectorRelease tag
      match result.outcome with
      | .error error => failure error result.tree
      | .ok () => post result.tree := by
  unfold releaseExposurePre updateExposureForProtectorRelease
  cases indexEq : tree.indexOfTag tag with
  | none => rfl
  | some index =>
    dsimp only [Id.run]
    cases nodeEq : tree.nodeAt index with
    | none => simp only [nodeEq]; rfl
    | some node =>
      simp only [nodeEq]
      split
      · rfl
      · exact updateEveryLocationPre_iff _ _ _ _

/-- The GC's final pass canonicalizes and merges adjacent location ranges. -/
def mergeAfterCollectPre (tree : BorrowTree) (post : BorrowTree → Prop)
    (failure : TreeGcError → BorrowTree → Prop) : Prop :=
  let canonical := tree.locations.modifyAll fun _ loc => trimLocationForRangeEquality loc
  let merged := canonical.mergeAdjacentThorough
  let after := { tree with locations := merged.state }
  match merged.outcome with
  | .error error => failure (.RangeMerge error) after
  | .ok () => post after

/-- Remove a dead leaf or splice a compatible replacement into its parent.
The state includes the list of children retained so far in source order. -/
def collectChild (live : Array BorTag) (parent child : UniIndex) (current : BorrowTree)
    (kept : Array UniIndex) : BorrowTree × Array UniIndex × Except TreeGcError Unit := Id.run do
  if nodeIsUseless current child live then
    let (after, outcome) := removeUselessNode current child
    return (after, kept, outcome)
  match replacementChild? current child live with
  | none => return (current, kept.push child, .ok ())
  | some replacement =>
    let (after, outcome) := removeUselessNode current child
    match outcome with
    | .error error => return (after, kept, .error error)
    | .ok () =>
      let some node := after.nodes.get replacement
        | return (after, kept, .error (.MissingReplacementChild replacement))
      let nodes := after.nodes.insert replacement { node with parent := some parent }
      return ({ after with nodes }, kept.push replacement, .ok ())

private theorem remove_node_size (tree : BorrowTree) (index : UniIndex) :
    (removeUselessNode tree index).1.nodes.size = tree.nodes.size := by
  unfold removeUselessNode
  cases tree.nodes.get index with
  | none => rfl
  | some node =>
    simp only [Id.run, pure, Pure.pure, UniValMap.remove]
    split
    · simp [UniValMap.size]
    · rfl

private theorem collectChild_size (live : Array BorTag) (parent child : UniIndex)
    (current : BorrowTree) (kept : Array UniIndex) :
    (collectChild live parent child current kept).1.nodes.size = current.nodes.size := by
  unfold collectChild
  split
  · exact remove_node_size current child
  · cases selected : replacementChild? current child live with
    | none => rfl
    | some replacement =>
      let removed := removeUselessNode current child
      have size := remove_node_size current child
      change removed.1.nodes.size = current.nodes.size at size
      simp only [Id.run, pure, Pure.pure, selected]
      cases status : removed.2 with
      | error => simpa only [removed, status] using size
      | ok value =>
        cases value
        have actual : (removeUselessNode current child).2 = .ok () := status
        simp only [actual]
        cases found : removed.1.nodes.get replacement with
        | none =>
          have absent : (removeUselessNode current child).1.nodes.get replacement = none := found
          simpa only [absent] using size
        | some node =>
          have present : (removeUselessNode current child).1.nodes.get replacement = some node := found
          simp only [present]
          exact (ZeroProtection.insert_existing_size removed.1.nodes replacement node _ found).trans size

/-- Finish one postorder stack frame, with the source's node checks after all
child edits. Each successful edit supplies the concrete successor to the next. -/
def collectChildrenPre (live : Array BorTag) (parent : UniIndex)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop) :
    List UniIndex → BorrowTree → Array UniIndex → Prop
  | [], current, kept =>
    match current.nodes.get parent with
    | none => failure (.MissingNode parent) current
    | some node => post { current with nodes := current.nodes.insert parent { node with children := kept } }
  | child :: rest, current, kept =>
    let (after, kept, outcome) := collectChild live parent child current kept
    match outcome with
    | .error error => failure error after
    | .ok () => collectChildrenPre live parent post failure rest after kept

private abbrev ChildCollectProgress := Option TreeGcResult × BorrowTree × Array UniIndex

private def collectChildStep (live : Array BorTag) (parent child : UniIndex)
    (state : ChildCollectProgress) : Id (ForInStep ChildCollectProgress) :=
  let (after, kept, outcome) := collectChild live parent child state.2.1 state.2.2
  match outcome with
  | .error error => .done (some ⟨after, .error error⟩, after, state.2.2)
  | .ok () => .yield (none, after, kept)

private abbrev collectChildSource (live : Array BorTag) (parent child : UniIndex)
    (progress : ChildCollectProgress) : Id (ForInStep ChildCollectProgress) :=
  let current := progress.2.1
  let kept := progress.2.2
  let removed := removeUselessNode current child
  if nodeIsUseless current child live then
    match removed.2 with
    | .error error => .done (some ⟨removed.1, .error error⟩, removed.1, kept)
    | .ok () => .yield (none, removed.1, kept)
  else
    match replacementChild? current child live with
    | none => .yield (none, current, kept.push child)
    | some replacement =>
      match removed.2 with
      | .error error => .done (some ⟨removed.1, .error error⟩, removed.1, kept)
      | .ok () =>
        match removed.1.nodes.get replacement with
        | some node =>
          let nextNode := { node with parent := some parent }
          .yield (none, { removed.1 with nodes := removed.1.nodes.insert replacement nextNode },
            kept.push replacement)
        | _ => .done (some ⟨removed.1, .error (.MissingReplacementChild replacement)⟩, removed.1, kept)

private theorem collectChildStep_eq (live : Array BorTag) (parent child : UniIndex)
    (progress : ChildCollectProgress) :
    collectChildSource live parent child progress = collectChildStep live parent child progress := by
  simp only [collectChildSource, collectChildStep, collectChild, Id.run]
  by_cases useless : nodeIsUseless progress.2.1 child live = true
  · simp only [useless, ↓reduceIte]
    rcases removed : removeUselessNode progress.2.1 child with ⟨tree, outcome⟩
    cases outcome <;> simp [removed, bind, Bind.bind, pure, Pure.pure]
  · simp only [useless, ↓reduceIte]
    cases selected : replacementChild? progress.2.1 child live with
    | none => simp [selected, pure, Pure.pure]
    | some replacement =>
      simp only [selected]
      rcases removed : removeUselessNode progress.2.1 child with ⟨tree, outcome⟩
      cases outcome with
      | error => simp [removed, bind, Bind.bind, pure, Pure.pure]
      | ok value =>
        cases value
        cases found : tree.nodes.get replacement <;>
          simp [removed, found, bind, Bind.bind, pure, Pure.pure]

private theorem collectChildFold_eq (live : Array BorTag) (parent : UniIndex)
    (children : Array UniIndex) (initial : ChildCollectProgress)
    (actual : (child : UniIndex) → child ∈ children → ChildCollectProgress → Id (ForInStep ChildCollectProgress))
    (same : ∀ child h state, actual child h state = collectChildStep live parent child state) :
    forIn' (m := Id) children initial actual =
      forIn (m := Id) children.toList initial (collectChildStep live parent) := by
  rw [Array.forIn_toList]
  change forIn' (m := Id) children initial actual =
    forIn' (m := Id) children initial (fun child _ state => collectChildStep live parent child state)
  rw [show actual = _ from funext fun child => funext fun h => funext (same child h)]

private theorem collectSourceFold_eq (live : Array BorTag) (parent : UniIndex)
    (children : Array UniIndex) (initial : ChildCollectProgress) :
    forIn' (m := Id) children initial (fun child _ progress =>
      collectChildSource live parent child progress) =
      forIn (m := Id) children.toList initial (collectChildStep live parent) := by
  apply collectChildFold_eq live parent
  intro child _ progress
  exact collectChildStep_eq live parent child progress

private def checkedFinishNode (parent : UniIndex) (progress : ChildCollectProgress)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop) : Prop :=
  match progress.1 with
  | some result =>
    match result.outcome with
    | .ok () => post result.tree
    | .error error => failure error result.tree
  | none =>
    let current := progress.2.1
    match current.nodes.get parent with
    | none => failure (.MissingNode parent) current
    | some node =>
      post { current with nodes := current.nodes.insert parent { node with children := progress.2.2 } }

private theorem collectChildrenPre_iff (live : Array BorTag) (parent : UniIndex)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop)
    (children : List UniIndex) (current : BorrowTree) (kept : Array UniIndex) :
    collectChildrenPre live parent post failure children current kept ↔
      checkedFinishNode parent (Id.run (forIn children (none, current, kept)
        (collectChildStep live parent))) post failure := by
  induction children generalizing current kept with
  | nil => rfl
  | cons child rest ih =>
    simp only [collectChildrenPre, List.forIn_cons, bind, Bind.bind, collectChildStep]
    rcases childResult : collectChild live parent child current kept with ⟨after, kept, outcome⟩
    cases outcome with
    | error => simp [childResult, checkedFinishNode]
    | ok value =>
      cases value
      simpa only [childResult] using ih after kept

private theorem collectChildFold_error (live : Array BorTag) (parent : UniIndex)
    (children : List UniIndex) (current : BorrowTree) (kept : Array UniIndex) :
    ∀ status, (forIn (m := Id) children (none, current, kept)
      (collectChildStep live parent)).1 = some status →
      ∃ error, status.outcome = .error error := by
  induction children generalizing current kept with
  | nil => simp [List.forIn_nil, pure, Pure.pure]
  | cons child rest ih =>
    simp only [List.forIn_cons, bind, Bind.bind, collectChildStep]
    rcases effect : collectChild live parent child current kept with ⟨after, kept, outcome⟩
    cases outcome with
    | error error =>
      intro status equal
      have returned : status = ⟨after, .error error⟩ := (Option.some.inj equal).symm
      exact ⟨error, by rw [returned]⟩
    | ok value =>
      cases value
      exact ih after kept

private theorem collectChildrenPre_congr (live : Array BorTag) (parent : UniIndex)
    (post post' : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop)
    (children : List UniIndex) (current : BorrowTree) (kept : Array UniIndex)
    (same : ∀ after, after.nodes.size = current.nodes.size → (post after ↔ post' after)) :
    collectChildrenPre live parent post failure children current kept ↔
      collectChildrenPre live parent post' failure children current kept := by
  induction children generalizing current kept with
  | nil =>
    simp only [collectChildrenPre]
    cases found : current.nodes.get parent with
    | none => rfl
    | some node =>
      exact same _ (ZeroProtection.insert_existing_size current.nodes parent node _ found)
  | cons child rest ih =>
    simp only [collectChildrenPre]
    have size := collectChild_size live parent child current kept
    rcases childResult : collectChild live parent child current kept with ⟨after, kept, outcome⟩
    cases outcome with
    | error => rfl
    | ok value =>
      cases value
      simp only [childResult]
      have sameSize : after.nodes.size = current.nodes.size := by simpa only [childResult] using size
      exact ih after kept (fun tree size => same tree (size.trans sameSize))

/-- One checked cursor in the source postorder traversal. Descending advances
the parent's cursor; completing a node applies its ordered child edits then pops. -/
def collectWalkPre (live : Array BorTag) (root : UniIndex)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop) :
    Nat → Nat → Array (UniIndex × Nat) → BorrowTree → Prop
  | 0, _, stack, current =>
    if stack.isEmpty then post current else failure (.ParentCycle root) current
  | fuel + 1, steps, stack, current =>
    if stack.isEmpty then post current
    else if steps + 1 > current.nodes.size * 2 + 1 then failure (.ParentCycle root) current
    else
      match stack.back? with
      | none => failure (.EmptyTraversalStack root) current
      | some (index, childPos) =>
        match current.nodes.get index with
        | none => failure (.MissingNode index) current
        | some node =>
          if childPos < node.children.size then
            match node.children[childPos]? with
            | none => failure (.MissingChildPosition index childPos) current
            | some child =>
              collectWalkPre live root post failure fuel (steps + 1)
                ((stack.pop.push (index, childPos + 1)).push (child, 0)) current
          else collectChildrenPre live index
            (collectWalkPre live root post failure fuel (steps + 1) stack.pop) failure
            node.children.toList current #[]

private abbrev CollectWalkProgress := Option TreeGcResult × BorrowTree × Array (UniIndex × Nat) × Nat

/-- The exact continuation for a single root's checked postorder traversal. -/
def collectRootPre (live : Array BorTag) (root : UniIndex) (tree : BorrowTree)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop) : Prop :=
  collectWalkPre live root post failure (tree.nodes.size * 2 + 1) 0 #[(root, 0)] tree

set_option maxHeartbeats 4000000 in
theorem collectRootPre_iff (live : Array BorTag) (root : UniIndex) (tree : BorrowTree)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop) :
    collectRootPre live root tree post failure ↔
      let result := removeUselessChildren tree root live
      match result.outcome with
      | .ok () => post result.tree
      | .error error => failure error result.tree := by
  unfold collectRootPre removeUselessChildren
  simp only [Id.run, bind, pure, ForIn.forIn]
  name_ancestor_loop
  let finish : CollectWalkProgress → Prop := fun result =>
    match result.1 with
    | none => post result.2.1
    | some status => match status.outcome with
      | .ok () => post status.tree
      | .error error => failure error status.tree
  let continueLoop := fun (tree : BorrowTree) (stack : Array (UniIndex × Nat)) (steps : Nat) =>
    finish (Lean.Loop.forIn (m := Id) {} (none, tree, stack, steps) scan)
  have checked (fuel steps : Nat) (stack : Array (UniIndex × Nat)) (current : BorrowTree)
      (bounded : current.nodes.size * 2 + 1 ≤ fuel + steps) :
      collectWalkPre live root post failure fuel steps stack current ↔ continueLoop current stack steps := by
    induction fuel generalizing steps stack current with
    | zero =>
      have past : steps + 1 > current.nodes.size * 2 + 1 := by omega
      unfold continueLoop
      rw [Lean.Loop.forIn_eq_of_monadTail]
      cases empty : stack.isEmpty <;>
        simp only [collectWalkPre, scan, past, empty, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, finish, bind, Bind.bind, pure, Pure.pure]
    | succ fuel ih =>
      unfold continueLoop
      rw [Lean.Loop.forIn_eq_of_monadTail]
      conv in (scan () (none, current, stack, steps)) => unfold scan
      simp only [collectWalkPre]
      cases empty : stack.isEmpty
      · simp only [empty, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        by_cases past : steps + 1 > current.nodes.size * 2 + 1
        · simp only [past, ↓reduceIte, finish, bind, Bind.bind, pure, Pure.pure]
        · simp only [past, ↓reduceIte]
          cases top : stack.back? with
          | none => simp only [top, finish, bind, Bind.bind, pure, Pure.pure]
          | some frame =>
            obtain ⟨index, position⟩ := frame
            simp only [top]
            cases found : current.nodes.get index with
            | none => simp only [found, finish, bind, Bind.bind, pure, Pure.pure]
            | some node =>
              simp only [found]
              by_cases descends : position < node.children.size
              · simp only [descends, ↓reduceIte]
                cases childEq : node.children[position]? with
                | none => simp only [childEq, finish, bind, Bind.bind, pure, Pure.pure]
                | some child =>
                  simpa only [childEq, bind, Bind.bind, pure, Pure.pure, continueLoop] using
                    ih (steps + 1) ((stack.pop.push (index, position + 1)).push (child, 0)) current (by omega)
              · simp only [descends, ↓reduceIte]
                have congruent := collectChildrenPre_congr live index
                  (collectWalkPre live root post failure fuel (steps + 1) stack.pop)
                  (fun next => continueLoop next stack.pop (steps + 1))
                  failure node.children.toList current #[]
                  (fun next same => ih (steps + 1) stack.pop next (by rw [same]; omega))
                refine congruent.trans ?_
                rw [collectChildrenPre_iff]
                with_unfolding_all rw [collectSourceFold_eq live index]
                simp only [Id.run]
                have failed := collectChildFold_error live index node.children.toList current #[]
                generalize (forIn (m := Id) node.children.toList (none, current, #[])
                  (collectChildStep live index)) = progress at failed ⊢
                rcases progress with ⟨returned, after, kept⟩
                cases returned with
                | none =>
                  cases foundAfter : after.nodes.get index with
                  | none => simp only [checkedFinishNode, foundAfter, finish, bind, Bind.bind, pure, Pure.pure]
                  | some node =>
                    simp only [checkedFinishNode, foundAfter, continueLoop, bind, Bind.bind, pure, Pure.pure]
                | some status =>
                  obtain ⟨error, statusEq⟩ := failed status rfl
                  simp only [checkedFinishNode, finish, statusEq, bind, Bind.bind, pure, Pure.pure]
      · simp only [empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte, finish, bind, Bind.bind, pure, Pure.pure]
  refine (checked (tree.nodes.size * 2 + 1) 0 #[(root, 0)] tree (by omega)).trans ?_
  unfold continueLoop
  generalize Lean.Loop.forIn (m := Id) {} (none, tree, #[(root, 0)], 0) scan = result
  rcases result with ⟨returned, current, stack, steps⟩
  cases returned with
  | none => rfl
  | some outcome =>
    cases eq : outcome.outcome <;> simp only [finish, eq]

/-- GC visits roots in order and only merges after every root succeeds. -/
def collectRootsPre (live : Array BorTag) (post : BorrowTree → Prop)
    (failure : TreeGcError → BorrowTree → Prop) : List UniIndex → BorrowTree → Prop
  | [], tree => mergeAfterCollectPre tree post failure
  | root :: rest, tree =>
    collectRootPre live root tree (collectRootsPre live post failure rest) failure

/-- Pull back the continuation across each root's ordered postorder traversal
and the final merge of adjacent compatible location ranges. -/
def collectPre (tree : BorrowTree) (live : Array BorTag)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop) : Prop :=
  collectRootsPre live post failure tree.roots.toList tree

theorem collectPre_iff (tree : BorrowTree) (live : Array BorTag)
    (post : BorrowTree → Prop) (failure : TreeGcError → BorrowTree → Prop) :
    collectPre tree live post failure ↔
      let result := tree.removeUnreachableTags live
      match result.outcome with
      | .error error => failure error result.tree
      | .ok () => post result.tree := by
  unfold collectPre removeUnreachableTags
  simp only [← Array.forIn_toList, Id.run]
  generalize tree.roots.toList = roots
  induction roots generalizing tree with
  | nil =>
    simp only [collectRootsPre, mergeAfterCollectPre, List.forIn_nil, bind, Bind.bind, pure, Pure.pure]
    cases (DedupRangeMap.mergeAdjacentThorough
      (tree.locations.modifyAll fun _ loc => trimLocationForRangeEquality loc)).outcome <;> rfl
  | cons root rest ih =>
    simp only [collectRootsPre, collectRootPre_iff, List.forIn_cons, bind, Bind.bind, pure, Pure.pure]
    cases processed : (removeUselessChildren tree root live).outcome with
    | error => simp only [processed]
    | ok value =>
      cases value
      simpa only [processed, bind, Bind.bind, pure, Pure.pure] using ih (removeUselessChildren tree root live).tree

/-- A permission segment checks its initial state and offset before committing
the range-map mutation, whose partial result survives a failure. -/
def childSegmentPre (positioned : RangeMapSegment Tree.LocationState) (offset : Size)
    (index : UniIndex) (held : Bool) (current : BorrowTree)
    (minimumSifa : IdempotentForeignAccess)
    (next : BorrowTree → IdempotentForeignAccess → Prop)
    (failure : ChildInsertError → BorrowTree → Prop) : Prop :=
  let initial := positioned.data.permission
  if !initial.isInitial then failure (.InsidePermissionNotInitial initial) current
  else
    match initial.strongestIdempotentForeignAccess held with
    | .ImpossibleProtectedReservedIM => failure (.InsidePermissionInvariant initial) current
    | .Access expectedSifa =>
      if positioned.data.idempotentForeignAccess != expectedSifa then
        failure (.InsideSifaMismatch initial) current
      else
        let smallest := weakerSifa minimumSifa positioned.data.idempotentForeignAccess
        match Size.add (Size.ofBytes positioned.range.start) offset with
        | .error error => failure (.SizeError error) current
        | .ok start =>
          let updated := current.locations.modifyRange start
            (Size.ofBytes (positioned.range.stop - positioned.range.start)) fun _ location =>
              { location with perms := location.perms.insert index positioned.data }
          let after := { current with locations := updated.state }
          match updated.outcome with
          | .error error => failure (.RangeMapError error) after
          | .ok () => next after smallest

/-- Pull back through the source ancestor walk. A terminating node still
updates its cached SIFA and materialized locations. The fuel mirrors the
interpreter's checked parent-cycle bound on well-formed and malformed trees. -/
def weakenAncestorPre (start : UniIndex) (strongest : IdempotentForeignAccess)
    (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop) :
    Nat → Nat → Option UniIndex → BorrowTree → Prop
  | 0, _, cursor, current => failure (.ParentCycle (cursor.getD start)) current
  | fuel + 1, steps, cursor, current =>
    if steps > current.nodes.size then failure (.ParentCycle (cursor.getD start)) current
    else
      match cursor with
      | none => post current
      | some index =>
        match current.nodes.get index with
        | none => failure (.MissingNode index) current
        | some node =>
          let next := ZeroProtection.weakened current index node strongest
          if ZeroProtection.changed current index node strongest then
            weakenAncestorPre start strongest post failure fuel (steps + 1) node.parent next
          else post next

def weakenAncestorsPre (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop) : Prop :=
  if strongest == .Write then post tree
  else weakenAncestorPre start strongest post failure (tree.nodes.size + 1) 0 (some start) tree

set_option maxHeartbeats 2500000 in
theorem weakenAncestorsPre_iff (tree : BorrowTree) (start : UniIndex)
    (strongest : IdempotentForeignAccess) (post : BorrowTree → Prop)
    (failure : ChildInsertError → BorrowTree → Prop) :
    weakenAncestorsPre tree start strongest post failure ↔
      let result := updateSifaAfterRetag tree start strongest
      match result.2 with
      | .error error => failure error result.1
      | .ok () => post result.1 := by
  unfold weakenAncestorsPre updateSifaAfterRetag
  split
  · rfl
  · simp only [Id.run, bind, pure, ForIn.forIn]
    name_ancestor_loop
    let finish : ZeroProtection.LoopState → Prop := fun result =>
      match result.1 with
      | none => post result.2.1
      | some (after, .ok ()) => post after
      | some (after, .error error) => failure error after
    have inactive (current : BorrowTree) (cursor : Option UniIndex) (steps : Nat) :
        finish (Lean.Loop.forIn (m := Id) {} (none, current, cursor, steps, false) scan) ↔ post current := by
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rfl
    have exactLoop (fuel steps : Nat) (cursor : Option UniIndex) (current : BorrowTree)
        (bounded : current.nodes.size + 1 ≤ fuel + steps) :
        weakenAncestorPre start strongest post failure fuel steps cursor current ↔
          finish (Lean.Loop.forIn (m := Id) {} (none, current, cursor, steps, true) scan) := by
      induction fuel generalizing steps cursor current with
      | zero =>
        have past : steps > current.nodes.size := by omega
        rw [Lean.Loop.forIn_eq_of_monadTail]
        simp only [weakenAncestorPre, scan, past, ↓reduceIte, bind, Bind.bind, pure, Pure.pure, finish]
      | succ fuel ih =>
        rw [Lean.Loop.forIn_eq_of_monadTail]
        by_cases past : steps > current.nodes.size
        · simp only [weakenAncestorPre, scan, past, ↓reduceIte, bind, Bind.bind, pure, Pure.pure, finish]
        · cases cursor with
          | none =>
            simpa only [weakenAncestorPre, scan, past, ↓reduceIte, bind, Bind.bind, pure, Pure.pure]
              using (inactive current none steps).symm
          | some index =>
            cases found : current.nodes.get index with
            | none =>
              simp only [weakenAncestorPre, scan, past, found, ↓reduceIte,
                bind, Bind.bind, pure, Pure.pure, finish]
            | some node =>
              let next := ZeroProtection.weakened current index node strongest
              have nextSize : next.nodes.size = current.nodes.size :=
                ZeroProtection.insert_existing_size current.nodes index node _ found
              have casesEq : scan () (none, current, some index, steps, true) =
                  if ZeroProtection.changed current index node strongest then
                    .yield (none, next, node.parent, steps + 1, true)
                  else .yield (none, next, some index, steps, false) := by
                simp only [scan, ite_eq_left rfl, ite_eq_right past, found]
                change (if ZeroProtection.changed current index node strongest then _ else _) = _
                rfl
              rw [casesEq]
              simp only [weakenAncestorPre, past, ↓reduceIte, found]
              cases changed : ZeroProtection.changed current index node strongest
              · simpa only [changed, Bool.false_eq_true, ↓reduceIte, bind, Bind.bind]
                  using (inactive next (some index) steps).symm
              · simpa only [changed, ↓reduceIte, bind, Bind.bind]
                  using ih (steps + 1) node.parent next (by rw [nextSize]; omega)
    have checked := exactLoop (tree.nodes.size + 1) 0 (some start) tree (by omega)
    refine checked.trans ?_
    generalize Lean.Loop.forIn (m := Id) {} (none, tree, some start, 0, true) scan = result
    rcases result with ⟨returned, current, cursor, steps, active⟩
    cases returned with
    | none => rfl
    | some outcome =>
      rcases outcome with ⟨after, status⟩
      cases status <;> rfl

def finishChildPre (parent : Option UniIndex) (tree : BorrowTree)
    (minimumSifa : IdempotentForeignAccess) (post : BorrowTree → Prop)
    (failure : ChildInsertError → BorrowTree → Prop) : Prop :=
  match parent with
  | none => post tree
  | some parent => weakenAncestorsPre tree parent minimumSifa post failure

def childSegmentsPre (offset : Size) (index : UniIndex) (parent : Option UniIndex)
    (held : Bool) (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop) :
    List (RangeMapSegment Tree.LocationState) → BorrowTree → IdempotentForeignAccess → Prop
  | [], now, minimum => finishChildPre parent now minimum post failure
  | segment :: rest, now, minimum =>
    childSegmentPre segment offset index held now minimum
      (childSegmentsPre offset index parent held post failure rest) failure

def finishInsertedChildPre (tree : BorrowTree) (offset : Size) (parent : Option UniIndex)
    (tag : BorTag) (index : UniIndex) (inside : DedupRangeMap Tree.LocationState)
    (outside : Permission) (held : Bool) (defaultSifa : IdempotentForeignAccess)
    (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop) : Prop :=
  let node : TreeNode := {
    tag
    parent
    children := #[]
    defaultInitialPermission := outside
    defaultInitialSifa := defaultSifa
    isExposed := false
  }
  let inserted := { tree with nodes := tree.nodes.insert index node }
  let run := fun ready => childSegmentsPre offset index parent held post failure
    inside.iterAll.toList ready defaultSifa
  match parent with
  | none => run { inserted with roots := inserted.roots.push index }
  | some parent =>
    match inserted.nodes.get parent with
    | none => failure (.MissingNode parent) inserted
    | some parentNode =>
      let updatedParent := { parentNode with children := parentNode.children.push index }
      run { inserted with nodes := inserted.nodes.insert parent updatedParent }

/-- Pull back the continuation through mapping insertion and parent lookup
before checking permissions and committing the node and its ranges. -/
def insertChildPre (tree : BorrowTree) (offset : Size) (provenance : ProvenanceExtra)
    (tag : BorTag) (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop) : Prop :=
  match tree.tagMapping.insert tag with
  | .DuplicateKeyAfterReplacement mapping _ =>
    failure (.DuplicateTag tag) { tree with tagMapping := mapping }
  | .Error mapping _ =>
    failure (.TagIndexExhausted mapping.size) { tree with tagMapping := mapping }
  | .Inserted mapping index =>
    let current := { tree with tagMapping := mapping }
    let parent := match provenance with
      | .wildcard => some none
      | .concrete parent => (tree.tagMapping.get parent).map some
    match parent with
    | none =>
      let name := match provenance with
        | .concrete parent => parent
        | .wildcard => tag
      failure (.MissingParentTag name) current
    | some parent =>
      if !outside.isInitial then failure (.OutsidePermissionNotInitial outside) current
      else if outside.isUnique then failure .OutsideUniquePermission current
      else
        match outside.strongestIdempotentForeignAccess held with
        | .ImpossibleProtectedReservedIM => failure .ProtectedReservedIM current
        | .Access defaultSifa =>
          finishInsertedChildPre current offset parent tag index inside outside held defaultSifa post failure

private def insertChildSegments (offset : Size) (index : UniIndex) (parent : Option UniIndex)
    (held : Bool) (segments : List (RangeMapSegment Tree.LocationState))
    (current : BorrowTree) (minimumSifa : IdempotentForeignAccess) : ChildInsertResult := Id.run do
  let mut current := current
  let mut minimumSifa := minimumSifa
  for segment in segments do
    let initial := segment.data.permission
    if !initial.isInitial then
      return { tree := current, outcome := .error (.InsidePermissionNotInitial initial) }
    let expectedSifa := match initial.strongestIdempotentForeignAccess held with
      | .Access sifa => some sifa
      | .ImpossibleProtectedReservedIM => none
    let some expectedSifa := expectedSifa
      | return { tree := current, outcome := .error (.InsidePermissionInvariant initial) }
    if segment.data.idempotentForeignAccess != expectedSifa then
      return { tree := current, outcome := .error (.InsideSifaMismatch initial) }
    minimumSifa := weakerSifa minimumSifa segment.data.idempotentForeignAccess
    let start ← match Size.add (Size.ofBytes segment.range.start) offset with
      | .ok start => pure start
      | .error error =>
        return { tree := current, outcome := .error (.SizeError error) }
    let rangeUpdate := current.locations.modifyRange start
      (Size.ofBytes (segment.range.stop - segment.range.start)) fun _ location =>
        { location with perms := location.perms.insert index segment.data }
    current := { current with locations := rangeUpdate.state }
    match rangeUpdate.outcome with
    | .error error => return { tree := current, outcome := .error (.RangeMapError error) }
    | .ok () => pure ()
  match parent with
  | none => return { tree := current, outcome := .ok () }
  | some parent =>
    let (updated, outcome) := updateSifaAfterRetag current parent minimumSifa
    return { tree := updated, outcome }

def childResultPre (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop)
    (result : ChildInsertResult) : Prop :=
  match result.outcome with
  | .error error => failure error result.tree
  | .ok () => post result.tree

private theorem childSegmentsPre_iff (offset : Size) (index : UniIndex) (parent : Option UniIndex)
    (held : Bool) (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop)
    (segments : List (RangeMapSegment Tree.LocationState)) (tree : BorrowTree)
    (minimumSifa : IdempotentForeignAccess) :
    childSegmentsPre offset index parent held post failure segments tree minimumSifa ↔
      childResultPre post failure (insertChildSegments offset index parent held segments tree minimumSifa) := by
  induction segments generalizing tree minimumSifa with
  | nil =>
    simp only [childSegmentsPre, insertChildSegments, finishChildPre, List.forIn_nil,
      bind, Bind.bind, Id.run, pure, Pure.pure]
    cases parent with
    | none => rfl
    | some parent =>
      simpa only [childResultPre] using weakenAncestorsPre_iff tree parent minimumSifa post failure
  | cons segment rest ih =>
    simp only [childSegmentsPre, childSegmentPre, insertChildSegments, List.forIn_cons,
      bind, Bind.bind, Id.run, pure, Pure.pure]
    cases initial : segment.data.permission.isInitial
    · simp only [initial, Bool.not_false, ↓reduceIte]
      rfl
    · simp only [initial, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases expected : segment.data.permission.strongestIdempotentForeignAccess held with
      | ImpossibleProtectedReservedIM =>
        simp only [expected]
        rfl
      | Access expectedSifa =>
        simp only [expected]
        split
        · simp_all only [↓reduceIte]
          rfl
        · simp_all only [↓reduceIte]
          cases shifted : Size.add (Size.ofBytes segment.range.start) offset with
          | error =>
            simp only [shifted]
            rfl
          | ok start =>
            simp only [shifted]
            let update := tree.locations.modifyRange start
              (Size.ofBytes (segment.range.stop - segment.range.start)) fun _ location =>
                { location with perms := location.perms.insert index segment.data }
            cases result : update.outcome with
            | error =>
              simp only [update] at result
              simp only [result]
              rfl
            | ok value =>
              cases value
              simp only [update] at result
              simpa only [result, insertChildSegments, bind, Bind.bind, Id.run, pure, Pure.pure] using
                ih { tree with locations := update.state }
                  (weakerSifa minimumSifa segment.data.idempotentForeignAccess)

theorem insertChildPre_iff (tree : BorrowTree) (offset : Size) (provenance : ProvenanceExtra)
    (tag : BorTag) (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (post : BorrowTree → Prop) (failure : ChildInsertError → BorrowTree → Prop) :
    insertChildPre tree offset provenance tag inside outside held post failure ↔
      childResultPre post failure (tree.newChild offset provenance tag inside outside held) := by
  unfold insertChildPre newChild
  cases mapped : tree.tagMapping.insert tag with
  | DuplicateKeyAfterReplacement => rfl
  | Error => rfl
  | Inserted mapping index =>
    simp only [Id.run, pure, Pure.pure]
    generalize (match provenance with
      | .wildcard => some none
      | .concrete parent => (tree.tagMapping.get parent).map some) = matched
    cases matched with
    | none => rfl
    | some parent =>
      cases initialized : outside.isInitial
      · simp only [initialized, Bool.not_false, ↓reduceIte]
        rfl
      · simp only [initialized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases unique : outside.isUnique
        · simp only [unique, Bool.false_eq_true, ↓reduceIte]
          cases sifa : outside.strongestIdempotentForeignAccess held with
          | ImpossibleProtectedReservedIM =>
            simp only [sifa]
            rfl
          | Access defaultSifa =>
            simp only [sifa, finishInsertedChildPre]
            cases parent with
            | none =>
              simpa only [insertChildSegments, ← Array.forIn_toList, Id.run, pure, Pure.pure,
                bind, Bind.bind] using childSegmentsPre_iff offset index none held post failure
                  inside.iterAll.toList _ defaultSifa
            | some parent =>
              dsimp only
              let nodes := tree.nodes.insert index {
                tag, parent := some parent, defaultInitialPermission := outside,
                defaultInitialSifa := defaultSifa
              }
              cases found : nodes.get parent with
              | none =>
                simp only [nodes] at found
                simp only [found]
                rfl
              | some parentNode =>
                simp only [nodes] at found
                simp only [found]
                simpa only [insertChildSegments, ← Array.forIn_toList, Id.run, pure, Pure.pure,
                  bind, Bind.bind] using childSegmentsPre_iff offset index (some parent) held post failure
                    inside.iterAll.toList _ defaultSifa
        · simp only [unique, ↓reduceIte]
          rfl

end Miri.TreeBorrows.BorrowTree.MutationVerification
