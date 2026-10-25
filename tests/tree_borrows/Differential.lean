import Miri.TreeBorrows.Permissions
import Miri.TreeBorrows.LocationState
import Miri.TreeBorrows.Traversal
import Miri.TreeBorrows.NormalTree
import Miri.TreeBorrows.RangedNormalTree
import Miri.TreeBorrows.GlobalState
import Miri.TreeBorrows.TreeState
import Miri.TreeBorrows.RetagPolicy
import Miri.TreeBorrows.RetagPipeline
import Miri.DataStructures.DedupRangeMap
import Miri.ABI.Size
import Miri.Memory.Identity

open Miri.TreeBorrows
open Miri.ABI
open Miri.DataStructures
open Miri.Memory

private def permissions : List Permission :=
  [.Cell, .ReservedFrz false, .ReservedFrz true, .ReservedIM,
    .Unique, .Frozen, .Disabled]

private def kinds : List AccessKind := [.Read, .Write]
private def relatednesses : List AccessRelatedness := [.LocalAccess, .ForeignAccess]
private def idempotentAccesses : List IdempotentForeignAccess := [.None, .Read, .Write]
private def wildcardLevels : List WildcardAccessLevel := [.None, .Read, .Write]

private def permissionCode : Permission → String
  | .Cell => "c"
  | .ReservedFrz false => "r0"
  | .ReservedFrz true => "r1"
  | .ReservedIM => "ri"
  | .Unique => "u"
  | .Frozen => "f"
  | .Disabled => "d"

private def kindCode : AccessKind → String
  | .Read => "r"
  | .Write => "w"

private def relatednessCode : AccessRelatedness → String
  | .LocalAccess => "l"
  | .ForeignAccess => "x"

private def accessCode : Option AccessKind → String
  | none => "none"
  | some .Read => "r"
  | some .Write => "w"

private def idempotentCode : IdempotentForeignAccess → String
  | .None => "n"
  | .Read => "r"
  | .Write => "w"

private def wildcardCode : WildcardAccessLevel → String
  | .None => "n"
  | .Read => "r"
  | .Write => "w"

private def boolCode (value : Bool) : String := if value then "true" else "false"

private def orderingCode : PermissionOrdering → String
  | .Incomparable => "incomparable"
  | .Less => "less"
  | .Equal => "equal"
  | .Greater => "greater"

private def skipResultCode : IdempotentForeignAccess.SkipCheckResult → String
  | .Decision canSkip => boolCode canSkip
  | .DebugAssertion => "assert"

private def accessOutcomeCode : AccessOutcome → String
  | .Transition permission => s!"s:{permissionCode permission}"
  | .UndefinedBehavior => "ub"
  | .ImpossibleProtectedReservedIM => "assert"

private def transitionOutcomeCode : PermTransitionOutcome → String
  | .Transition transition =>
      let applied := permissions.map fun start =>
        match transition.applied start with
        | none => "-"
        | some next => permissionCode next
      let appliedCode := String.intercalate "," applied ++ ","
      let next := permissionCode transition.endpoint
      s!"s:{next}:{boolCode transition.isNoop}:{boolCode transition.producesDisabled}:{boolCode transition.isPossible}:{appliedCode}"
  | .UndefinedBehavior => "ub"
  | .ImpossibleProtectedReservedIM => "assert"

private def locationStateCode (state : Tree.LocationState) : String :=
  s!"{permissionCode state.permission} {boolCode state.accessed} {idempotentCode state.idempotentForeignAccess} {boolCode state.possible}"

private def continueTraversalCode : Tree.ContinueTraversal → String
  | .Recurse => "recurse"
  | .SkipSelfAndChildren => "skip"

private def locationAccessOutcomeCode : Tree.LocationState.AccessResult → String
  | .Success _ transition =>
      s!"ok:{permissionCode transition.toPermission}:{boolCode transition.isNoop}:{boolCode transition.producesDisabled}:{boolCode transition.isPossible}"
  | .Error _ (.ChildAccessForbidden permission) =>
      s!"child-forbidden:{permissionCode permission}"
  | .Error _ (.ProtectedDisabled permission) =>
      s!"protected-disabled:{permissionCode permission}"
  | .Error _ .ProtectedDealloc => "protected-dealloc"
  | .PermissionInvariantFailure _
  | .TransitionApplicationInvariantFailure _
  | .PossibleInvariantFailure _ => "assert"

private def traversalTrees : List (String × Tree.TraversalTree) :=
  [
    ("chain3", ⟨#[
      ⟨none, [1]⟩,
      ⟨some 0, [2]⟩,
      ⟨some 1, []⟩
    ]⟩),
    ("branch6", ⟨#[
      ⟨none, [1, 2]⟩,
      ⟨some 0, [3, 4]⟩,
      ⟨some 0, [5]⟩,
      ⟨some 1, []⟩,
      ⟨some 1, []⟩,
      ⟨some 2, []⟩
    ]⟩)
  ]

private def traversalEventsCode (events : List Tree.TraversalEvent) : String :=
  String.intercalate "," (events.map fun event =>
    s!"{event.node}{relatednessCode event.relatedness}")

private def accessErrorCode (error : Diagnostics.TransitionError) : String :=
  match error with
  | .ChildAccessForbidden _ => "child-forbidden"
  | .ProtectedDisabled _ => "protected-disabled"
  | .ProtectedDealloc => "protected-dealloc"

private def normalStatusCode (status : Tree.NormalAccessStatus) : String :=
  match status with
  | .Completed => "completed"
  | .TransitionError node error => s!"{accessErrorCode error}-{node}"
  | .RecordDebugAssertion node => s!"record-assert-{node}"
  | .PermissionInvariantFailure node => s!"permission-assert-{node}"
  | .TransitionApplicationInvariantFailure node => s!"transition-assert-{node}"
  | .PossibleInvariantFailure node => s!"possible-assert-{node}"
  | .MissingLocationState node => s!"missing-{node}"

private def normalStatesCode (states : Array (Option Tree.LocationState)) : String :=
  String.intercalate "|" (states.toList.map fun state =>
    match state with
    | none => "-"
    | some state => locationStateCode state)

private def branchTopology : Tree.TraversalTree := ⟨#[
  ⟨none, [1, 2]⟩,
  ⟨some 0, [3, 4]⟩,
  ⟨some 0, [5]⟩,
  ⟨some 1, []⟩,
  ⟨some 1, []⟩,
  ⟨some 2, []⟩
]⟩

private def branchDefaults : Array Tree.LocationState := #[
  ⟨.Unique, true, .None⟩,
  ⟨.ReservedFrz false, false, .None⟩,
  ⟨.ReservedFrz false, false, .None⟩,
  ⟨.ReservedFrz false, false, .None⟩,
  ⟨.ReservedFrz false, false, .None⟩,
  ⟨.ReservedFrz false, false, .None⟩
]

private def retagTestAllocId : AllocId := ⟨11, by decide⟩
private def retagTestParentTag : BorTag := ⟨2, by decide⟩

private def retagTestMachineState : Except AllocError (RetagPipeline.MachineState Unit) := do
  let allocation ← Allocation.fromBytes #[0] Align.ONE .Mut
  let tree := BorrowTree.new retagTestParentTag (Size.ofBytes 1)
  let allocation := allocation.withExtra tree
  let localAlloc : LocalAllocation Provenance BorrowTree Unit := ⟨.stack, allocation⟩
  let memory0 : MemoryState Provenance BorrowTree Unit := MemoryState.empty
  let issued := MemoryState.setIssuedIds memory0 #[retagTestAllocId]
  let memory := {issued with live := #[(retagTestAllocId, localAlloc)]}
  return ⟨memory, GlobalState.new, {}⟩

private def retagTestRequest (hooks : RetagPipeline.Hooks := {}) : RetagPipeline.Request := {
  typeShape := .reference
  typeFacts := ⟨true, true, true⟩
  referenceKind := .Mutable
  mode := .FnEntry
  config := ⟨false, false⟩
  layoutSize := Size.ofBytes 1
  originalProvenance := some (.concrete retagTestAllocId retagTestParentTag)
  pointeeIsFreeze := true
  preciseInteriorMut := false
  hooks := { hooks with allocationResolution := some ⟨retagTestAllocId,
    Size.ZERO, .concrete retagTestParentTag⟩ }
}

private def requireRetagCheck (holds : Bool) (message : String) : IO Unit := do
  if !holds then throw (IO.userError message)

private def runRetagPipelineChecks : IO Unit := do
  let globalPriority := { RetagPipeline.RetagTypeShape.globalBox with
    isReference := true, isRawPointer := true }
  let referencePriority := { RetagPipeline.RetagTypeShape.reference with
    isRawPointer := true, isBox := true }
  let rawPriority := { RetagPipeline.RetagTypeShape.rawPointer with isBox := true }
  requireRetagCheck (globalPriority.classify == .globalBox &&
      referencePriority.classify == .reference && rawPriority.classify == .rawPointer &&
      RetagPipeline.RetagTypeShape.customAllocatorBox.classify == .customAllocatorBox &&
      RetagPipeline.RetagTypeShape.invalid.classify == .invalidType)
    "retag type classification must preserve the pinned guard priority"
  let initial ← match retagTestMachineState with
    | .ok state => pure state
    | .error error => throw (IO.userError s!"test allocation construction failed: {error}")
  let request := retagTestRequest

  let sizeFailure := RetagPipeline.retagPointerValue initial
    { request with hooks := { request.hooks with sizeAndAlignOfValue := .error "size" } }
  let sizeStoppedBeforeTag := match sizeFailure.outcome with
    | .error (.sizeQuery _) => sizeFailure.state.global.nextPointerTag == BorTag.one
    | _ => false
  requireRetagCheck sizeStoppedBeforeTag
    "retag size-query failure must precede pointer-tag allocation"

  let accessFailure := RetagPipeline.retagPointerValue initial
    { request with hooks := { request.hooks with pointerAccess := .error "bounds" } }
  let accessStoppedAfterTag := match accessFailure.outcome with
    | .error (.pointerAccess _) =>
        accessFailure.state.global.nextPointerTag.value == 2 &&
          !(accessFailure.events.any fun event => match event with
            | .allocationResolution _ => true
            | _ => false)
    | _ => false
  requireRetagCheck accessStoppedAfterTag
    "retag pointer-access failure must consume the tag before allocation resolution"

  let rawRequest := { request with typeShape := .rawPointer, mode := .Raw }
  let rawResult := RetagPipeline.retagPointerValue initial rawRequest
  requireRetagCheck (rawResult.outcome == .ok none &&
      rawResult.state.global.nextPointerTag == BorTag.one)
    "raw pointer retag must return before place conversion and tag allocation"

  let raceFailure := RetagPipeline.retagPointerValue initial
    { request with hooks := { request.hooks with dataRace := some #[.error "race"] } }
  let raceTree := match raceFailure.state.memory.live[0]? with
    | some (_, localAlloc) => localAlloc.allocation.extra
    | none => BorrowTree.new retagTestParentTag (Size.ofBytes 1)
  let racePreservedProtector := match raceFailure.outcome with
    | .error (.dataRace _) =>
        raceFailure.state.global.protectedTags.get BorTag.one == some .StrongProtector &&
          raceFailure.state.frame.protectedTags.contains (retagTestAllocId, BorTag.one) &&
          (raceTree.indexOfTag BorTag.one).isNone
    | _ => false
  requireRetagCheck racePreservedProtector
    "data-race failure must retain protector registration and precede child insertion"

  let successful := RetagPipeline.retagPointerValue initial request
  let successTree := match successful.state.memory.live[0]? with
    | some (_, localAlloc) => localAlloc.allocation.extra
    | none => BorrowTree.new retagTestParentTag (Size.ofBytes 1)
  let successUpdatedExtra := successful.outcome ==
      .ok (some (.concrete retagTestAllocId BorTag.one)) &&
    (successTree.indexOfTag BorTag.one).isSome &&
    successful.state.global.protectedTags.get BorTag.one == some .StrongProtector &&
    successful.state.frame.protectedTags.contains (retagTestAllocId, BorTag.one) &&
    successful.events.any fun event => event == .retaggedValueReconstructed
  requireRetagCheck successUpdatedExtra
    "successful retag must insert its child into the live allocation extra and finish the value"

private def normalTreeFixture (states : Array (Option Tree.LocationState))
    (protectedNodes : List Nat) : Tree.NormalTreeState := {
  topology := branchTopology
  defaultStates := branchDefaults
  protectedNodes := protectedNodes
  locationStates := states
}

private def emptyBranchStates : Array (Option Tree.LocationState) :=
  #[none, none, none, none, none, none]

private def normalTreeFixtures : List
    (String × Tree.NormalTreeState × Nat × AccessKind × Tree.ChildrenVisitMode) :=
  let frozen : Tree.LocationState := ⟨.Frozen, true, .None⟩
  let unique : Tree.LocationState := ⟨.Unique, true, .None⟩
  let childForbidden := #[none, some frozen, none, none, none, none]
  let protectedDisabled := #[none, none, none, none, some unique, none]
  let skippedFrozen := #[none, none, some frozen, none, none, none]
  [
    ("child-forbidden", normalTreeFixture childForbidden [], 3, .Write,
      .VisitChildrenOfAccessed),
    ("protected-disabled", normalTreeFixture protectedDisabled [4], 3, .Write,
      .VisitChildrenOfAccessed),
    ("latent-disabled", normalTreeFixture emptyBranchStates [4], 3, .Write,
      .VisitChildrenOfAccessed),
    ("skip-frozen-read", normalTreeFixture skippedFrozen [], 3, .Read,
      .VisitChildrenOfAccessed)
  ]

private def rangedAccessStatusCode (status : Tree.RangedAccessStatus) : String :=
  match status with
  | .Completed => "completed"
  | .RangeMapFailure _ => "range-map-error"
  | .LocationMapFailure _ _ => "location-map-error"
  | .AccessFailure range status =>
      s!"access-failure:{range.start}:{range.stop}:{normalStatusCode status}"

private def rangedLocationResultsCode (results : Array Tree.RangedLocationResult) : String :=
  String.intercalate "|" (results.toList.map fun item =>
    s!"{item.range.start}:{item.range.stop}:{item.result.root}:{normalStatusCode item.result.status}:{traversalEventsCode item.result.visited}:{normalStatesCode item.result.tree.locationStates}")

private def rangedMapCode (map : DedupRangeMap (Array (Option Tree.LocationState))) : String :=
  String.intercalate "|" (map.iterAll.toList.map fun segment =>
    s!"{segment.range.start}:{segment.range.stop}={normalStatesCode segment.data}")

private def wildcardRelatednessCode : Option WildcardAccessRelatedness → String
  | none => "None"
  | some .LocalAccess => "Some(LocalAccess)"
  | some .ForeignAccess => "Some(ForeignAccess)"
  | some .EitherAccess => "Some(EitherAccess)"

private def sourcePermissionName : Permission → String
  | .Cell => "Cell"
  | .ReservedFrz false => "ReservedFrz(false)"
  | .ReservedFrz true => "ReservedFrz(true)"
  | .ReservedIM => "ReservedIM"
  | .Unique => "Unique"
  | .Frozen => "Frozen"
  | .Disabled => "Disabled"

private def sourceSifaName : IdempotentForeignAccess → String
  | .None => "None"
  | .Read => "Read"
  | .Write => "Write"

private def retagPermissionCode : RetagPolicy.NewPermission → String
  | policy =>
      let protector := match policy.protector with
        | none => "none"
        | some .WeakProtector => "weak"
        | some .StrongProtector => "strong"
      s!"Some({sourcePermissionName policy.freezePermission},{sourcePermissionName policy.nonfreezePermission},{sourcePermissionName policy.outsidePermission},{protector})"

private def emitRetagPolicyRows : IO Unit := do
  let modes := [RetagPolicy.RetagMode.None, .Default, .TwoPhase, .FnEntry, .Raw]
  let kinds := [
    ("shared", RetagPolicy.ReferenceKind.Shared),
    ("mutable", RetagPolicy.ReferenceKind.Mutable),
    ("box", RetagPolicy.ReferenceKind.Box),
  ]
  for mode in modes do
    let modeName := match mode with
      | .None => "none"
      | .Default => "default"
      | .TwoPhase => "two-phase"
      | .FnEntry => "fn-entry"
      | .Raw => "raw"
    for (kindName, kind) in kinds do
      for isUnpin in [false, true] do
        for isUnsafeUnpin in [false, true] do
          for isFreeze in [false, true] do
            for implicitWrites in [false, true] do
              for rustcNoWritable in [false, true] do
                let facts : RetagPolicy.TypeFacts := ⟨isUnpin, isUnsafeUnpin, isFreeze⟩
                let config : RetagPolicy.PolicyConfig := ⟨implicitWrites, rustcNoWritable⟩
                let output := match RetagPolicy.create facts kind mode config with
                  | none => "none"
                  | some permission => retagPermissionCode permission
                IO.println s!"retag-policy {modeName} {kindName} {isUnpin} {isUnsafeUnpin} {isFreeze} {implicitWrites} {rustcNoWritable} {output}"

private def wildcardStatusCode : BorrowTree.WildcardAccessStatus → String
  | .Completed => "ok"
  | .EmptyTraversalStack _ => "tree-borrows-transition-error"
  | .NoValidExposedReferences _ _ => "no-valid-exposed-references"
  | .MissingNode _ => "tree-borrows-transition-error"
  | .RecordDebugAssertion _ => "tree-borrows-transition-error"
  | .TransitionError _ _ => "tree-borrows-transition-error"
  | .CacheFailure _ => "tree-borrows-transition-error"
  | .PermissionInvariantFailure _ => "tree-borrows-transition-error"
  | .TransitionApplicationInvariantFailure _ => "tree-borrows-transition-error"
  | .PossibleInvariantFailure _ => "tree-borrows-transition-error"
  | .ParentCycle _ => "tree-borrows-transition-error"

private def wildcardFixtureNode (tag : BorTag) (parent : Option Nat)
    (children : Array Nat) (permission : Permission) (exposed : Bool) : TreeNode := {
  tag
  parent := parent.map fun index => ⟨UInt32.ofNat index⟩
  children := children.map fun index => ⟨UInt32.ofNat index⟩
  defaultInitialPermission := permission
  defaultInitialSifa := .None
  isExposed := exposed
}

private def wildcardFixtureTree (nodes : Array (Option TreeNode))
    (tags : Array BorTag) (roots : Array UniIndex := #[⟨0⟩]) : BorrowTree := {
  tagMapping := {
    mapping := tags.mapIdx fun index tag => (tag, ⟨UInt32.ofNat index⟩)
    deassigned := #[]
  }
  nodes := ⟨nodes⟩
  locations := DedupRangeMap.new Size.ZERO {}
  roots
}

private def wildcardFixtureLocation (tree : BorrowTree)
    (states : Array (Nat × Tree.LocationState))
    (exposures : Array (Nat × WildcardAccessLevel)) : LocationTree := Id.run do
  let mut perms : UniValMap Tree.LocationState := {}
  for (index, state) in states do
    perms := perms.insert ⟨UInt32.ofNat index⟩ state
  let mut cache : ExposedCache := {}
  for (index, level) in exposures do
    let update := cache.updateExposure tree.nodes ⟨UInt32.ofNat index⟩ .None level
    cache := update.cache
  return { perms, exposedCache := cache }

private def wildcardLocationCode (tree : BorrowTree) (location : LocationTree) : String :=
  String.intercalate "|" ((List.range tree.nodes.size).map fun index =>
    match tree.locationStateAt location ⟨UInt32.ofNat index⟩ with
    | none => "-"
    | some state => locationStateCode state)

private def emitWildcardFixture (name : String) (tree : BorrowTree)
    (location : LocationTree) (kind : AccessKind) (isWildcardTree : Bool) : IO Unit := do
  let result := tree.performWildcardAccessAt location ⟨0⟩ none kind {} isWildcardTree
  IO.println s!"wild-access {name} {wildcardStatusCode result.status} {wildcardLocationCode tree result.location}"

private def emitMultiRootFixture (name : String) (tree : BorrowTree)
    (location : LocationTree) (provenance : ProvenanceExtra) (kind : AccessKind) : IO Unit := do
  let tree := { tree with locations := DedupRangeMap.new (Size.ofBytes 1) location }
  let result := tree.performBorrowAccessRange provenance (Size.ofBytes 0) (Size.ofBytes 1)
    kind {} .VisitChildrenOfAccessed
  let status := match result.status with
    | BorrowTree.BorrowTreeAccessStatus.Completed => "ok"
    | BorrowTree.BorrowTreeAccessStatus.AccessFailure _ _
    | BorrowTree.BorrowTreeAccessStatus.WildcardFailure _ _ =>
        "tree-borrows-transition-error"
    | _ => "tree-borrows-transition-error"
  let location := (result.tree.locations.iterAll[0]?.map fun segment => segment.data).getD {}
  IO.println s!"multi-root {name} {status} {wildcardLocationCode result.tree location}"

private def lifecycleFixtureTree (rootPermission childPermission : Permission)
    (rootState : Tree.LocationState) (childState : Option Tree.LocationState)
    (childExposed : Bool := false) : BorrowTree := Id.run do
  let base := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[1] rootPermission false)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) (some 0) #[] childPermission childExposed)]
    #[BorTag.one, ⟨2, by decide⟩]
  let states := match childState with
    | none => #[(0, rootState)]
    | some child => #[(0, rootState), (1, child)]
  let location := wildcardFixtureLocation base states #[]
  return { base with locations := DedupRangeMap.new (Size.ofBytes 1) location }

private def emitLifecycleFixtures : IO Unit := do
  let releaseTree := lifecycleFixtureTree .Disabled (.ReservedFrz false)
    ⟨.Unique, true, .None⟩ (some ⟨.ReservedFrz true, true, .Read⟩) true
  let releaseTree := { releaseTree with
    locations := DedupRangeMap.new (Size.ofBytes 1)
      (wildcardFixtureLocation releaseTree #[(0, ⟨.Unique, true, .None⟩),
        (1, ⟨.ReservedFrz true, true, .Read⟩)] #[(1, .Read)]) }
  let protectors := ProtectedTags.insert {} (⟨2, by decide⟩ : BorTag) .StrongProtector
  let beforeLocation := releaseTree.locations.iterAll[0]?.map (·.data)
    |>.getD (default : LocationTree)
  let beforeCache := wildcardRelatednessCode
    (ExposedCache.accessRelatedness beforeLocation.exposedCache ⟨0⟩ ⟨1⟩ .Write false false)
  let released := releaseTree.releaseProtector (⟨2, by decide⟩ : BorTag) protectors
  let releaseStatus := match released.status with
    | BorrowTree.ProtectorReleaseStatus.Released => "ok"
    | _ => "tree-borrows-transition-error"
  let releaseLocation := (released.tree.locations.iterAll[0]?.map fun segment => segment.data).getD {}
  let afterCache := wildcardRelatednessCode
    (ExposedCache.accessRelatedness releaseLocation.exposedCache ⟨0⟩ ⟨1⟩ .Write false false)
  IO.println s!"protector-release skip-children {releaseStatus} {wildcardLocationCode released.tree releaseLocation} {beforeCache} {afterCache}"

  for (name, permission) in [("strong-write", Permission.Unique), ("cell-exempt", Permission.Cell)] do
    let tree := lifecycleFixtureTree .Disabled (.ReservedFrz false)
      ⟨permission, true, .None⟩ none
    let protectors := ProtectedTags.insert {} BorTag.one .StrongProtector
    let result := tree.deallocateBorrowRange (.concrete BorTag.one)
      (Size.ofBytes 0) (Size.ofBytes 1) protectors
    let status := match result.status with
      | BorrowTree.BorrowTreeDeallocStatus.Deallocated => "ok"
      | _ => "tree-borrows-transition-error"
    IO.println s!"dealloc {name} {status}"

private def emitGcFixtures : IO Unit := do
  let leafTree := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[1] .Disabled false)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) (some 0) #[] .Frozen false)]
    #[BorTag.one, ⟨2, by decide⟩]
  let rootState : Tree.LocationState := ⟨.Unique, true, .None⟩
  let leafState : Tree.LocationState := ⟨.Frozen, false, .Read⟩
  let firstLocation := wildcardFixtureLocation leafTree #[(0, rootState), (1, leafState)] #[]
  let secondLocation := wildcardFixtureLocation leafTree #[(0, rootState)] #[]
  let initialMap := DedupRangeMap.new (Size.ofBytes 2) firstLocation
  let split := initialMap.iterMut (Size.ofBytes 1) (Size.ofBytes 1)
  let secondUpdate := split.state.setAtPos 1 secondLocation
  let leafTree := { leafTree with locations := secondUpdate.state }
  let deadLeaf := leafTree.removeUnreachableTags #[BorTag.one]
  let hasLeaf := (deadLeaf.tree.nodes.get ⟨1⟩).isSome
  let rootChildren := (deadLeaf.tree.nodes.get ⟨0⟩).map (·.children.size) |>.getD 0
  let rangeCount := deadLeaf.tree.locations.iterAll.size
  let hasLeafTag := (deadLeaf.tree.tagMapping.get (⟨2, by decide⟩ : BorTag)).isSome
  IO.println s!"gc dead-leaf {boolCode !hasLeaf} {rootChildren} {rangeCount} {boolCode !hasLeafTag}"

  let collapsible := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[1] .Disabled false)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) (some 0) #[2] .Disabled false)
     , some (wildcardFixtureNode (⟨3, by decide⟩ : BorTag) (some 1) #[] .Disabled false)]
    #[BorTag.one, ⟨2, by decide⟩, ⟨3, by decide⟩]
  let collapsed := collapsible.removeUnreachableTags #[BorTag.one, ⟨3, by decide⟩]
  let parentGone := (collapsed.tree.nodes.get ⟨1⟩).isNone
  let rootChild := (collapsed.tree.nodes.get ⟨0⟩).bind (·.children[0]?)
    |>.map UniIndex.toNat |>.getD 99
  let childParent := (collapsed.tree.nodes.get ⟨2⟩).bind (·.parent)
    |>.map UniIndex.toNat |>.getD 99
  IO.println s!"gc collapse {boolCode parentGone} {rootChild} {childParent}"

  let protectedPath := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[1] .Disabled false)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) (some 0) #[2] .Frozen false)
     , some (wildcardFixtureNode (⟨3, by decide⟩ : BorTag) (some 1) #[] .ReservedIM false)]
    #[BorTag.one, ⟨2, by decide⟩, ⟨3, by decide⟩]
  let protectedPath := { protectedPath with
    locations := DedupRangeMap.new (Size.ofBytes 1) {} }
  let preserved := protectedPath.removeUnreachableTags #[BorTag.one, ⟨3, by decide⟩]
  let intermediatePresent := (preserved.tree.nodes.get ⟨1⟩).isSome
  let preservedChildParent := (preserved.tree.nodes.get ⟨2⟩).bind (·.parent)
    |>.map UniIndex.toNat |>.getD 99
  IO.println s!"gc preserve-permission {boolCode intermediatePresent} {preservedChildParent}"

private def emitProvenanceFixture : IO Unit := do
  let tag10 : BorTag := ⟨10, by decide⟩
  let tag11 : BorTag := ⟨11, by decide⟩
  let tag12 : BorTag := ⟨12, by decide⟩
  let tag13 : BorTag := ⟨13, by decide⟩
  let tree := wildcardFixtureTree
    #[ some (wildcardFixtureNode tag10 none #[1] .Disabled false)
     , some (wildcardFixtureNode tag11 (some 0) #[] .Disabled true)
     , some (wildcardFixtureNode tag12 none #[3] .Disabled true)
     , some (wildcardFixtureNode tag13 (some 2) #[] .Disabled true)]
    #[tag10, tag11, tag12, tag13] #[⟨0⟩, ⟨2⟩]
  let visited := BorrowTree.provenanceTags tree
  let output := String.intercalate "," (visited.toList.map fun tag => toString tag.value)
  IO.println s!"tree-provenance {output}"

def main : IO Unit := do
  let rootNoExposure := wildcardFixtureTree
    #[some (wildcardFixtureNode BorTag.one none #[] .Frozen false)]
    #[BorTag.one]
  emitWildcardFixture "no-exposed-main" rootNoExposure
    (wildcardFixtureLocation rootNoExposure #[] #[]) .Read false

  let wildcardRoot := wildcardFixtureTree
    #[some (wildcardFixtureNode BorTag.one none #[] (.ReservedFrz false) false)]
    #[BorTag.one]
  emitWildcardFixture "wildcard-virtual-foreign" wildcardRoot
    (wildcardFixtureLocation wildcardRoot #[] #[]) .Read true

  let parentChild := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[1] .Frozen false)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) (some 0) #[] .ReservedIM true)]
    #[BorTag.one, ⟨2, by decide⟩]
  emitWildcardFixture "child-exposed-write" parentChild
    (wildcardFixtureLocation parentChild
      #[(1, ⟨.Unique, true, .None⟩)] #[(1, .Write)]) .Write false

  let eitherRead := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[1] .Frozen true)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) (some 0) #[] .Frozen true)]
    #[BorTag.one, ⟨2, by decide⟩]
  emitWildcardFixture "either-read" eitherRead
    (wildcardFixtureLocation eitherRead #[] #[(0, .Read), (1, .Read)]) .Read false

  let twoRootTags := #[BorTag.one, (⟨2, by decide⟩ : BorTag)]
  let concreteToWildcard := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[] .Disabled false)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) none #[] (.ReservedFrz false) true)]
    twoRootTags #[⟨0⟩, ⟨1⟩]
  emitMultiRootFixture "concrete-to-wildcard" concreteToWildcard
    (wildcardFixtureLocation concreteToWildcard
      #[(0, ⟨.Unique, true, .None⟩)] #[(1, .Read)])
    (.concrete BorTag.one) .Read

  let wildcardProvenance := wildcardFixtureTree
    #[ some (wildcardFixtureNode BorTag.one none #[] .Frozen true)
     , some (wildcardFixtureNode (⟨2, by decide⟩ : BorTag) none #[] (.ReservedFrz false) true)]
    twoRootTags #[⟨0⟩, ⟨1⟩]
  emitMultiRootFixture "wildcard-provenance" wildcardProvenance
    (wildcardFixtureLocation wildcardProvenance #[] #[(0, .Read), (1, .Read)])
    .wildcard .Read

  emitLifecycleFixtures
  emitGcFixtures
  emitProvenanceFixture

  for permission in permissions do
    let permissionName := permissionCode permission
    IO.println s!"meta {permissionName} {boolCode permission.isInitial} {boolCode permission.isDisabled} {boolCode permission.isFrozen} {boolCode permission.isCell} {boolCode permission.isUnique} {accessCode permission.associatedAccess}"
    for isProtected in [false, true] do
      let localAccess := permission.strongestAllowedLocalAccess isProtected
      let foreignAccess := match permission.strongestIdempotentForeignAccess isProtected with
        | .Access access => idempotentCode access
        | .ImpossibleProtectedReservedIM => "assert"
      IO.println s!"strong {permissionName} {if isProtected then "1" else "0"} {wildcardCode localAccess} {foreignAccess}"

  for left in permissions do
    for right in permissions do
      IO.println s!"compare {permissionCode left} {permissionCode right} {orderingCode (permissionCompare left right)}"

  for parent in permissions do
    for child in permissions do
      IO.println s!"replace {permissionCode parent} {permissionCode child} {boolCode (Permission.canBeReplacedByChild parent child)}"

  for recorded in idempotentAccesses do
    for happeningNext in idempotentAccesses do
      IO.println s!"skip {idempotentCode recorded} {idempotentCode happeningNext} {skipResultCode (IdempotentForeignAccess.canSkipForeignAccess recorded happeningNext)}"
      IO.println s!"record {idempotentCode recorded} {idempotentCode happeningNext} {idempotentCode (IdempotentForeignAccess.recordNew recorded happeningNext)}"
      let (weakened, wasWeakened) := IdempotentForeignAccess.ensureNoStrongerThan recorded happeningNext
      IO.println s!"weaken {idempotentCode recorded} {idempotentCode happeningNext} {idempotentCode weakened} {boolCode wasWeakened}"

  for access in idempotentAccesses do
    IO.println s!"flags {idempotentCode access} {boolCode access.isLocal} {boolCode access.isForeign}"
  for kind in kinds do
    IO.println s!"from-foreign {kindCode kind} {idempotentCode (IdempotentForeignAccess.fromForeign kind)}"
  for kind in kinds do
    for level in wildcardLevels do
      IO.println s!"allows {wildcardCode level} {kindCode kind} {boolCode (WildcardAccessLevel.allows level kind)}"
  for kind in kinds do
    for relation in relatednesses do
      IO.println s!"from-access {kindCode kind} {relatednessCode relation} {idempotentCode (IdempotentForeignAccess.fromAccessAndRelatedness kind relation)}"

  for permission in permissions do
    for kind in kinds do
      for relation in relatednesses do
        for isProtected in [false, true] do
          let result := performAccessTransition kind relation permission isProtected
          IO.println s!"transition {permissionCode permission} {kindCode kind} {relatednessCode relation} {if isProtected then "1" else "0"} {transitionOutcomeCode result}"

  for permission in permissions do
    for accessed in [false, true] do
      for sifa in idempotentAccesses do
        let state : Tree.LocationState := ⟨permission, accessed, sifa⟩
        IO.println s!"location {permissionCode permission} {boolCode accessed} {idempotentCode sifa} {boolCode state.possible}"

  for permission in permissions do
    for sifa in idempotentAccesses do
      let nonAccessed := Tree.LocationState.newNonAccessed permission sifa
      let nonAccessedCode := match nonAccessed with
        | .Constructed state => locationStateCode state
        | .PermissionNotInitialOrDisabled => "assert_initial"
        | .UniquePermissionNotAccessed => "assert_unique"
      IO.println s!"new-non-accessed {permissionCode permission} {idempotentCode sifa} {nonAccessedCode}"
      let accessed := Tree.LocationState.newAccessed permission sifa
      IO.println s!"new-accessed {permissionCode permission} {idempotentCode sifa} {locationStateCode accessed}"

  for permission in permissions do
    for accessed in [false, true] do
      for sifa in idempotentAccesses do
        let state : Tree.LocationState := ⟨permission, accessed, sifa⟩
        for kind in kinds do
          for relation in relatednesses do
            IO.println s!"location-skip {permissionCode permission} {boolCode accessed} {idempotentCode sifa} {kindCode kind} {relatednessCode relation} {continueTraversalCode (state.skipIfKnownNoop kind relation)}"
            let recordResult := state.recordNewAccess kind relation
            let recordCode := match recordResult with
              | .Recorded next => locationStateCode next
              | .DebugAssertion => "assert"
            IO.println s!"location-record {permissionCode permission} {boolCode accessed} {idempotentCode sifa} {kindCode kind} {relatednessCode relation} {recordCode}"
            for isProtected in [false, true] do
              let result := state.performAccess kind relation isProtected
              let nextState := match result with
                | .Success next _ | .Error next _ => next
                | .PermissionInvariantFailure next
                | .TransitionApplicationInvariantFailure next
                | .PossibleInvariantFailure next => next
              IO.println s!"location-perform {permissionCode permission} {boolCode accessed} {idempotentCode sifa} {kindCode kind} {relatednessCode relation} {if isProtected then "1" else "0"} {locationAccessOutcomeCode result} {locationStateCode nextState}"

  for (treeName, tree) in traversalTrees do
    for start in List.range tree.nodes.size do
      for visitChildren in [false, true] do
        let mode := if visitChildren then
          Tree.ChildrenVisitMode.VisitChildrenOfAccessed
        else
          Tree.ChildrenVisitMode.SkipChildrenOfAccessed
        for skipMask in List.range (2 ^ tree.nodes.size) do
          let skipped := (List.range tree.nodes.size).filter
            (fun index => Nat.testBit skipMask index)
          let (root, events) := Tree.TraversalTree.traverse tree start mode skipped
          IO.println
            s!"tree-walk {treeName} {start} {if visitChildren then "children" else "nonchildren"} {skipMask} {root} {traversalEventsCode events}"

  for (name, tree, start, kind, mode) in normalTreeFixtures do
    let result := Tree.NormalTreeState.performAccess tree start kind mode
    IO.println
      s!"normal-access {name} {start} children {kindCode kind} {result.root} {normalStatusCode result.status} {traversalEventsCode result.visited} {normalStatesCode result.tree.locationStates}"

  let accessRoot := BorrowTree.new BorTag.one (Size.ofBytes 1)
  let accessInside := DedupRangeMap.new Size.ZERO
    (Tree.LocationState.newAccessed .Cell .Write)
  let accessChild := accessRoot.newChild Size.ZERO (.concrete BorTag.one)
    (⟨2, by decide⟩ : BorTag) accessInside .Frozen false
  let actualTreeAccess := accessChild.tree.performNormalAccessRange BorTag.one
    (Size.ofBytes 0) (Size.ofBytes 1) .Write ({} : ProtectedTags)
    .VisitChildrenOfAccessed
  let location := actualTreeAccess.tree.locations.iterAll[0]?.map fun segment => segment.data
  let actualStates := match location with
    | none => #[]
    | some location => #[location.perms.get ⟨0⟩, location.perms.get ⟨1⟩]
  let actualStatus := match actualTreeAccess.status with
    | .Completed => "completed"
    | .AccessFailure _ status => normalStatusCode status
    | _ => "tree-access-error"
  match actualTreeAccess.locations[0]?.bind BorrowTree.BorrowTreeLocationResult.normalAccess with
  | none => IO.println "normal-access actual-tree-write-frozen-child 0 children w 0 missing -"
  | some accessRow =>
      IO.println s!"normal-access actual-tree-write-frozen-child 0 children w {accessRow.root} {actualStatus} {traversalEventsCode accessRow.visited} {normalStatesCode actualStates}"

  let ranged := Tree.RangedNormalTreeState.new (Size.ofBytes 3) branchTopology
    branchDefaults [] emptyBranchStates
  let rangedResult := Tree.RangedNormalTreeState.performAccessRange ranged
    (Size.ofBytes 1) (Size.ofBytes 1) 3 .Write .VisitChildrenOfAccessed
  IO.println
    s!"ranged-access one-byte 1 1 {rangedAccessStatusCode rangedResult.status} {rangedLocationResultsCode rangedResult.locations} {rangedMapCode rangedResult.state.locations}"

  let frozen : Tree.LocationState := ⟨.Frozen, true, .None⟩
  let frozenStates := emptyBranchStates.setIfInBounds 3 (some frozen)
  let initialMap := DedupRangeMap.new (Size.ofBytes 3) emptyBranchStates
  let seededMap := initialMap.modifyRange (Size.ofBytes 1) (Size.ofBytes 1)
    (fun _ _ => frozenStates)
  let failingRange := Tree.RangedNormalTreeState.new (Size.ofBytes 3) branchTopology
    branchDefaults [] emptyBranchStates
  let failingRange := { failingRange with locations := seededMap.state }
  let failureResult := Tree.RangedNormalTreeState.performAccessRange failingRange
    (Size.ofBytes 0) (Size.ofBytes 3) 3 .Write .VisitChildrenOfAccessed
  IO.println
    s!"ranged-access failure-stop 0 3 {rangedAccessStatusCode failureResult.status} {rangedLocationResultsCode failureResult.locations} {rangedMapCode failureResult.state.locations}"

  let initialGlobal := GlobalState.new
  let (globalAfterFirst, firstTag) := match initialGlobal.newPointerTag with
    | .ok result => result
    | .error _ => panic! "non-overflowing pointer tag allocation failed"
  let (globalAfterSecond, secondTag) := match globalAfterFirst.newPointerTag with
    | .ok result => result
    | .error _ => panic! "non-overflowing pointer tag allocation failed"
  let allocation : AllocId := ⟨11, by decide⟩
  let (globalWithRoot, rootTag) := match globalAfterSecond.rootPointerTag allocation with
    | .ok result => result
    | .error _ => panic! "non-overflowing root tag allocation failed"
  let (_, sameRootTag) := match globalWithRoot.rootPointerTag allocation with
    | .ok result => result
    | .error _ => panic! "cached root tag lookup failed"
  let frame : FrameState := ⟨#[(allocation, firstTag)]⟩
  let protectors := ProtectedTags.insert
    (ProtectedTags.insert globalWithRoot.protectedTags firstTag .StrongProtector)
    secondTag .WeakProtector
  let withProtectors := { globalWithRoot with protectedTags := protectors }
  let afterCall := withProtectors.endCall frame
  IO.println s!"global-tags {firstTag.value} {secondTag.value} {rootTag.value} {sameRootTag.value}"
  IO.println s!"global-end-call {(afterCall.protectedTags.get firstTag).isSome} {(afterCall.protectedTags.get secondTag).isSome}"
  IO.println s!"global-root-count {globalWithRoot.rootPointerTags.size}"

  let rootIndex : UniIndex := ⟨0⟩
  let firstIndex : UniIndex := ⟨1⟩
  let secondIndex : UniIndex := ⟨2⟩
  let rootNode : TreeNode := ⟨.one, none, #[firstIndex, secondIndex], .Unique, .None, false, none⟩
  let childNode : TreeNode := ⟨⟨2, by decide⟩, some rootIndex, #[], .ReservedFrz false, .None, false, none⟩
  let secondNode : TreeNode := ⟨⟨3, by decide⟩, some rootIndex, #[], .ReservedFrz false, .None, false, none⟩
  let nodes := (UniValMap.insert ({} : UniValMap TreeNode) rootIndex rootNode)
    |>.insert firstIndex childNode
    |>.insert secondIndex secondNode
  let firstExposure := ExposedCache.updateExposure {} nodes firstIndex .None .Read
  let firstCache := firstExposure.cache
  IO.println s!"wild-cache-one {(firstCache.nodes.get rootIndex |>.getD {}).localReads} {(firstCache.nodes.get firstIndex |>.getD {}).localReads}"
  let secondExposure := ExposedCache.updateExposure firstCache nodes secondIndex .None .Read
  let mixed := secondExposure.cache.accessRelatedness rootIndex firstIndex .Read false false
  let mixedForeign := secondExposure.cache.accessRelatedness rootIndex firstIndex .Read false true
  IO.println s!"wild-relation-mixed {wildcardRelatednessCode mixed} {wildcardRelatednessCode mixedForeign}"
  let virtualForeign := ExposedCache.accessRelatedness {} rootIndex rootIndex .Read true false
  IO.println s!"wild-relation-virtual {wildcardRelatednessCode virtualForeign}"
  let releasedExposure := ExposedCache.updateExposure secondExposure.cache nodes firstIndex .Read .None
  let remaining := releasedExposure.cache.accessRelatedness rootIndex secondIndex .Read false true
  IO.println s!"wild-cache-release {(releasedExposure.cache.nodes.get rootIndex |>.getD {}).localReads} {(releasedExposure.cache.nodes.get firstIndex |>.getD {}).localReads} {wildcardRelatednessCode remaining}"

  for byteCount in [0, 1] do
    let sourceTree := BorrowTree.new BorTag.one (Size.ofBytes byteCount)
    let rootIndex : UniIndex := ⟨0⟩
    let rootNode := sourceTree.nodes.get rootIndex |>.getD
      ⟨BorTag.one, none, #[], .Disabled, .None, false, none⟩
    let rootState := match sourceTree.locations.iterAll[0]? with
      | none => ("None", "false")
      | some segment =>
          match segment.data.perms.get rootIndex with
          | none => ("None", "false")
          | some state =>
              (s!"Some({sourcePermissionName state.permission})", boolCode state.accessed)
    IO.println s!"tree-new {byteCount} {sourceTree.roots.size} {rootNode.tag.value} {sourcePermissionName rootNode.defaultInitialPermission} {rootState.1} {rootState.2} {sourceTree.locations.entries.size}"

  let rootTree := BorrowTree.new BorTag.one (Size.ofBytes 1)
  let emptyInside := DedupRangeMap.new Size.ZERO
    (Tree.LocationState.newAccessed .Cell .Write)
  let firstChild := rootTree.newChild Size.ZERO (.concrete BorTag.one)
    (⟨2, by decide⟩ : BorTag) emptyInside (.ReservedFrz false) false
  let secondChild := firstChild.tree.newChild Size.ZERO (.concrete (⟨2, by decide⟩ : BorTag))
    (⟨3, by decide⟩ : BorTag) emptyInside (.ReservedFrz false) true
  let rootNode := secondChild.tree.nodes.get ⟨0⟩ |>.getD
    ⟨BorTag.one, none, #[], .Disabled, .None, false, none⟩
  let parentNode := secondChild.tree.nodes.get ⟨1⟩ |>.getD
    ⟨⟨2, by decide⟩, none, #[], .Disabled, .None, false, none⟩
  let childNode := secondChild.tree.nodes.get ⟨2⟩ |>.getD
    ⟨⟨3, by decide⟩, none, #[], .Disabled, .None, false, none⟩
  IO.println s!"tree-child {rootNode.children.size} {parentNode.parent.getD ⟨0⟩ |>.toNat} {childNode.parent.getD ⟨0⟩ |>.toNat} {sourceSifaName parentNode.defaultInitialSifa} {sourceSifaName childNode.defaultInitialSifa} {secondChild.tree.roots.size}"

  let rangedRoot := BorrowTree.new BorTag.one (Size.ofBytes 5)
  let initialInside : Tree.LocationState := ⟨.ReservedFrz false, true, .Read⟩
  let centerInside : Tree.LocationState := ⟨.ReservedIM, true, .Write⟩
  let insideMap := DedupRangeMap.new (Size.ofBytes 3) initialInside
  let insideMap := insideMap.modifyRange (Size.ofBytes 1) (Size.ofBytes 1)
    (fun _ _ => centerInside)
  let rangedChild := rangedRoot.newChild (Size.ofBytes 1) (.concrete BorTag.one)
    (⟨2, by decide⟩ : BorTag) insideMap.state .Frozen false
  let rangeRows := rangedChild.tree.locations.iterAll.toList.map fun segment =>
    let childState := match segment.data.perms.get ⟨1⟩ with
      | none => "default"
      | some state => s!"{sourcePermissionName state.permission}/{if state.accessed then "accessed" else "future"}"
    s!"{segment.range.start}:{segment.range.stop}={childState}"
  let rootDefaultSifa := rangedChild.tree.nodes.get ⟨0⟩ |>.getD
    ⟨BorTag.one, none, #[], .Disabled, .None, false, none⟩ |>.defaultInitialSifa
  let childDefaultSifa := rangedChild.tree.nodes.get ⟨1⟩ |>.getD
    ⟨⟨2, by decide⟩, none, #[], .Disabled, .None, false, none⟩ |>.defaultInitialSifa
  IO.println s!"tree-retag-range {sourceSifaName rootDefaultSifa} {sourceSifaName childDefaultSifa} {String.intercalate "|" rangeRows}"
  emitRetagPolicyRows
  IO.println "retag-source-order policy>placeConversion>size>tag>pointerAccess>allocationResolution>creationLog>protector>kind>freeze>allocationExtra>parentAccess>dataRace>newChild>replaceProvenance>rebuildValue"
  runRetagPipelineChecks
