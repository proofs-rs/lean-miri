import Miri.TreeBorrows.Traversal

/-!
One-location normal-tree access processing from the interaction between
Miri's tree visitor and LocationState::perform_transition. This composes the
exact local/foreign visit schedule with lazy per-node defaults, SIFA skip and
record behavior, permission transitions, and protector errors.

The model assumes aligned node/default/state arrays and a valid finite tree.
It covers the normal concrete-provenance tree path at one location. Ranged
allocations, wildcard roots/exposed caches, diagnostics, and deallocation
checks remain separate.
-/

namespace Miri.TreeBorrows

namespace Tree

/-- Per-node defaults and protector status for one concrete tree location. -/
structure NormalTreeState where
  topology : TraversalTree
  defaultStates : Array LocationState
  protectedNodes : List Nat
  locationStates : Array (Option LocationState)
  deriving DecidableEq, Repr

/-- Termination/status from one normal tree access. -/
inductive NormalAccessStatus where
  | Completed
  | TransitionError (node : Nat) (error : Diagnostics.TransitionError)
  | RecordDebugAssertion (node : Nat)
  | PermissionInvariantFailure (node : Nat)
  | TransitionApplicationInvariantFailure (node : Nat)
  | PossibleInvariantFailure (node : Nat)
  | MissingLocationState (node : Nat)
  deriving DecidableEq, Repr

/-- Updated one-location tree, root of the accessed tree, events propagated,
and the first source error (if any). -/
structure NormalAccessResult where
  tree : NormalTreeState
  root : Nat
  visited : List TraversalEvent
  status : NormalAccessStatus
  deriving DecidableEq, Repr

namespace NormalTreeState

/-- Existing lazy state, or the node's source default state. -/
def stateAt (tree : NormalTreeState) (node : Nat) : Option LocationState :=
  match tree.locationStates[node]? with
  | none => none
  | some (some state) => some state
  | some none => tree.defaultStates[node]?

private def setState (tree : NormalTreeState) (node : Nat)
    (state : LocationState) : Option NormalTreeState :=
  if h : node < tree.locationStates.size then
    some { tree with locationStates := tree.locationStates.set node (some state) h }
  else none

private def skippedForeignNodes (tree : NormalTreeState) (kind : AccessKind) :
    List Nat :=
  (List.range tree.topology.nodes.size).filter fun node =>
    match tree.stateAt node with
    | none => false
    | some state =>
        state.skipIfKnownNoop kind .ForeignAccess == .SkipSelfAndChildren

private def processEvents (tree : NormalTreeState) (root : Nat)
    (kind : AccessKind) : List TraversalEvent → NormalAccessResult
  | [] => ⟨tree, root, [], .Completed⟩
  | event :: rest =>
      match tree.stateAt event.node with
      | none => ⟨tree, root, [event], .MissingLocationState event.node⟩
      | some oldState =>
          match oldState.recordNewAccess kind event.relatedness with
          | .DebugAssertion =>
              ⟨tree, root, [event], .RecordDebugAssertion event.node⟩
          | .Recorded recordedState =>
              let isProtected := tree.protectedNodes.contains event.node
              let accessResult :=
                recordedState.performAccess kind event.relatedness isProtected
              let nextState := accessResult.resultingState
              match tree.setState event.node nextState with
              | none => ⟨tree, root, [event], .MissingLocationState event.node⟩
              | some nextTree =>
                  match accessResult with
                  | .Success _ _ =>
                      let later := processEvents nextTree root kind rest
                      { later with visited := event :: later.visited }
                  | .Error _ error =>
                      ⟨nextTree, root, [event], .TransitionError event.node error⟩
                  | .PermissionInvariantFailure _ =>
                      ⟨nextTree, root, [event],
                        .PermissionInvariantFailure event.node⟩
                  | .TransitionApplicationInvariantFailure _ =>
                      ⟨nextTree, root, [event],
                        .TransitionApplicationInvariantFailure event.node⟩
                  | .PossibleInvariantFailure _ =>
                      ⟨nextTree, root, [event],
                        .PossibleInvariantFailure event.node⟩

/-- Apply the normal concrete-tree access at one location. The visit skip set
is computed from each node's current-or-default state exactly as Miri's
foreign-only continue callback does. -/
def performAccess (tree : NormalTreeState) (start : Nat) (kind : AccessKind)
    (mode : ChildrenVisitMode) : NormalAccessResult :=
  let skipped := skippedForeignNodes tree kind
  let (root, events) :=
    TraversalTree.traverse tree.topology start mode skipped
  processEvents tree root kind events

/-- A one-node Cell tree used to establish a complete normal-access contract. -/
def singletonCell : NormalTreeState := {
  topology := ⟨#[⟨none, []⟩]⟩
  defaultStates := #[⟨.Cell, false, .None⟩]
  protectedNodes := []
  locationStates := #[none]
}

/-- On a singleton tree, a local Cell access completes and materializes the
accessed location state exactly as the source helpers require. -/
theorem singletonCellAccess_contract (kind : AccessKind) :
    let result := performAccess singletonCell 0 kind .VisitChildrenOfAccessed
    result.status = .Completed ∧
    result.visited = [⟨0, .LocalAccess⟩] ∧
    result.tree.locationStates = #[some ⟨.Cell, true, .None⟩] := by
  cases kind <;> decide

/-- Backward rule for the ordered normal-tree visit. The continuation receives
the same trace and the materialized state even when a visit fails. -/
def eventsPre (root : Nat) (kind : AccessKind) (finish : NormalAccessResult → Prop) :
    List TraversalEvent → NormalTreeState → Prop
  | [], tree => finish ⟨tree, root, [], .Completed⟩
  | event :: rest, tree =>
    let reject status := finish ⟨tree, root, [event], status⟩
    match tree.stateAt event.node with
    | none => reject (.MissingLocationState event.node)
    | some old =>
      match old.recordNewAccess kind event.relatedness with
      | .DebugAssertion => reject (.RecordDebugAssertion event.node)
      | .Recorded recorded =>
        recorded.resultPre kind event.relatedness (tree.protectedNodes.contains event.node)
          (fun result => match tree.setState event.node result.resultingState with
          | none => reject (.MissingLocationState event.node)
          | some next =>
            let fail status := finish ⟨next, root, [event], status⟩
            match result with
            | .Success _ _ =>
              eventsPre root kind (fun later =>
                finish { later with visited := event :: later.visited }) rest next
            | .Error _ error => fail (.TransitionError event.node error)
            | .PermissionInvariantFailure _ => fail (.PermissionInvariantFailure event.node)
            | .TransitionApplicationInvariantFailure _ =>
                fail (.TransitionApplicationInvariantFailure event.node)
            | .PossibleInvariantFailure _ => fail (.PossibleInvariantFailure event.node))

theorem eventsPre_iff (root : Nat) (kind : AccessKind) (finish : NormalAccessResult → Prop)
    (events : List TraversalEvent) (tree : NormalTreeState) :
    eventsPre root kind finish events tree ↔ finish (processEvents tree root kind events) := by
  induction events generalizing tree finish with
  | nil => rfl
  | cons event rest ih =>
    simp only [eventsPre, processEvents]
    cases tree.stateAt event.node with
    | none => rfl
    | some old =>
      dsimp only
      cases old.recordNewAccess kind event.relatedness with
      | DebugAssertion => rfl
      | Recorded recorded =>
        dsimp only
        rw [← LocationState.resultPre_iff]
        generalize recorded.performAccess kind event.relatedness
          (tree.protectedNodes.contains event.node) = result
        cases tree.setState event.node result.resultingState with
        | none => rfl
        | some next =>
          dsimp only
          cases result <;> first | rfl | exact ih _ next

/-- Compute the interpreter's exact visit schedule before pulling the
continuation through each visited node. -/
def accessPre (tree : NormalTreeState) (start : Nat) (kind : AccessKind)
    (mode : ChildrenVisitMode) (finish : NormalAccessResult → Prop) : Prop :=
  let (root, events) := TraversalTree.traverse tree.topology start mode (skippedForeignNodes tree kind)
  eventsPre root kind finish events tree

theorem accessPre_iff (tree : NormalTreeState) (start : Nat) (kind : AccessKind)
    (mode : ChildrenVisitMode) (finish : NormalAccessResult → Prop) :
    accessPre tree start kind mode finish ↔ finish (performAccess tree start kind mode) := by
  unfold accessPre performAccess
  dsimp only
  generalize TraversalTree.traverse tree.topology start mode (skippedForeignNodes tree kind) = visits
  rcases visits with ⟨root, events⟩
  exact eventsPre_iff root kind finish events tree

end NormalTreeState

end Tree

end Miri.TreeBorrows
