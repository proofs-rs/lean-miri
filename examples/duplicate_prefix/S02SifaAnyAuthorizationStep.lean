import duplicate_prefix.S02SifaAnyAuthorizationTransport

namespace DuplicatePrefix.S02SifaAnyAuthorizationStep
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowNodeUpdate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Actual single-ancestor cache weakening preserves full authorization
on every physical root, including supports containing that ancestor. -/
theorem weakened (strongest : IdempotentForeignAccess) (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum kind support)
    (consistent : ∀ query value,support query → tree.nodes.get query = some value →
      GeneralBorrowSifaPermissionConsistency.Consistent
        ((location.perms.get query).getD value.defaultLocationState) (protections.contains value.tag)) :
    Authorization (GeneralBorrowSifa.weakened tree index node strongest)
      (weakenLocation location index strongest) protections root position maximum kind support := by
  let after := GeneralBorrowSifa.weakened tree index node strongest
  have shape := weakened_tree_shape tree index node present strongest
  have fields (query : UniIndex) (value : TreeNode) (found : tree.nodes.get query = some value) :
      ∃ next,after.nodes.get query = some next ∧ next.parent = value.parent ∧ next.tag = value.tag ∧
        next.children = value.children ∧ next.isExposed = value.isExposed ∧
        next.defaultInitialPermission = value.defaultInitialPermission := by
    by_cases same : query = index
    · subst query
      have equal := Option.some.inj (found.symm.trans present)
      subst value
      exact ⟨{node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1},
        GeneralBorrowFreshLocation.get_same _ index _,rfl,rfl,rfl,rfl,rfl⟩
    · exact ⟨value,(GeneralBorrowFreshLocation.get_other _ index query _ same).trans found,rfl,rfl,rfl,rfl,rfl⟩
  have stateFrame (query : UniIndex) (value next : TreeNode)
      (found : tree.nodes.get query = some value) (nextFound : after.nodes.get query = some next) :
      ((weakenLocation location index strongest).perms.get query).getD next.defaultLocationState =
        (location.perms.get query).getD value.defaultLocationState ∨
      ((weakenLocation location index strongest).perms.get query).getD next.defaultLocationState =
        {(location.perms.get query).getD value.defaultLocationState with
          idempotentForeignAccess :=
            (((location.perms.get query).getD value.defaultLocationState).idempotentForeignAccess.ensureNoStrongerThan strongest).1} := by
    by_cases same : query = index
    · subst query
      have equal := Option.some.inj (found.symm.trans present)
      subst value
      have nextEq : next = {node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1} := by
        have known : after.nodes.get index = some {node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1} :=
          GeneralBorrowFreshLocation.get_same _ index _
        exact Option.some.inj (nextFound.symm.trans known)
      subst next
      right
      cases stored : location.perms.get index with
      | none => simp [weakenLocation,stored,TreeNode.defaultLocationState]
      | some state => simp only [weakenLocation,stored,GeneralBorrowFreshLocation.get_same,Option.getD_some]
    · have nextEq : next = value := by
        have known : after.nodes.get query = some value := (GeneralBorrowFreshLocation.get_other _ index query _ same).trans found
        exact Option.some.inj (nextFound.symm.trans known)
      subst next
      left
      cases stored : location.perms.get index with
      | none => simp only [weakenLocation,stored]
      | some state => simp only [weakenLocation,stored,GeneralBorrowFreshLocation.get_other _ index query _ same]
  apply S02SifaAnyAuthorizationTransport.transport strongest tree after location (weakenLocation location index strongest) protections
    depth (GeneralBorrowFreshMetadata.parent_depth tree after shape depth)
    (by rw [GeneralBorrowFreshMetadata.node_size tree after shape];exact Nat.le_refl _)
    ?_ ?_ root position maximum kind support old consistent ?_
  · intro query value found
    obtain ⟨next,nextFound,parent,tag,children,exposure,permission⟩ := fields query value found
    refine ⟨next,nextFound,parent,tag,children,exposure,?_⟩
    rcases stateFrame query value next found nextFound with same | weakened
    · rw [same]
    · rw [weakened]
  · intro query next found exposed
    obtain ⟨previous,previousFound,_⟩ := GeneralBorrowFreshMetadata.node_fields after tree shape.symm query next found
    exact ⟨previous,previousFound⟩
  · intro query value next included found nextFound
    exact stateFrame query value next found nextFound

/-- One real weakening transports the callback capability on the same physical
byte window, with no separation from the changed ancestor. -/
theorem weakened_owned (strongest : IdempotentForeignAccess) (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (protections : ProtectedTags) (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (kind : AccessKind) (support : UniIndex → Prop) (lower upper : UInt64)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (old : GeneralRangeMapOrigins.OwnedOn
      (fun location => Authorization tree location protections root position maximum kind support) lower upper tree.locations) :
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Authorization (GeneralBorrowSifa.weakened tree index node strongest) location protections root position maximum kind support)
      lower upper (GeneralBorrowSifa.weakened tree index node strongest).locations := by
  intro row valid positive start stop
  have previous : row < tree.locations.entries.size := by
    simpa only [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.size_map] using valid
  have rowEq : (GeneralBorrowSifa.weakened tree index node strongest).locations.entries[row].data =
      weakenLocation tree.locations.entries[row].data index strongest := by
    simp only [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.getElem_map,weakenLocation]
    rfl
  have rangeEq : (GeneralBorrowSifa.weakened tree index node strongest).locations.entries[row].range = tree.locations.entries[row].range := by
    simp only [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.getElem_map]
  rw [rangeEq] at start stop
  have initial := old row previous positive start stop
  rw [rowEq]
  exact weakened strongest tree depth index node present _ protections root position maximum kind support initial
    (fun query value included found => (profile row previous).present query value found)

/-- Generic invariant rule for the actual ancestor SIFA loop, including its
error-return branches. This does not assert that the operation succeeds. -/
theorem loop_invariant (strongest : IdempotentForeignAccess) (P : BorrowTree → Prop) (tree : BorrowTree) (start : UniIndex)
    (initial : P tree)
    (next : ∀ current index node,current.nodes.get index = some node → P current →
      P (GeneralBorrowSifa.weakened current index node strongest)) :
    P (sourceUpdateSifa tree start strongest).1 := by
  unfold_source_sifa
  split
  · exact initial
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, (P state.2.1 ∧ ∀ returned,state.1 = some returned → P returned.1) →
        (∃ final, scan () state = .done final ∧ (P final.2.1 ∧ ∀ returned,final.1 = some returned → P returned.1)) ∨
        ∃ next, scan () state = .yield next ∧ (P next.2.1 ∧ ∀ returned,next.1 = some returned → P returned.1) ∧ GeneralBorrowSifaView.Measure next < GeneralBorrowSifaView.Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : P current := preserved.1
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
            · simp [GeneralBorrowSifaView.Measure]
          | some index =>
            cases lookup : current.nodes.get index with
            | none =>
              refine .inl ⟨(some (current,.error (.MissingNode index)),current,some index,steps,true),?_,?_⟩
              · simp [scan,past,lookup]
              · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
            | some node =>
              let nextTree := GeneralBorrowSifa.weakened current index node strongest
              have nextShape : P nextTree := next current index node lookup currentShape
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node strongest with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp [GeneralBorrowSifaView.Measure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp only [GeneralBorrowSifaView.Measure,↓reduceIte]
                rw [sameSize]
                omega
    have initialized : (P tree ∧ ∀ returned,(none : Option (BorrowTree × Except BorrowTree.ChildInsertError Unit)) = some returned → P returned.1) := ⟨initial,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan GeneralBorrowSifaView.Measure (fun state => P state.2.1 ∧ ∀ returned,state.1 = some returned → P returned.1) step (none,tree,some start,0,true) initialized
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual

/-- Actual ancestor SIFA preserves full root authorization on
any physical destination window. Runtime permission consistency discharges
Foreign skip weakening even when the support contains changed ancestors. -/
theorem owned (strongest : IdempotentForeignAccess) (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (protections : ProtectedTags) (root : UniIndex) (position : Nat)
    (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop) (lower upper : UInt64)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (initial : GeneralRangeMapOrigins.OwnedOn
      (fun location => Authorization tree location protections root position maximum kind support) lower upper tree.locations) :
    let after := (sourceUpdateSifa tree start strongest).1
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Authorization after location protections root position maximum kind support) lower upper after.locations := by
  let P (current : BorrowTree) : Prop :=
    Nonempty (GeneralBorrowExposure.ParentDepth current.nodes) ∧
    GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile current location protections) current.locations ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Authorization current location protections root position maximum kind support) lower upper current.locations
  have initialized : P tree := ⟨⟨depth⟩,profile,initial⟩
  have maintained := loop_invariant strongest P tree start initialized (by
    intro current index node present packet
    obtain ⟨⟨currentDepth⟩,currentProfile,currentOwned⟩ := packet
    have shape := weakened_tree_shape current index node present strongest
    exact ⟨⟨GeneralBorrowFreshMetadata.parent_depth current _ shape currentDepth⟩,
      GeneralBorrowSifaProfileTransport.weakened_profile current protections index node present strongest currentProfile,
      weakened_owned strongest current currentDepth index node present protections root position maximum kind support lower upper currentProfile currentOwned⟩)
  exact maintained.2.2

end DuplicatePrefix.S02SifaAnyAuthorizationStep
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SifaAnyAuthorizationStep.weakened,
      ``DuplicatePrefix.S02SifaAnyAuthorizationStep.weakened_owned,
      ``DuplicatePrefix.S02SifaAnyAuthorizationStep.loop_invariant,
      ``DuplicatePrefix.S02SifaAnyAuthorizationStep.owned] do
   for ax in (← collectAxioms name) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
