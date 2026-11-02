import duplicate_prefix.S05SemanticReadForeignCone
import duplicate_prefix.S05SemanticReadSoundnessStep

namespace DuplicatePrefix.S05SemanticReadStage
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowSifaPermissionConsistency
open GeneralBorrowWildcardSubtreeStack GeneralBorrowWildcardControlWitness
open GeneralBorrowWildcardTaskRegions GeneralBorrowProjection
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (ReadFrame updated)
open GeneralBorrowSnapshotReadState (wildcard)
open DuplicatePrefixCallbackAuthorization
open S05LiveSubtreeCacheSoundness S05SemanticReadEffects S05ReadPostorderGraph
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- A retained live descendant is Read-idempotent, or a physical barrier
already excludes its Write cone. This is a numeric/graph stage fact. -/
def Ready (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query witness : UniIndex) (node : TreeNode) : Prop :=
  ¬ LiveCone tree location query witness ∨
    Consistent {effective location witness node with idempotentForeignAccess := .Read} (protections.contains node.tag)
noncomputable def seen (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query witness : UniIndex) (node : TreeNode) : Bool := by
  classical
  exact decide (Ready tree location protections query witness node)
private theorem seen_iff (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query witness : UniIndex) (node : TreeNode) :
    seen tree location protections query witness node = true ↔ Ready tree location protections query witness node := by
  classical
  simp [seen]

/-- Every entered Foreign posttask carries numeric-ready-or-pending
certificates for all latent descendants. Read classification is frame-stable. -/
def Stage (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop) (stack : Array Task) : Prop :=
  ∀ query node,area query → (query,true) ∈ stack.toList → tree.nodes.get query = some node →
    relation initial root query node maximum .Read position = some .ForeignAccess →
    ∀ witness witnessNode,tree.nodes.get witness = some witnessNode → Path tree query witness →
      Pending tree witness (seen tree current protections query witness witnessNode) stack

theorem initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop) :
    Stage tree location location protections root position maximum area #[(root,false)] := by
  intro query node inside member
  simp at member

private theorem ready_mono (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (effects : Effects tree before after protections) (query witness : UniIndex) (node : TreeNode)
    (present : tree.nodes.get witness = some node)
    (ready : Ready tree before protections query witness node) : Ready tree after protections query witness node := by
  rcases ready with barrier | bound
  · exact .inl (fun live => barrier (live_backward tree before after protections effects query witness live))
  · exact .inr (transport _ _ _ _ (effects witness node present) bound)

theorem expand (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop)
    (graph : Reciprocal tree) (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (stage : Stage tree initial current protections root position maximum area (stack.push (index,false))) :
    Stage tree initial current protections root position maximum area (expanded stack index node.children) := by
  intro query queryNode inside member queryPresent foreign witness witnessNode found path
  simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append,List.mem_cons,List.mem_singleton] at member
  rcases member with (old | equal) | child
  · exact GeneralBorrowWildcardControlWitness.expand graph _ stack index node present
      (stage query queryNode inside (by simp [old]) queryPresent foreign witness witnessNode found path)
  · have equal : (query,true) = (index,true) := by simpa using equal
    have same : query = index := (Prod.mk.inj equal).1
    subst query
    exact GeneralBorrowWildcardControlWitness.expand graph _ stack index node present
      (Or.inr ⟨(index,false),by simp,path,by simp⟩)
  · obtain ⟨childIndex,member,same⟩ := List.mem_map.mp child
    have impossible := congrArg Prod.snd same
    cases impossible

private theorem apart_top (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (stack : Array Task) (top earlier : Task) (member : earlier ∈ stack.toList)
    (disjoint : Disjoint (source_normal_projection tree location protections).topology (stack.push top)) :
    Apart (source_normal_projection tree location protections).topology earlier top := by
  have all := (List.pairwise_append.mp (by simpa only [Disjoint,Array.toList_push] using disjoint)).2.2
  exact all earlier member top (by simp)

private theorem live_tail (tree : BorrowTree) (location : LocationTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (query index witness : UniIndex)
    (path : Path tree query index) (live : LiveCone tree location query witness) : LiveCone tree location index witness := by
  intro middle node present indexWalk witnessWalk
  have later := GeneralBorrowWildcardControlWitness.path_of_walk tree depth index middle node present _ indexWalk
  exact live middle node present ((S05ReadPostorderGraph.trans path later).walk depth) witnessWalk

private theorem skip_read_bound (state : LocationState)
    (noBarrier : state.permission ≠ .Disabled ∧ state.permission ≠ .Frozen)
    (skipped : skip state .Read .ForeignAccess = true) : IdempotentForeignAccess.Read.rank ≤ state.idempotentForeignAccess.rank := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases cache <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases cache <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]

/-- Source skip pops preserve every entered Foreign cone. Physical shortcuts
supply a barrier; otherwise the CURRENT numeric soundness supplies Read
idempotence for the skipped live descendants, independent of their caches. -/
theorem pop (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (inside : area index) (present : tree.nodes.get index = some node)
    (disjoint : Disjoint (source_normal_projection tree initial protections).topology (stack.push (index,false)))
    (sound : Soundness tree current protections area)
    (skipped : skip (effective current index node) .Read .ForeignAccess = true)
    (stage : Stage tree initial current protections root position maximum area (stack.push (index,false))) :
    Stage tree initial current protections root position maximum area stack := by
  classical
  intro query queryNode queryInside queryPending queryPresent foreign witness witnessNode found path
  have pending := stage query queryNode queryInside (by simp [queryPending]) queryPresent foreign witness witnessNode found path
  by_cases reached : Path tree index witness
  · apply Or.inl
    apply (seen_iff tree current protections query witness witnessNode).mpr
    by_cases live : LiveCone tree current query witness
    · rcases S05ReadPostorderGraph.comparable path reached with across | backwards
      · have noBarrier := live index node present (across.walk depth) (reached.walk depth)
        have queryCache := skip_read_bound _ noBarrier skipped
        have bound := sound index node inside present witness witnessNode found (reached.walk depth)
          (live_tail tree current depth query index witness across live)
        obtain ⟨strength,table,bound⟩ := bound
        exact Or.inr ⟨strength,table,Nat.le_trans queryCache bound⟩
      · have apart := apart_top tree initial protections stack (index,false) (query,true) queryPending disjoint
        have desc := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections index query backwards
        exact False.elim (apart query.toNat ⟨by simp [Region],by simpa only [Region,Bool.false_eq_true,ite_false] using desc⟩)
    · exact Or.inl live
  · exact GeneralBorrowWildcardControlWitness.pop stack index false pending reached



private theorem foreign_record_cache (state recorded : LocationState)
    (record : state.recordNewAccess .Read .ForeignAccess = .Recorded recorded) : recorded.idempotentForeignAccess = .Read := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases cache <;>
      simp [LocationState.recordNewAccess,LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
        IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
        Permission.isDisabled,Permission.isFrozen,IdempotentForeignAccess.recordNew,
        IdempotentForeignAccess.fromAccessAndRelatedness,IdempotentForeignAccess.max] at record
    all_goals cases record;rfl
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases cache <;>
      simp [LocationState.recordNewAccess,LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
        IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
        Permission.isDisabled,Permission.isFrozen,IdempotentForeignAccess.recordNew,
        IdempotentForeignAccess.fromAccessAndRelatedness,IdempotentForeignAccess.max] at record
    all_goals cases record;rfl

/-- The exact Read post action preserves the live-permission ready-or-pending
stage. A retained descendant of an entered Foreign cone cannot receive Local
or Either, by static Read counters, count cones and parent-tag geometry. -/
theorem post (tree : BorrowTree) (initial current after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (tagOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (covers : ∀ query,area query → GeneralBorrowExposureCardinality.Covers tree.nodes root query)
    (readFrame : ReadFrame initial current) (profile : GeneralBorrowLocationSifaConsistency.Profile tree after protections)
    (stack : Array Task) (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (action : (relation current root index node maximum .Read position = some .EitherAccess ∧ after = materialized current index node) ∨
      ∃ exact recorded next delta,relation current root index node maximum .Read position = some (wildcard exact) ∧
        (effective current index node).recordNewAccess .Read exact = .Recorded recorded ∧
        recorded.performAccess .Read exact (protections.contains node.tag) = .Success next delta ∧
        after = updated tree current index node protections recorded next delta)
    (stage : Stage tree initial current protections root position maximum area (stack.push (index,true))) :
    Stage tree initial after protections root position maximum area stack := by
  classical
  have effects : Effects tree current after protections := by
    rcases action with ⟨classified,same⟩ | ⟨exact,recorded,next,delta,classified,record,access,same⟩
    · subst after
      exact S05SemanticReadEffects.materialize tree current current protections (S05SemanticReadEffects.initial tree current protections) index node present
    · subst after
      exact S05SemanticReadEffects.update tree current current protections (S05SemanticReadEffects.initial tree current protections) index node present recorded next delta exact record access
  intro query queryNode inside pending queryPresent foreign witness witnessNode found path
  have certified := stage query queryNode inside (by simp [pending]) queryPresent foreign witness witnessNode found path
  apply GeneralBorrowWildcardControlWitness.post _ _ stack index certified
  · intro wasReady
    exact (seen_iff tree after protections query witness witnessNode).mpr
      (ready_mono tree current after protections effects query witness witnessNode found
        ((seen_iff tree current protections query witness witnessNode).mp wasReady))
  · intro same
    subst witness
    have nodeEq := Option.some.inj (present.symm.trans found)
    subst witnessNode
    have classified : relation current root index node maximum .Read position = some .ForeignAccess := by
      rw [GeneralBorrowSnapshotReadState.relation_frame initial current readFrame]
      exact S05SemanticReadForeignCone.downward tree initial protections root query index queryNode node maximum position
        queryPresent present depth tagOrder coherent short (covers query inside) path foreign
    apply (seen_iff tree after protections query index node).mpr
    apply Or.inr
    rcases action with ⟨either,same⟩ | ⟨exact,recorded,next,delta,precise,record,access,same⟩
    · rw [classified] at either
      cases either
    · cases exact with
      | LocalAccess =>
        change relation current root index node maximum .Read position = some .LocalAccess at precise
        rw [classified] at precise
        cases precise
      | ForeignAccess =>
        have cache := S05ContributorCacheOrder.perform_access_cache recorded .Read .ForeignAccess (protections.contains node.tag)
        rw [access] at cache
        simp only [LocationState.AccessResult.resultingState,foreign_record_cache _ _ record] at cache
        have bounded := profile.present index node present
        rw [same] at bounded ⊢
        simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] at bounded ⊢
        have stateEq : {next with idempotentForeignAccess := .Read} = next := by
          cases next with | mk permission accessed sifa => simp_all
        rw [stateEq]
        exact bounded

/-- The source top posttask has no remaining descendant work; its pending
certificate is therefore an actual numeric permission frontier. -/
theorem frontier (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop)
    (stack : Array Task) (index witness : UniIndex) (node witnessNode : TreeNode)
    (inside : area index) (present : tree.nodes.get index = some node) (found : tree.nodes.get witness = some witnessNode)
    (foreign : relation initial root index node maximum .Read position = some .ForeignAccess)
    (path : Path tree index witness) (different : witness ≠ index)
    (separated : S05ReadPostorderGraph.Separated tree (stack.push (index,true)))
    (disjoint : Disjoint (source_normal_projection tree initial protections).topology (stack.push (index,true)))
    (stage : Stage tree initial current protections root position maximum area (stack.push (index,true))) :
    Ready tree current protections index witness witnessNode := by
  have certificate := stage index node inside (by simp) present foreign witness witnessNode found path
  exact (seen_iff tree current protections index witness witnessNode).mp
    (S05ReadPostorderGraph.frontier tree initial protections stack index witness _ path different separated disjoint certificate)

/-- No readiness premise is supplied: the actual source postorder stage
establishes the strict foreign frontier and discharges cache-gain soundness. -/
theorem foreign_sound (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (readFrame : ReadFrame initial current)
    (stack : Array Task) (index : UniIndex) (node : TreeNode) (inside : area index)
    (present : tree.nodes.get index = some node)
    (foreign : relation current root index node maximum .Read position = some .ForeignAccess)
    (separated : S05ReadPostorderGraph.Separated tree (stack.push (index,true)))
    (disjoint : Disjoint (source_normal_projection tree initial protections).topology (stack.push (index,true)))
    (stage : Stage tree initial current protections root position maximum area (stack.push (index,true)))
    (sound : Soundness tree current protections area)
    (recorded next : LocationState) (delta : PermTransition)
    (record : (effective current index node).recordNewAccess .Read .ForeignAccess = .Recorded recorded)
    (access : recorded.performAccess .Read .ForeignAccess (protections.contains node.tag) = .Success next delta) :
    Soundness tree (updated tree current index node protections recorded next delta) protections area := by
  have effects := S05SemanticReadEffects.update tree current current protections (S05SemanticReadEffects.initial tree current protections)
    index node present recorded next delta .ForeignAccess record access
  have cache := S05ContributorCacheOrder.perform_access_cache recorded .Read .ForeignAccess (protections.contains node.tag)
  rw [access] at cache
  simp only [LocationState.AccessResult.resultingState,foreign_record_cache _ _ record] at cache
  apply S05SemanticReadSoundnessStep.foreign_post tree current protections area sound index node present recorded next delta record access
  intro witness witnessNode different found walked live
  have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth index witness witnessNode found _ walked
  have initialForeign : relation initial root index node maximum .Read position = some .ForeignAccess := by
    simpa only [GeneralBorrowSnapshotReadState.relation_frame initial current readFrame] using foreign
  have ready := frontier tree initial current protections root position maximum area stack index witness node witnessNode inside present found
    initialForeign path different separated disjoint stage
  rcases ready with blocked | bound
  · exact False.elim (blocked (live_backward tree current _ protections effects index witness live))
  · have moved := transport _ _ _ _ (effects witness witnessNode found) bound
    simpa only [cache] using moved

end DuplicatePrefix.S05SemanticReadStage
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05SemanticReadStage.initial,
      ``DuplicatePrefix.S05SemanticReadStage.expand,
      ``DuplicatePrefix.S05SemanticReadStage.pop,
      ``DuplicatePrefix.S05SemanticReadStage.post,
      ``DuplicatePrefix.S05SemanticReadStage.frontier,
      ``DuplicatePrefix.S05SemanticReadStage.foreign_sound] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
