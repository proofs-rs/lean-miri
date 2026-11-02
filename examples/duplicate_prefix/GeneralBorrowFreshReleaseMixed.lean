import duplicate_prefix.GeneralBorrowFreshReleaseLoop
namespace DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Per-node writable labels retain mutable ancestors while allowing several
Frozen shared nodes on the active child's local ancestor path. -/
def Mixed (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex) (writable : Nat → Bool)
    (location : LocationTree) : Prop :=
  let normal := source_normal_projection tree location protections
  DuplicatePrefix.GeneralBorrowOwnership.Pointwise normal writable
    (DuplicatePrefix.GeneralBorrowAnchor.relation normal anchor.toNat)

def Combined (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex) (writable : Nat → Bool)
    (location : LocationTree) : Prop :=
  DuplicatePrefix.GeneralBorrowRange.LocationOwned tree protections anchor .Read location ∧ Mixed tree protections anchor writable location

theorem mixed_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (writable : Nat → Bool) (location : LocationTree) :
    Mixed {tree with locations := map} protections anchor writable location = Mixed tree protections anchor writable location := rfl

/-- A real child read preserves the arbitrary mixed-strength labels, including
permission-map write-back and exposed-cache processing. -/
theorem mixed_location (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange) (writable : Nat → Bool)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (owned : DuplicatePrefix.GeneralBorrowRange.LocationOwned tree protections anchor .Read location)
    (mixed : Mixed tree protections anchor writable location)
    (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes) (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree) :
    Mixed tree protections anchor writable
      (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)) := by
  obtain ⟨⟨forest⟩,owner⟩ := owned
  let normal := source_normal_projection tree location protections
  have preserved := DuplicatePrefix.GeneralBorrowOwnership.normal_preserves normal forest anchor.toNat owner.anchorValid
    .Read mode writable owner.locationsAligned mixed (fun _ _ _ _ => rfl)
  have storage : DuplicatePrefix.GeneralBorrowStorage.SameStorage normal (normal.performAccess anchor.toNat .Read mode).tree :=
    DuplicatePrefix.GeneralBorrowStorage.events_storage
      (normal.topology.traverse anchor.toNat mode (sourceNormalSkipped normal .Read)).2
      (normal.topology.traverse anchor.toNat mode (sourceNormalSkipped normal .Read)).1 .Read normal
  have relations : DuplicatePrefix.GeneralBorrowAnchor.relation (normal.performAccess anchor.toNat .Read mode).tree anchor.toNat =
      DuplicatePrefix.GeneralBorrowAnchor.relation normal anchor.toNat := by
    funext position
    unfold DuplicatePrefix.GeneralBorrowAnchor.relation
    rw [storage.1]
  unfold Mixed
  rw [DuplicatePrefix.GeneralBorrowRangePreserves.single_root_location tree location protections anchor root .Read mode range
    forest owner depth children anchorNode anchorPresent roots covered]
  rw [DuplicatePrefix.GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Read mode fits]
  change DuplicatePrefix.GeneralBorrowOwnership.Pointwise (normal.performAccess anchor.toNat .Read mode).tree writable
    (DuplicatePrefix.GeneralBorrowAnchor.relation (normal.performAccess anchor.toNat .Read mode).tree anchor.toNat)
  rw [relations]
  exact preserved.2
private theorem replaced_owned_on (predicate : LocationTree → Prop) (lower upper : UInt64)
    (map : DedupRangeMap LocationTree) (position : Nat) (valid : position < map.entries.size) (data : LocationTree)
    (owned : OwnedOn predicate lower upper map) (newOwned : predicate data) :
    OwnedOn predicate lower upper (replaced map position valid data) := by
  intro index bounded positive beforeUpper afterLower
  have oldBound : index < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid data index oldBound] at beforeUpper afterLower
  by_cases same : position = index
  · subst index
    simpa [replaced] using newOwned
  · have previous := owned index oldBound positive beforeUpper afterLower
    simpa [replaced,Array.getElem_set,same] using previous

theorem release_shared_mixed (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (writable : Nat → Bool) (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) (notExposed : anchorNode.isExposed = false)
    (roots : tree.roots = #[root]) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor) (active : ActiveOn tree anchor .Read lower upper)
    (owned : OwnedOn (Combined tree protections anchor writable) lower upper tree.locations) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      OwnedOn (Combined result.tree protections anchor writable) lower upper result.tree.locations := by
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := Combined tree protections anchor writable
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      OwnedOn predicate lower upper map ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapOwned,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapOwned,?_⟩
      intro other member
      exact untouched other (by simp [member])
    cases stored : (tree.locations.entries[position]'oldValid).data.perms.get anchor with
    | none =>
      refine ⟨(none,{tree with locations := map}),?_,skipped⟩
      simp only [scan,index_exact map position currentValid,same,stored]
    | some before =>
      cases associated : before.permission.associatedAccess with
      | none =>
        refine ⟨(none,{tree with locations := map}),?_,skipped⟩
        simp only [scan,index_exact map position currentValid,same,stored,associated]
      | some accessKind =>
        cases accessed : before.accessed with
        | false =>
          refine ⟨(none,{tree with locations := map}),?_,skipped⟩
          simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,Bool.false_eq_true,↓reduceIte]
        | true =>
          have profile := active position oldValid before stored accessed accessKind associated
          have readOnly : accessKind = .Read := profile.2.2 rfl
          subst accessKind
          have here := owned position oldValid positive profile.1 profile.2.1
          obtain ⟨here,mixedHere⟩ := here
          obtain ⟨⟨forest⟩,owner⟩ := here
          have succeeded := DuplicatePrefix.GeneralBorrowSingleRoot.access_at tree
            (tree.locations.entries[position]'oldValid).data protections anchor root AccessKind.Read .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range forest
            (DuplicatePrefix.GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat AccessKind.Read .Read profile.2.2 owner)
            depth children anchorNode anchorPresent roots covered
          let access := source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
            AccessKind.Read protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size :=
            setAtPos_length map position currentValid (source_access_location access)
          have actual : scan position (none,{tree with locations := map}) =
              .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,succeeded]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,
            (setAtPos_length map position currentValid _).trans sizeEq,?_,?_⟩
          · have nextOwned := DuplicatePrefix.GeneralBorrowRangePreserves.location_owned tree
              (tree.locations.entries[position]'oldValid).data protections anchor root AccessKind.Read .Read .SkipChildrenOfAccessed
              (tree.locations.entries[position]'oldValid).range profile.2.2 fits ⟨⟨forest⟩,owner⟩
              depth children anchorNode anchorPresent roots covered
            have nextMixed := mixed_location tree (tree.locations.entries[position]'oldValid).data protections
              anchor root .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range writable fits
              ⟨⟨forest⟩,owner⟩ mixedHere depth children anchorNode anchorPresent roots covered
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_owned_on predicate lower upper map position currentValid _ mapOwned ⟨nextOwned,nextMixed⟩
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro equal;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,owned,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapOwned,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag tag = some anchor := tagPresent
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some anchorNode := anchorPresent
  simp only [lookup,nodeLookup,notExposed,Bool.not_false,↓reduceIte,Id.run,pure]
  refine ⟨True.intro,True.intro,?_⟩
  intro position valid positive start stop
  unfold Combined
  rw [DuplicatePrefix.GeneralBorrowFreshInstallation.location_map,mixed_map]
  exact mapOwned position valid positive start stop
end DuplicatePrefix.GeneralBorrowFreshReleaseMixed
#print axioms DuplicatePrefix.GeneralBorrowFreshReleaseMixed.mixed_location

#print axioms DuplicatePrefix.GeneralBorrowFreshReleaseMixed.release_shared_mixed
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReleaseMixed." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mixed protector-end access dependency {dependency}"
