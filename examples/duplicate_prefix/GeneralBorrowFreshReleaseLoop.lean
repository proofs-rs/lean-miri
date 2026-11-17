import duplicate_prefix.GeneralBorrowFreshProtectorRelease
import duplicate_prefix.GeneralBorrowFreshInstallation
namespace DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

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

theorem access_context (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange) :
    source_tree_access_at {tree with locations := map} location source kind protections mode range =
      source_tree_access_at tree location source kind protections mode range := rfl

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

/-- Active stored states of this protector lie in its owned slice. Inactive
or absent outside states impose no allocation-wide ownership requirement. -/
def ActiveOn (tree : BorrowTree) (anchor : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64) : Prop :=
  ∀ position (valid : position < tree.locations.entries.size) state,
    tree.locations.entries[position].data.perms.get anchor = some state → state.accessed = true →
    ∀ kind, state.permission.associatedAccess = some kind →
      tree.locations.entries[position].range.start.toNat < upper.toNat ∧
      lower.toNat < tree.locations.entries[position].range.stop.toNat ∧ (ownerKind = .Read → kind = .Read)

theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (ownerKind : AccessKind) (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) (notExposed : anchorNode.isExposed = false)
    (roots : tree.roots = #[root]) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor) (active : ActiveOn tree anchor ownerKind lower upper)
    (owned : OwnedOn (DuplicatePrefix.GeneralBorrowRange.LocationOwned tree protections anchor ownerKind) lower upper tree.locations) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧
      OwnedOn (DuplicatePrefix.GeneralBorrowRange.LocationOwned result.tree protections anchor ownerKind) lower upper result.tree.locations := by
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := DuplicatePrefix.GeneralBorrowRange.LocationOwned tree protections anchor ownerKind
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
          have here := owned position oldValid positive profile.1 profile.2.1
          obtain ⟨⟨forest⟩,owner⟩ := here
          have succeeded := DuplicatePrefix.GeneralBorrowSingleRoot.access_at tree
            (tree.locations.entries[position]'oldValid).data protections anchor root accessKind .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range forest
            (DuplicatePrefix.GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat accessKind ownerKind profile.2.2 owner)
            depth children anchorNode anchorPresent roots covered
          let access := source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
            accessKind protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
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
              (tree.locations.entries[position]'oldValid).data protections anchor root accessKind ownerKind .SkipChildrenOfAccessed
              (tree.locations.entries[position]'oldValid).range profile.2.2 fits ⟨⟨forest⟩,owner⟩
              depth children anchorNode anchorPresent roots covered
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_owned_on predicate lower upper map position currentValid _ mapOwned nextOwned
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
  refine ⟨True.intro,?_⟩
  intro position valid positive start stop
  rw [DuplicatePrefix.GeneralBorrowFreshInstallation.location_map]
  exact mapOwned position valid positive start stop
end DuplicatePrefix.GeneralBorrowFreshReleaseLoop
#print axioms DuplicatePrefix.GeneralBorrowFreshReleaseLoop.release
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReleaseLoop." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual protector-end loop dependency {dependency}"
