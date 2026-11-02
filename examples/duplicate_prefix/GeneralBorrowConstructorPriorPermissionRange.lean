import duplicate_prefix.GeneralBorrowConstructorPriorPermission
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowConstructorPriorPermissionRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Physical permission frames need hold only on the earlier lifetime's range. -/
theorem shape (before after : BorrowTree) (same : treeShape after = treeShape before)
    (query : UniIndex) (expected : Option Permission) (lower upper : UInt64)
    (initial : OwnedOn (At query expected) lower upper before.locations) :
    OwnedOn (At query expected) lower upper after.locations := by
  have rows := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size rows
  intro position valid positive beforeUpper afterLower
  have oldValid : position < before.locations.entries.size := by omega
  have row := congrArg (fun entries => entries[position]?) rows
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some] at row
  have pair := Prod.mk.inj (Option.some.inj row)
  have locations := pair.2
  rw [pair.1] at beforeUpper afterLower
  have factor (map : UniValMap LocationState) :
      (map.get query).map LocationState.permission =
        ((map.data.map (Option.map stateShape))[query.toNat]?).bind (fun slot => slot.map Prod.fst) := by
    simp only [Array.getElem?_map]
    cases stored : map.data[query.toNat]? with
    | none => simp [UniValMap.get,stored]
    | some state => cases state <;> simp [UniValMap.get,stored,stateShape]
  unfold locationShape at locations
  unfold At at initial ⊢
  rw [factor,locations,←factor]
  exact initial position oldValid positive beforeUpper afterLower


/-- Any pure range callback preserving a predicate preserves its independently
chosen slice-local profile, including split/merge preparation. -/
theorem modify_owned {α : Type} [DecidableEq α] (predicate : α → Prop) (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α) (well : map.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat) (lower upper : UInt64)
    (initial : OwnedOn predicate lower upper map)
    (step : ∀ range value,predicate value → predicate (modify range value)) :
    OwnedOn predicate lower upper (map.modifyRange offset len modify).state := by
  have prepared := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have good := refines_owned_on map (map.iterMut offset len).state predicate lower upper
    prepared.1.wellFormed prepared.2.1 initial
  rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds]
  have fold : ∀ (positions : List Nat) (current : DedupRangeMap α),OwnedOn predicate lower upper current →
      OwnedOn predicate lower upper (positions.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position modify) current) := by
    intro positions
    induction positions with
    | nil => intro current good;exact good
    | cons position rest ih =>
      intro current good
      apply ih
      dsimp only [GeneralBorrowFreshModify.atPosition]
      split
      · rename_i valid
        change OwnedOn predicate lower upper (replaced current position valid (modify current.entries[position].range current.entries[position].data))
        intro index bounded positive beforeUpper afterLower
        have oldBound : index < current.entries.size := by simpa only [replaced_length] using bounded
        rw [replaced_range current position valid _ index oldBound] at beforeUpper afterLower
        have old := good index oldBound positive beforeUpper afterLower
        by_cases same : position = index
        · subst index
          simpa [replaced] using step current.entries[position].range current.entries[position].data old
        · simpa [replaced,Array.getElem_set,same] using old
      · exact good
  exact fold _ _ good

/-- A later real protected constructor cannot erase an earlier reservation's
conflict even when the two lifetimes have different bounded ranges. -/
theorem stage (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (inside : LocationState) (mapping : UniKeyMap BorTag) (expected : Option Permission)
    (different : query ≠ index) (offset len lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : OwnedOn (At query expected) lower upper tree.locations) (strongest : IdempotentForeignAccess) :
    let staged := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)).state
    OwnedOn (At query expected) lower upper (sourceUpdateSifa staged parent strongest).1.locations := by
  dsimp only
  apply shape _ _ (GeneralBorrowSifaView.preserves _ parent strongest)
  apply modify_owned (At query expected) tree.locations (Size.ofBytes offset) (Size.ofBytes len) _ well bounds lower upper initial
  intro range location good
  change ((location.perms.insert index inside).get query).map LocationState.permission = expected
  rw [GeneralBorrowFreshLocation.get_other _ index query _ different]
  exact good

/-- Actual protected Default append preserves any earlier tag's stored
permission on its independently chosen lifetime range, including an earlier established conflict. -/
theorem protected_append (input : GeneralBorrowFreshMetadataChildMutable.Input)
    (query : UniIndex) (expected : Option Permission) (lower upper : UInt64)
    (different : query ≠ GeneralBorrowFreshMetadataChildMutable.index input)
    (initial : OwnedOn (At query expected) lower upper input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
    OwnedOn (At query expected) lower upper (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutable.append input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq]
  exact stage input.tree (GeneralBorrowFreshMetadataChildMutable.index input) input.parent query input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) GeneralBorrowFreshChild.inside
    (GeneralBorrowFreshMetadataChildMutable.mapping input) expected different input.offset input.len lower upper input.well input.bounds initial .None

/-- Actual protected Default reuse preserves any earlier tag's stored
permission on its independently chosen lifetime range, including an earlier established conflict. -/
theorem protected_reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input)
    (query : UniIndex) (expected : Option Permission) (lower upper : UInt64)
    (different : query ≠ GeneralBorrowFreshMetadataChildMutableReuse.index input)
    (initial : OwnedOn (At query expected) lower upper input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
    OwnedOn (At query expected) lower upper (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq]
  exact stage input.tree (GeneralBorrowFreshMetadataChildMutableReuse.index input) input.parent query input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) GeneralBorrowFreshChild.inside
    (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) expected different input.offset input.len lower upper input.well input.bounds initial .None

end DuplicatePrefix.GeneralBorrowConstructorPriorPermissionRange
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowConstructorPriorPermissionRange.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ranged prior constructor permission dependency {dependency}"
