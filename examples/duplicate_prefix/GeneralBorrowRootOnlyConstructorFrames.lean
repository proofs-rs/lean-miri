import duplicate_prefix.GeneralBorrowRootOnlyPartitionExposure
import duplicate_prefix.GeneralBorrowSifaCacheFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse
import duplicate_prefix.GeneralBorrowFreshModify

namespace DuplicatePrefix.GeneralBorrowRootOnlyConstructorFrames
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exposure-shape equality transports root-only exposure across the genuine
ancestor-SIFA stage, which modifies SIFA metadata but never exposure flags. -/
theorem only_of_exposure (before after : BorrowTree) (root : UniIndex)
    (same : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (only : RootOnly before root) : RootOnly after root := by
  intro index node found exposed
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after same index
  rw [found,Option.map_some,exposed] at flags
  cases old : before.nodes.get index with
  | none => simp only [old,Option.map_none,reduceCtorEq] at flags
  | some oldNode =>
    have exposedOld : oldNode.isExposed = true := Option.some.inj (by simpa only [old,Option.map_some] using flags.symm)
    exact only index oldNode old exposedOld

private theorem mapped_lookup (location : LocationTree) (index : UniIndex) :
    (location.perms.get index).map stateShape = (locationShape location)[index.toNat]?.getD none := by
  unfold UniValMap.get locationShape
  simp only [Array.getElem?_map]
  cases location.perms.data[index.toNat]? <;> rfl

/-- Stored Unique permission depends only on the source permission view. -/
theorem unique_of_shape (before after : LocationTree) (root : UniIndex)
    (same : locationShape after = locationShape before) (unique : StoredUnique before root) : StoredUnique after root := by
  obtain ⟨old,stored,permission⟩ := unique
  have mapped : (after.perms.get root).map stateShape = some (stateShape old) := by
    rw [mapped_lookup,same,←mapped_lookup,stored]
    rfl
  cases found : after.perms.get root with
  | none => simp only [found,Option.map_none,reduceCtorEq] at mapped
  | some next =>
    refine ⟨next,found,?_⟩
    have equal := Option.some.inj (by simpa only [found,Option.map_some] using mapped)
    exact (congrArg Prod.fst equal).trans permission

/-- Full location invariant transport through permission-view and exact-cache
frames. This keeps cache preservation distinct from the permission-only view. -/
theorem locations_of_shapes (before after : BorrowTree) (root : UniIndex) (cache : ExposedCache)
    (shape : treeShape after = treeShape before)
    (caches : GeneralBorrowSifaCacheFrame.cacheShape after = GeneralBorrowSifaCacheFrame.cacheShape before)
    (initial : Every (LocationInvariant cache root) before.locations) :
    Every (LocationInvariant cache root) after.locations := by
  have ranges : after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) := congrArg (fun row => row.2.2.1) shape
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size ranges
  intro position valid
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have perms := congrArg (fun rows => rows[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at perms
  have locShape := congrArg Prod.snd (Option.some.inj perms)
  have values := congrArg (fun rows => rows[position]?) caches
  simp only [GeneralBorrowSifaCacheFrame.cacheShape,Array.getElem?_map,
    Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at values
  exact ⟨unique_of_shape _ _ root locShape (initial position oldValid).1,
    (congrArg Prod.snd (Option.some.inj values)).trans (initial position oldValid).2⟩

/-- Every source ancestor-SIFA branch preserves root-only exposure, stored
Unique permissions and exact caches. Even error branches satisfy this frame;
this theorem does not promote an error result to successful execution. -/
theorem sifa (tree : BorrowTree) (root start : UniIndex) (strongest : IdempotentForeignAccess)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    RootOnly (sourceUpdateSifa tree start strongest).1 root ∧
    Every (LocationInvariant cache root) (sourceUpdateSifa tree start strongest).1.locations := by
  exact ⟨only_of_exposure tree _ root (GeneralBorrowFreshMetadataChildSifa.sifa_exposure tree start strongest) only,
    locations_of_shapes tree _ root cache (GeneralBorrowSifaView.preserves tree start strongest)
      (GeneralBorrowSifaCacheFrame.sifa_cache tree start strongest) initial⟩

/-- Any predicate preserved by the actual modifier callback survives range
preparation, splits and all physical per-position writes. -/
theorem modify_every {α : Type} [DecidableEq α] (predicate : α → Prop)
    (map : DedupRangeMap α) (offset len : Size) (modify : ByteRange → α → α)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (initial : Every predicate map) (stable : ∀ range value, predicate value → predicate (modify range value)) :
    Every predicate (map.modifyRange offset len modify).state := by
  rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds]
  have prepared := GeneralRangeMapSafety.iter_mut predicate map offset len well initial bounds
  have loop : ∀ positions : List Nat, ∀ current, Every predicate current →
      Every predicate (positions.foldl (fun state position => GeneralBorrowFreshModify.atPosition state position modify) current) := by
    intro positions
    induction positions with
    | nil => intro current good;exact good
    | cons position rest ih =>
      intro current good
      apply ih
      unfold GeneralBorrowFreshModify.atPosition
      dsimp only
      split
      · rename_i valid
        apply replaced_every predicate current position valid _ good
        exact stable _ _ (good position valid)
      · exact good
  exact loop _ _ prepared.every

/-- Materializing a fresh/reused CHILD permission changes neither the root's
stored Unique permission nor the exact exposure cache. -/
theorem materialize (map : DedupRangeMap LocationTree) (root child : UniIndex)
    (different : root ≠ child) (cache : ExposedCache) (state : LocationState)
    (offset len : Size) (well : map.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (initial : Every (LocationInvariant cache root) map) :
    Every (LocationInvariant cache root) (map.modifyRange offset len
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child state)).state := by
  apply modify_every (LocationInvariant cache root) map offset len _ well bounds initial
  intro range location good
  obtain ⟨old,stored,unique⟩ := good.1
  refine ⟨⟨old,?_,unique⟩,good.2⟩
  exact (GeneralBorrowFreshLocation.get_other location.perms child root state different).trans stored

end DuplicatePrefix.GeneralBorrowRootOnlyConstructorFrames
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyConstructorFrames." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only constructor frame dependency {dependency}"
