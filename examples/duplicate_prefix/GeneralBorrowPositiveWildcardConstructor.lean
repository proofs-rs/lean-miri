import duplicate_prefix.WildcardHitZeroConstructor
import duplicate_prefix.GeneralBorrowFreshRange
import duplicate_prefix.GeneralBorrowFreshLocation
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.WildcardHitZeroConstructor
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def result (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (offset len : UInt64) : BorrowTree :=
  {(installed tree mapping index tag outside sifa) with locations :=
    (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => {location with perms := location.perms.insert index inside})).state}

private theorem exact (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess held = .Access sifa)
    (insideInitial : inside.permission.isInitial = true)
    (insideForeign : inside.permission.strongestIdempotentForeignAccess held = .Access inside.idempotentForeignAccess)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new (Size.ofBytes len) inside) outside held =
      ⟨result tree mapping index tag outside sifa inside offset len,.ok ()⟩ := by
  have modifyOK := GeneralBorrowFreshRange.modify_success tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => {location with perms := location.perms.insert index inside}) well bounds
  have zeroAdd : (Size.ofBytes 0).add (Size.ofBytes offset) = .ok (Size.ofBytes offset) := by simp [Size.add,Size.ofBytes]
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,initial,nonunique,foreign,Bool.not_true,Id.run,bind,pure]
  simp only [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes,nonzero,beq_iff_eq,↓reduceIte,
    ←Array.forIn_toList,List.forIn_cons,List.forIn_nil,Id.run,bind,pure,
    insideInitial,insideForeign,Bool.not_true,bne_self_eq_false,↓reduceIte,UInt64.sub_zero]
  have zeroAddRaw : ({bytes := 0} : Size).add {bytes := offset} = .ok {bytes := offset} := zeroAdd
  simp only [zeroAddRaw,Id.run,bind,pure]
  have rawModifyOK : (tree.locations.modifyRange ({bytes := offset} : Size) {bytes := len}
      (fun _ location => {location with perms := location.perms.insert index inside})).outcome = .ok () := modifyOK
  simp only [rawModifyOK]
  rfl

/-- Positive wildcard-root formation, including real range materialization.
No parent tag, parent walk, cache mutation or ancestor-SIFA operation is needed:
the new node is genuinely appended to the ordered root array. All constructor
checks follow from initial permission metadata, allocation and map geometry. -/
theorem append (tree : BorrowTree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (noFree : tree.tagMapping.deassigned.back? = none) (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess held = .Access sifa)
    (insideInitial : inside.permission.isInitial = true)
    (insideForeign : inside.permission.strongestIdempotentForeignAccess held = .Access inside.idempotentForeignAccess)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
    tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new (Size.ofBytes len) inside) outside held =
      ⟨result tree mapping index tag outside sifa inside offset len,.ok ()⟩ :=
  exact tree tag _ _ (GeneralBorrowTagMap.insert_append _ tag fresh noFree fits) outside sifa inside held initial nonunique foreign
    insideInitial insideForeign offset len nonzero well bounds

theorem reuse (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (available : tree.tagMapping.deassigned.back? = some index)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess held = .Access sifa)
    (insideInitial : inside.permission.isInitial = true)
    (insideForeign : inside.permission.strongestIdempotentForeignAccess held = .Access inside.idempotentForeignAccess)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned.pop⟩
    tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new (Size.ofBytes len) inside) outside held =
      ⟨result tree mapping index tag outside sifa inside offset len,.ok ()⟩ :=
  exact tree tag _ _ (GeneralBorrowTagMap.insert_free _ tag fresh index available) outside sifa inside held initial nonunique foreign
    insideInitial insideForeign offset len nonzero well bounds

/-- Exact new-root geometry, independent of whether the allocator appended or
reused a slot. The child is unexposed and has no physical parent. -/
theorem geometry (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (offset len : UInt64) :
    (result tree mapping index tag outside sifa inside offset len).roots = tree.roots.push index ∧
    (result tree mapping index tag outside sifa inside offset len).nodeAt index = some (rootNode tag outside sifa) := by
  refine ⟨rfl,?_⟩
  exact GeneralBorrowFreshLocation.get_same tree.nodes index (rootNode tag outside sifa)
end DuplicatePrefix.GeneralBorrowPositiveWildcardConstructor
