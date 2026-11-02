import duplicate_prefix.GeneralBorrowStructuralHistoryMixedWildcard
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryMixedWildcardComplete
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowStructuralHistoryMixedWildcard
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Pure source initial-permission/SIFA checks and arithmetic guards for every
stored inside segment. These are data conditions, not retag outcome premises. -/
def InitialInside (inside : DedupRangeMap LocationState) (base : Size) (held : Bool) : Prop :=
  ∀segment∈inside.iterAll.toList,segment.data.permission.isInitial=true ∧
    segment.data.permission.strongestIdempotentForeignAccess held=.Access segment.data.idempotentForeignAccess ∧
    segment.range.start.toNat+base.bytes.toNat<2^64

private theorem addition (left right : Size) (fits : left.bytes.toNat+right.bytes.toNat<2^64) :
    left.add right=.ok (Size.ofBytes (left.bytes+right.bytes)) := by
  have equal : (left.bytes+right.bytes).toNat=left.bytes.toNat+right.bytes.toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have noOverflow : ¬left.bytes+right.bytes<left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt,equal]
    omega
  simp only [Size.add,noOverflow,↓reduceIte]

/-- Generic mixed permission maps really complete when every source initial
permission/SIFA/arithmetic check follows from its stored data. Append/reuse,
partition mutation and success are all derived from the original State. -/
theorem construct (tree : BorrowTree) (initial : State tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (initialOutside : outside.isInitial=true) (notUnique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (base : Size) (inside : DedupRangeMap LocationState) (bounded : Bounded inside base tree.locations.size)
    (insideInitial : InitialInside inside base held) :
    let actual := tree.newChild base .wildcard tag inside outside held
    actual.outcome=.ok () ∧ State actual.tree ∧ actual.tree.locations.size=tree.locations.size ∧ actual.tree.nodes.size≤tree.nodes.size+1 := by
  have structural := GeneralBorrowStructuralHistoryMixedWildcard.preserves tree initial tag fresh room outside sifa held
    initialOutside notUnique foreign base inside bounded
  refine ⟨?_,structural⟩
  obtain ⟨mapping,index,inserted,graph,growth⟩ := GeneralBorrowStructuralHistoryWildcardAllocator.select tree initial.toGraphState tag fresh room outside sifa
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,initialOutside,notUnique,foreign,Bool.not_true,Id.run,bind,pure,←Array.forIn_toList]
  name_fresh_modify_scan
  let property := fun current : Option BorrowTree.ChildInsertResult × BorrowTree × IdempotentForeignAccess =>
    current.1=none ∧ current.2.1.locations.WellFormed ∧ current.2.1.locations.size=tree.locations.size
  have step : ∀segment∈inside.iterAll.toList,∀current,property current→property (scan segment current).value := by
    intro segment member current good
    rcases current with ⟨returned,current,minimum⟩
    obtain ⟨permission,sifaOK,fits⟩ := insideInitial segment member
    have added := addition (Size.ofBytes segment.range.start) base fits
    let start := Size.ofBytes (segment.range.start+base.bytes)
    have rangeBound := bounded segment member start added
    rw [←good.2.2] at rangeBound
    let modify := fun (_ : ByteRange) (location : LocationTree) => {location with perms:=location.perms.insert index segment.data}
    have modified := GeneralBorrowFreshRange.modify_success current.locations start (Size.ofBytes (segment.range.stop-segment.range.start)) modify good.2.1 rangeBound
    have geometry := GeneralBorrowFreshRangeFrame.modifyRange_frame current.locations start
      (Size.ofBytes (segment.range.stop-segment.range.start)) modify good.2.1 rangeBound
    simp only [scan,permission,Bool.not_true,Bool.false_eq_true,↓reduceIte,sifaOK,bne_self_eq_false,added]
    change property ((match (current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).outcome with
      | .error error => ForInStep.done (some {tree:={current with locations:=(current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).state},outcome:=.error (.RangeMapError error)},
          {current with locations:=(current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).state},source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
      | .ok () => ForInStep.yield (none,{current with locations:=(current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).state},source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)) : ForInStep (Option BorrowTree.ChildInsertResult × BorrowTree × IdempotentForeignAccess)).value
    rw [modified]
    exact ⟨rfl,geometry.1,(congrArg Size.mk geometry.2).trans good.2.2⟩
  let installed := WildcardHitZeroConstructor.installed tree mapping index tag outside sifa
  have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,installed,sifa) ⟨rfl,initial.well,rfl⟩
  dsimp only [installed,WildcardHitZeroConstructor.installed,WildcardHitZeroConstructor.rootNode] at maintained
  rw [maintained.1]
end DuplicatePrefix.GeneralBorrowStructuralHistoryMixedWildcardComplete
