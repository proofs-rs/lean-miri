import duplicate_prefix.GeneralBorrowStructuralHistoryMixedConcrete
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryMixedConcreteComplete
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowStructuralHistoryMixedConcrete
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

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

/-- Generic concrete mixed permission maps really complete when every source initial
permission/SIFA/arithmetic check follows from its stored data. Append/reuse,
partition mutation and success are all derived from the original State. -/
theorem construct (tree : BorrowTree) (initial : State tree) (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (initialOutside : outside.isInitial=true) (notUnique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (base : Size) (inside : DedupRangeMap LocationState) (bounded : Bounded inside base tree.locations.size)
    (insideInitial : InitialInside inside base held) :
    let actual := tree.newChild base (.concrete parentTag) tag inside outside held
    actual.outcome=.ok () ∧ State actual.tree ∧ actual.tree.locations.size=tree.locations.size ∧ actual.tree.nodes.size≤tree.nodes.size+1 := by
  have structural := GeneralBorrowStructuralHistoryMixedConcrete.preserves tree initial parentTag parent parentNode tagged present tag fresh room outside sifa held
    initialOutside notUnique foreign base inside bounded
  refine ⟨?_,structural⟩
  obtain ⟨mapping,index,inserted,parentLookup,graph,growth⟩ := GeneralBorrowStructuralHistoryConcreteAllocator.select tree initial parent parentNode present tag fresh room outside sifa
  have parentTagged : tree.tagMapping.get parentTag=some parent := tagged
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true,↓reduceIte,parentTagged,Option.map_some,initialOutside,notUnique,foreign,Bool.not_true,Id.run,bind,pure]
  have rawLookup : (tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).get parent=some parentNode := by
    simpa only [GeneralBorrowStructuralHistoryConcreteAllocator.node] using parentLookup
  rw [rawLookup]
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_fresh_modify_scan
  let property := fun current : Option BorrowTree.ChildInsertResult × BorrowTree × IdempotentForeignAccess =>
    current.1=none ∧ State current.2.1 ∧ current.2.1.locations.size=tree.locations.size ∧
      current.2.1.nodes.get parent=some (GeneralBorrowFreshGraph.updatedParent parentNode index)
  have step : ∀segment∈inside.iterAll.toList,∀current,property current→property (scan segment current).value := by
    intro segment member current good
    rcases current with ⟨returned,current,minimum⟩
    obtain ⟨permission,sifaOK,fits⟩ := insideInitial segment member
    have added := addition (Size.ofBytes segment.range.start) base fits
    let start := Size.ofBytes (segment.range.start+base.bytes)
    have rangeBound := bounded segment member start added
    rw [←good.2.2.1] at rangeBound
    let modify := fun (_ : ByteRange) (location : LocationTree) => {location with perms:=location.perms.insert index segment.data}
    have modified := GeneralBorrowFreshRange.modify_success current.locations start (Size.ofBytes (segment.range.stop-segment.range.start)) modify good.2.1.well rangeBound
    have geometry := GeneralBorrowStructuralHistoryGraphOperations.modify_range current good.2.1 start
      (Size.ofBytes (segment.range.stop-segment.range.start)) modify rangeBound
    simp only [scan,permission,Bool.not_true,Bool.false_eq_true,↓reduceIte,sifaOK,bne_self_eq_false,added]
    change property ((match (current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).outcome with
      | .error error => ForInStep.done (some {tree:={current with locations:=(current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).state},outcome:=.error (.RangeMapError error)},
          {current with locations:=(current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).state},source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)
      | .ok () => ForInStep.yield (none,{current with locations:=(current.locations.modifyRange start (Size.ofBytes (segment.range.stop-segment.range.start)) modify).state},source_fresh_weaker_sifa minimum segment.data.idempotentForeignAccess)) : ForInStep (Option BorrowTree.ChildInsertResult × BorrowTree × IdempotentForeignAccess)).value
    rw [modified]
    exact ⟨rfl,geometry.1,geometry.2.trans good.2.2.1,good.2.2.2⟩
  let installed := GeneralBorrowStructuralHistoryConcreteAllocator.installed tree mapping index parent parentNode tag outside sifa
  have stagePresent : installed.nodes.get parent=some (GeneralBorrowFreshGraph.updatedParent parentNode index) := by
    simpa only [installed,GeneralBorrowStructuralHistoryConcreteAllocator.installed,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowFreshGraph.updatedParent] using
      GeneralBorrowNodeUpdate.insert_existing_get_same (tree.nodes.insert index (GeneralBorrowStructuralHistoryConcreteAllocator.node tag parent outside sifa))
        parent parentNode (GeneralBorrowFreshGraph.updatedParent parentNode index) parentLookup
  have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,installed,sifa)
    ⟨rfl,⟨graph,initial.well⟩,rfl,stagePresent⟩
  dsimp only [installed,GeneralBorrowStructuralHistoryConcreteAllocator.installed,GeneralBorrowFreshMetadataChildAttach.staged,
    GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowStructuralHistoryConcreteAllocator.node] at maintained
  generalize folded : forIn inside.iterAll.toList (none,
    ({tree with tagMapping:=mapping,nodes:=(tree.nodes.insert index ⟨tag,some parent,#[],outside,sifa,false,none⟩).insert parent {parentNode with children:=parentNode.children.push index}}:BorrowTree),sifa) scan = final at maintained ⊢
  rcases final with ⟨returned,current,minimum⟩
  have noReturn : returned=none := maintained.1
  subst returned
  have currentState : State current := maintained.2.1
  have parentPresent : current.nodes.get parent=some (GeneralBorrowFreshGraph.updatedParent parentNode index) := maintained.2.2.2
  let oldDepth := Classical.choice currentState.depth
  let rank := GeneralBorrowCanonicalParentDepth.normalize current.nodes oldDepth
  have strict : rank.depth parent<current.nodes.size :=
    GeneralBorrowCanonicalParentDepth.strict current.nodes oldDepth.depth parent _ parentPresent
  have success := GeneralBorrowSifa.succeeds current rank parent _ parentPresent strict minimum
  cases actual : sourceUpdateSifa current parent minimum with
  | mk next outcome => simpa only [actual] using success

end DuplicatePrefix.GeneralBorrowStructuralHistoryMixedConcreteComplete
