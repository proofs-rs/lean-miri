import duplicate_prefix.GeneralBorrowExposedWildcardStoredRead
import duplicate_prefix.GeneralRangeMapOriginPrepare
import duplicate_prefix.GeneralRangeMapSafety
namespace DuplicatePrefix.GeneralBorrowExposedWildcardPartitionRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

set_option autoImplicit false in
/-- Raw location-local old-leaf support. Permission states and cache contents
may differ between allocation partitions. -/
structure At (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex)
    (extras : List UniIndex) (nodes : UniIndex→TreeNode) (location : LocationTree) : Prop where
  primaryStored : location.perms.get primary=some GeneralBorrowWildcardLeaf.unique
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections
  stored : ∀ root∈extras,(location.perms.get root).isSome=true
  supports : ∀ root∈extras,GeneralBorrowExposureCardinality.supports
    (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) .Read=true

private theorem scalar (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex) (primaryNode : TreeNode)
    (extras : List UniIndex) (nodes : UniIndex→TreeNode) (location : LocationTree) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots=(primary::extras).toArray) (present : tree.nodeAt primary=some primaryNode)
    (leaf : primaryNode.children=#[]) (exposed : primaryNode.isExposed=true) (short : tree.nodes.size<65536)
    (other : ∀ root∈extras,tree.nodeAt root=some (nodes root) ∧ (nodes root).children=#[] ∧ (nodes root).isExposed=true)
    (initial : At tree protections primary extras nodes location) :
    source_access_location (source_tree_access_at tree location none .Read protections mode range)=location ∧
    source_access_status (source_tree_access_at tree location none .Read protections mode range)=none := by
  apply GeneralBorrowExposedWildcardStoredRead.access tree location protections primary primaryNode extras nodes
    (fun root=>(location.perms.get root).getD (nodes root).defaultLocationState) mode range roots present leaf exposed initial.primaryStored initial.coherent short
  intro root member
  obtain ⟨found,leaf,exposed⟩:=other root member
  refine ⟨found,leaf,exposed,?_,initial.supports root member⟩
  cases stored : location.perms.get root with
  | none => have impossible:=initial.stored root member;simp [stored] at impossible
  | some state => simp only [stored,Option.getD_some]

private theorem replaced_self (map : DedupRangeMap LocationTree) (position : Nat) (valid : position<map.entries.size) :
    replaced map position valid map.entries[position].data=map := by
  have same : {map.entries[position] with data:=map.entries[position].data}=map.entries[position] := by
    cases map.entries[position];rfl
  simp only [replaced,same,Array.set_getElem_self]

/-- Actual wildcard ranged Read over ANY well-formed partition map. Every
selected scalar operation is the real no-op; the only resulting map changes
are the source iterator's necessary boundary splits. No successful access or
post-read allocator/cache/profile certificate is assumed. -/
theorem exact (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex) (primaryNode : TreeNode)
    (extras : List UniIndex) (nodes : UniIndex→TreeNode) (offset len : Size) (mode : ChildrenVisitMode)
    (roots : tree.roots=(primary::extras).toArray) (present : tree.nodeAt primary=some primaryNode)
    (leaf : primaryNode.children=#[]) (exposed : primaryNode.isExposed=true) (short : tree.nodes.size<65536)
    (other : ∀ root∈extras,tree.nodeAt root=some (nodes root) ∧ (nodes root).children=#[] ∧ (nodes root).isExposed=true)
    (well : tree.locations.WellFormed) (initial : Every (At tree protections primary extras nodes) tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat) :
    let actual:=tree.performBorrowAccessRange .wildcard offset len .Read protections mode
    actual.status=.Completed ∧ actual.tree={tree with locations:=(tree.locations.iterMut offset len).state} := by
  let prepared:=tree.locations.iterMut offset len
  have good:=GeneralRangeMapSafety.iter_mut (At tree protections primary extras nodes) tree.locations offset len well initial bounds
  unfold BorrowTree.performBorrowAccessRange
  simp only [Id.run,bind,pure,good.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property:=fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus=>
    state.2.2=.Completed ∧ state.1=prepared.state
  have step : ∀ cursor∈List.range' 0 prepared.positions.size,∀ state,property state→property (scan cursor state).value := by
    intro cursor member state valid
    rcases state with ⟨map,visited,status⟩
    rcases valid with ⟨statusEq,mapEq⟩
    dsimp only at statusEq mapEq
    subst status;subst map
    have cursorBound : cursor<prepared.positions.size := by have value:=List.mem_range'_1.mp member;omega
    have segmentBound : cursor<prepared.segments.size := by rw [←good.lengths];exact cursorBound
    let position:=prepared.positions[cursor]'cursorBound
    let segment:=prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩:=good.selected cursor cursorBound
    have segmentEq : segment=prepared.state.entries[position] := selected
    have policy : At tree protections primary extras nodes segment.data := by rw [segmentEq];exact good.every position positionBound
    have operation:=scalar tree protections primary primaryNode extras nodes segment.data mode segment.range roots present leaf exposed short other policy
    have same : (prepared.state.setAtPos position segment.data).state=prepared.state := by
      rw [setAtPos_exact prepared.state position positionBound]
      rw [segmentEq]
      exact replaced_self prepared.state position positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]?=some position:=Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]?=some segment:=Array.getElem?_eq_getElem segmentBound
    simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,operation.1,operation.2,
      setAtPos_success prepared.state position positionBound,ForInStep.value]
    exact ⟨rfl,same⟩
  have final:=GeneralBorrowLoop.list_invariant _ scan property step (prepared.state,#[],.Completed) ⟨rfl,rfl⟩
  refine ⟨final.1,?_⟩
  rw [final.2]

/-- The exact actual ranged result preserves all initial node/tag/root
metadata, per-partition support/cache policy, well-formedness and capacity;
its bytewise location values refine the original map even for interior windows. -/
theorem ranged (tree : BorrowTree) (protections : ProtectedTags) (primary : UniIndex) (primaryNode : TreeNode)
    (extras : List UniIndex) (nodes : UniIndex→TreeNode) (offset len : Size) (mode : ChildrenVisitMode)
    (roots : tree.roots=(primary::extras).toArray) (present : tree.nodeAt primary=some primaryNode)
    (leaf : primaryNode.children=#[]) (exposed : primaryNode.isExposed=true) (short : tree.nodes.size<65536)
    (other : ∀ root∈extras,tree.nodeAt root=some (nodes root) ∧ (nodes root).children=#[] ∧ (nodes root).isExposed=true)
    (well : tree.locations.WellFormed) (initial : Every (At tree protections primary extras nodes) tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat) :
    let actual:=tree.performBorrowAccessRange .wildcard offset len .Read protections mode
    actual.status=.Completed ∧ actual.tree.nodes=tree.nodes ∧ actual.tree.tagMapping=tree.tagMapping ∧ actual.tree.roots=tree.roots ∧
      actual.tree.locations.WellFormed ∧ actual.tree.locations.size=tree.locations.size ∧
      Every (At tree protections primary extras nodes) actual.tree.locations ∧
      GeneralRangeMapOrigins.Refines tree.locations actual.tree.locations := by
  have actual:=exact tree protections primary primaryNode extras nodes offset len mode roots present leaf exposed short other well initial bounds
  have good:=GeneralRangeMapSafety.iter_mut (At tree protections primary extras nodes) tree.locations offset len well initial bounds
  have origins:=GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  exact ⟨actual.1,by rw [actual.2],by rw [actual.2],by rw [actual.2],by rw [actual.2];exact good.wellFormed,
    by rw [actual.2];exact congrArg Size.ofBytes good.capacity,by rw [actual.2];exact good.every,by rw [actual.2];exact origins.2.1⟩
end DuplicatePrefix.GeneralBorrowExposedWildcardPartitionRead
