import duplicate_prefix.GeneralBorrowGcAnchorResources
import duplicate_prefix.GeneralBorrowSharedRootBankGc
namespace DuplicatePrefix.GeneralBorrowGcSharedBank
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
noncomputable def forest_of_owned (tree : BorrowTree) (protections : ProtectedTags) (parent : UniIndex) (offset len : UInt64)
    (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (kind : AccessKind)
    (owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent kind) offset (offset+len) tree.locations)
    (location : LocationTree) (tags : ProtectedTags) :
    GeneralBorrowForest.Forest (source_normal_projection tree location tags).topology := by
  apply Classical.choice
  have lenNonzero : len.toNat ≠ 0 := fun zero => nonzero (UInt64.toNat_inj.mp (by simpa using zero))
  have lenPositive : 0 < len.toNat := by omega
  have sizeBound : tree.locations.size.bytes.toNat < 2^64 := UInt64.toNat_lt_size tree.locations.size.bytes
  have addition : (offset+len).toNat = offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have inside : offset.toNat < tree.locations.size.bytes.toNat := by omega
  obtain ⟨position,valid,lower,upper⟩ := GeneralRangeMapGeometry.covered tree.locations well offset inside
  have contract := owned position valid (by omega) (by omega) upper
  rw [←GeneralBorrowFreshDefaultPathData.topology_any tree tree.locations.entries[position].data location protections tags]
  exact contract.1

/-- Initial liveness names the source tags of selectable bank handles; it does
not assume any retained index or successful collection. -/
def Live (s : GeneralBorrowSharedBankState.State root offset len) (live : Array BorTag) : Prop :=
  ∀ index ∈ s.handles, ∀ node, s.tree.nodes.get index = some node → live.contains node.tag = true

/-- Actual full GC retains the whole selectable readable handle bank, with the
same ordered handles and real allocator/graph/Clean resources. This supports
later shared generation from any retained child, at arbitrary original depth. -/
def collect {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (live : Array BorTag) (held : Live s.bank live) :
    {next : GeneralBorrowSharedBankState.State root offset len //
      next.tree = (s.bank.tree.removeUnreachableTags live).tree ∧ next.handles = s.bank.handles ∧
      (s.bank.tree.removeUnreachableTags live).outcome = .ok ()} := by
  let tree := s.bank.tree
  let node := Classical.choose s.rootPresent
  have present := (Classical.choose_spec s.rootPresent).1
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  have forest := forest_of_owned tree {} root offset len positive s.bank.resources.well s.bank.bounds .Read
    (s.bank.owned root s.rootMember) location {}
  have parent := GeneralBorrowGcRootResources.parentless tree root node location forest present (s.rootPath location)
  have roots : ∀ index ∈ tree.roots.toList, ∃ value, tree.nodes.get index = some value ∧ value.parent = none := by
    intro index member
    rw [s.bank.resources.roots] at member
    have same : index = root := by simpa using member
    subst index
    exact ⟨node,present,parent⟩
  let base := GeneralBorrowGcAnchorResources.collect tree root s.bank.resources location forest roots root node present
    live (held root s.rootMember node present) .Read offset (offset+len) (s.bank.owned root s.rootMember)
  have fits : tree.nodes.size ≤ 4294967296 := by have room := s.bank.resources.room;change tree.nodes.size+4 ≤ _ at room;omega
  have retention := GeneralBorrowGcLiveRetained.collect tree live
  exact ⟨{
    tree := (tree.removeUnreachableTags live).tree
    resources := base.resources
    handles := s.bank.handles
    present := by
      intro index member
      obtain ⟨old,found⟩ := s.bank.present index member
      obtain ⟨current,currentPresent,_⟩ := retention index old found (held index member old found)
      exact ⟨current,currentPresent⟩
    bounds := by rw [base.capacity];exact s.bank.bounds
    owned := by
      intro index member
      obtain ⟨old,found⟩ := s.bank.present index member
      obtain ⟨_,current,currentPresent,_,owner⟩ := GeneralBorrowGcAnchorOwnership.collect tree location {} forest
        s.bank.resources.depth s.bank.resources.children fits roots s.bank.resources.well live index old found
        (held index member old found) .Read offset (offset+len) (s.bank.owned index member) s.bank.resources.clean
      exact owner },rfl,rfl,base.completed⟩
end
end DuplicatePrefix.GeneralBorrowGcSharedBank
