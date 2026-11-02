import duplicate_prefix.GeneralBorrowGcSharedBank
import duplicate_prefix.GeneralBorrowSharedRootBankGc
namespace DuplicatePrefix.GeneralBorrowGcSharedRootBank
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowSharedRootLabel
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem combined (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (owned : GeneralBorrowRange.LocationOwned tree {} root .Write location) :
    Combined tree {} root (writable root) location := by
  have read := (GeneralBorrowFreshMixedChild.write_combined tree location {} root owned).1
  refine ⟨read,?_⟩
  intro position valid
  by_cases same : position = root.toNat
  · obtain ⟨state,present,permission⟩ := owned.2.permissions position (by rw [←owned.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [Required,AccessOwned,writable,same] using permission⟩
  · obtain ⟨state,present,permission⟩ := read.2.permissions position (by rw [←read.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [Required,AccessOwned,writable,same] using permission⟩

/-- GC retains the full original-root writable bank contract whenever the live
array names all selectable handles. Every child ownership and root path is
reconstructed from actual full GC, enabling later arbitrary-parent constructors. -/
def next {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (live : Array BorTag) (held : GeneralBorrowGcSharedBank.Live s.bank live) :
    GeneralBorrowSharedRootBankState.State root rootTag offset len := by
  let readResult := GeneralBorrowGcSharedBank.collect s positive live held
  let bank := readResult.val
  have bankEq : bank.tree = (s.bank.tree.removeUnreachableTags live).tree := readResult.property.1
  have handlesEq : bank.handles = s.bank.handles := readResult.property.2.1
  let base := GeneralBorrowSharedRootBankGc.collect s positive tag fresh (fun _ => tag) (fun _ => fresh) live
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  let data := GeneralBorrowSharedRootBankState.entryData s tag fresh
  have beforeForest := GeneralBorrowFreshDefaultPathData.forest_of_owned s.bank.tree {} root offset len positive
    s.bank.resources.well s.bank.bounds data.owned location {}
  have fits : s.bank.tree.nodes.size ≤ 4294967296 := by have room := s.bank.resources.room;omega
  let oldRoot := Classical.choose s.rootPresent
  have oldPresent := (Classical.choose_spec s.rootPresent).1
  have parent := GeneralBorrowGcRootResources.parentless s.bank.tree root oldRoot location beforeForest oldPresent (s.rootPath location)
  have roots : ∀ index ∈ s.bank.tree.roots.toList, ∃ value, s.bank.tree.nodes.get index = some value ∧ value.parent = none := by
    intro index member
    rw [s.bank.resources.roots] at member
    have same : index = root := by simpa using member
    subst index;exact ⟨oldRoot,oldPresent,parent⟩
  have metadata := GeneralBorrowGcNodeMetadata.collect s.bank.tree live
  have pathFacts := GeneralBorrowGcSurvivingRootPaths.collect s.bank.tree location {} beforeForest s.bank.resources.depth
    s.bank.resources.children fits roots s.bank.resources.well live
  have related := GeneralBorrowGcAnchorOwnership.related s.bank.tree _ s.bank.resources.depth
    (Classical.choose pathFacts) (Classical.choose_spec pathFacts) metadata
  have rootPresent : bank.tree.nodes.get root = some base.node := by rw [bankEq];exact base.present
  have paths : ∀ target ∈ bank.handles, ∀ loc : LocationTree,
      root.toNat ∈ (source_normal_projection bank.tree loc {}).topology.ancestorPath target.toNat := by
    intro target member loc
    obtain ⟨node,found⟩ := bank.present target member
    have relationEq := related target root node base.node (by rw [←bankEq];exact found) base.present loc
    have initial := s.paths target (handlesEq ▸ member) (⟨⟨#[]⟩,{}⟩ : LocationTree)
    simp only [relation,initial,ite_true] at relationEq
    rw [bankEq]
    split at relationEq
    · assumption
    · cases relationEq
  have rootPath : ∀ loc : LocationTree,
      (source_normal_projection bank.tree loc {}).topology.ancestorPath root.toNat = [root.toNat] := by
    intro loc
    rw [bankEq]
    change sourceAncestorPath _ _ _ = _
    have size : (source_normal_projection (s.bank.tree.removeUnreachableTags live).tree loc {}).topology.nodes.size =
        (s.bank.tree.removeUnreachableTags live).tree.nodes.size := by unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size]
    rw [size,GeneralBorrowGcAnchorOwnership.path _ base.resources.depth loc _ root base.node base.present]
    simp only [GeneralBorrowExposureAncestorFold.walk,base.present,base.parentless,List.map_cons,List.map_nil]
  exact {
    bank := bank
    rootMember := by rw [handlesEq];exact s.rootMember
    rootPresent := ⟨base.node,rootPresent,base.tagged⟩
    rootPath := rootPath
    paths := paths
    owned := by
      intro target member position valid positiveRange before after
      have rootOwnAll : OwnedOn (GeneralBorrowRange.LocationOwned bank.tree {} root .Write) offset (offset+len) bank.tree.locations := by
        simpa only [bankEq] using base.owned
      have rootOwn := rootOwnAll position valid positiveRange before after
      have rootMixed := (combined bank.tree _ root rootOwn).2
      exact GeneralBorrowSharedRootLabel.transfer bank.tree _ root root target rootMixed
        (bank.owned target member position valid positiveRange before after)
        (by rw [rootPath];simp) (paths target member _) }
end
end DuplicatePrefix.GeneralBorrowGcSharedRootBank
