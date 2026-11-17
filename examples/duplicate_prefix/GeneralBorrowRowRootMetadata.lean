import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralRangeMapGeometry
namespace DuplicatePrefix.GeneralBorrowRowRootMetadata
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Permission-independent concrete source/root/cutoff metadata. -/
structure Geometry (tree : BorrowTree) (source selected : UniIndex) (maximum : Option BorTag) : Prop where
  path : ∀ location protections,
    ((source_normal_projection tree location protections).topology.ancestorPath source.toNat).getLast? = some selected.toNat
  root : ∃ node, tree.nodeAt selected = some node ∧ maximum = some node.tag

private theorem topology_any (tree : BorrowTree) (first second : LocationTree) (firstTags secondTags : ProtectedTags) :
    (source_normal_projection tree first firstTags).topology = (source_normal_projection tree second secondTags).topology := by
  unfold_general_projection
  rfl

/-- Positive well-formed storage supplies a real initial row; its shared root
metadata is independent of all row permissions and protector membership. -/
theorem of_positive (tree : BorrowTree) (protections : ProtectedTags) (source selected : UniIndex)
    (maximum : Option BorTag) (offset len : UInt64) (well : tree.locations.WellFormed)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections (some source) (some selected) maximum offset len) :
    Geometry tree source selected maximum := by
  have inside : offset.toNat < tree.locations.size.bytes.toNat := by have p:=positive.positive;have b:=positive.bounds;omega
  obtain ⟨position,valid,start,stop⟩ := GeneralRangeMapGeometry.covered tree.locations well offset inside
  have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have nonzero : offset.toNat < (offset+len).toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    have p:=positive.positive
    omega
  obtain ⟨row⟩ := positive.rows position valid nonzero (by omega) stop
  refine ⟨?_,?_⟩
  · intro location tags
    rw [topology_any tree location tree.locations.entries[position].data tags protections]
    exact row.rootPath source rfl
  · obtain ⟨node,present⟩ := row.rootPresent selected rfl
    exact ⟨node,present,by simpa only [Option.bind_some,present,Option.map_some] using row.cutoff⟩

private theorem last_cons (head : Nat) (tail : List Nat) (last : Nat) (known : tail.getLast? = some last) :
    (head::tail).getLast? = some last := by
  cases tail <;> simp_all

/-- A real leaf attachment retains the selected physical-root cutoff. The
parent-to-child change needs only actual path extension and old-node tag framing. -/
theorem after_attach (before after : BorrowTree) (parent child selected : UniIndex) (maximum : Option BorTag)
    (old : Geometry before parent selected maximum)
    (attach : ∀ oldLocation newLocation protections,
      GeneralBorrowFreshSharedPaths.Attach (source_normal_projection before oldLocation protections).topology
        (source_normal_projection after newLocation protections).topology parent.toNat child.toNat)
    (oldNodes : ∀ query oldNode, before.nodeAt query = some oldNode →
      ∃ next, after.nodeAt query = some next ∧ next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed) :
    Geometry after child selected maximum := by
  refine ⟨?_,?_⟩
  · intro location protections
    rw [(attach default location protections).childPath]
    exact last_cons child.toNat _ selected.toNat (old.path default protections)
  · obtain ⟨node,present,cutoff⟩ := old.root
    obtain ⟨next,found,tag,_⟩ := oldNodes selected node present
    exact ⟨next,found,cutoff.trans (congrArg some tag.symm)⟩
/-- The same actual attachment also retains the original parent's root metadata. -/
theorem after_attach_parent (before after : BorrowTree) (parent child selected : UniIndex) (maximum : Option BorTag)
    (old : Geometry before parent selected maximum)
    (attach : ∀ oldLocation newLocation protections,
      GeneralBorrowFreshSharedPaths.Attach (source_normal_projection before oldLocation protections).topology
        (source_normal_projection after newLocation protections).topology parent.toNat child.toNat)
    (oldNodes : ∀ query oldNode, before.nodeAt query = some oldNode →
      ∃ next, after.nodeAt query = some next ∧ next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed) :
    Geometry after parent selected maximum := by
  refine ⟨?_,?_⟩
  · intro location protections
    have actual := attach default location protections
    rw [actual.oldPath parent.toNat actual.parentValid actual.parentDifferent]
    exact old.path default protections
  · obtain ⟨node,present,cutoff⟩ := old.root
    obtain ⟨next,found,tag,_⟩ := oldNodes selected node present
    exact ⟨next,found,cutoff.trans (congrArg some tag.symm)⟩
end DuplicatePrefix.GeneralBorrowRowRootMetadata
