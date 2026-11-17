import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowForestMutableRegister
import duplicate_prefix.GeneralBorrowForestTagHighWaterHistory
namespace DuplicatePrefix.GeneralBorrowFreshRegistration
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem effective_eq (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (same : ∀ index node, tree.nodeAt index = some node → after.contains node.tag = before.contains node.tag)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    GeneralBorrowExposureCardinality.effective location after index node = GeneralBorrowExposureCardinality.effective location before index node := by
  simp only [GeneralBorrowExposureCardinality.effective,same index node present]

private theorem count_eq (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (same : ∀ index node, tree.nodeAt index = some node → after.contains node.tag = before.contains node.tag)
    (kind : AccessKind) (removed : List UniIndex) (query : UniIndex) :
    residualCount tree location after kind removed query = residualCount tree location before kind removed query := by
  unfold residualCount
  congr 2
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  simp only [GeneralBorrowExposureCardinality.contributes,effective_eq tree location before after same row.1 row.2 present]

private theorem removal (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (same : ∀ index node, tree.nodeAt index = some node → after.contains node.tag = before.contains node.tag)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location after maximum kind removed) : Removal tree location before maximum kind removed := by
  refine ⟨legal.distinct,?_⟩
  intro index member
  obtain ⟨node,present,allowed⟩ := legal.allowed index member
  refine ⟨node,present,?_⟩
  cases kind <;> simpa only [removable,effective_eq tree location before after same index node present] using allowed

/-- Full callback authorization depends on protector membership only at present nodes. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (same : ∀ index node, tree.nodeAt index = some node → after.contains node.tag = before.contains node.tag)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location before root position maximum kind support) :
    Authorization tree location after root position maximum kind support := by
  refine ⟨old.rooted,old.present,old.children,old.covers,old.possible,?_,?_⟩
  · intro first second legalFirst legalSecond subset index node inside present retained
    have relationEq (removed : List UniIndex) :
        residualRelation tree location after root index node maximum kind position removed = residualRelation tree location before root index node maximum kind position removed := by
      simp only [residualRelation,count_eq tree location before after same]
    rw [same index node present,relationEq first,relationEq second]
    exact old.queries first second (removal tree location before after same maximum kind first legalFirst)
      (removal tree location before after same maximum kind second legalSecond) subset index node inside present retained
  · intro primary
    obtain ⟨index,node,inside,present,supports⟩ := old.witness primary
    refine ⟨index,node,inside,present,?_⟩
    simpa only [Supports,same index node present] using supports

/-- Fresh protector registration preserves the SAME raw S01 row, including
all nested-mask callback authorizations and its selected Both normal record. -/
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (tag : BorTag) (kind : ProtectorKind) (fresh : GeneralBorrowProtector.Fresh tree tag)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (old : DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location (protections.insert tag kind) source selected maximum) := by
  have same : ∀ index node, tree.nodeAt index = some node → (protections.insert tag kind).contains node.tag = protections.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other protections tag node.tag kind (fresh (index,node)
      (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have projection := GeneralBorrowProtector.normal_projection tree location protections tag kind fresh
  refine ⟨{wildcard := old.wildcard,rootPath := ?_,rootPresent := old.rootPresent,cutoff := old.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro anchor present
    rw [projection]
    exact old.rootPath anchor present
  · intro anchor present
    obtain ⟨normal⟩ := old.normal anchor present
    refine ⟨{component := normal.component,permissions := ?_}⟩
    intro access index included valid
    rw [projection]
    exact normal.permissions access index included valid
  · intro position valid different
    obtain ⟨support,read,write⟩ := old.callbacks position valid different
    exact ⟨support,authorization tree location protections _ same _ _ _ _ support read,
      authorization tree location protections _ same _ _ _ _ support write⟩

/-- Fresh registration transports the complete positive owner-window packet. -/
theorem positive (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowProtector.Fresh tree tag) (source selected : Option UniIndex)
    (maximum : Option BorTag) (offset len : UInt64)
    (old : DuplicatePrefixBorrowAuthorization.Positive tree protections source selected maximum offset len) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree (protections.insert tag kind) source selected maximum offset len) := by
  refine ⟨{positive := old.positive,bounds := old.bounds,sourcePresent := old.sourcePresent,wildcardRoot := old.wildcardRoot,rows := ?_}⟩
  intro position valid nonzero before after
  obtain ⟨oldRow⟩ := old.rows position valid nonzero before after
  exact row tree _ protections tag kind fresh source selected maximum oldRow
end DuplicatePrefix.GeneralBorrowFreshRegistration
