import duplicate_prefix.DuplicatePrefixResidualWriteTransition
namespace DuplicatePrefix.DuplicatePrefixCrossKindQueryGuard
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private theorem filter_sublist_of_imp {α : Type} (items : List α) (first second : α → Bool)
    (included : ∀ item ∈ items, first item = true → second item = true) :
    List.Sublist (items.filter first) (items.filter second) := by
  have exactFilter : items.filter first = (items.filter second).filter first := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro item member
    have implication := included item member
    cases a : first item <;> cases b : second item <;> simp_all
  rw [exactFilter]
  exact List.filter_sublist

theorem supports_write_read (level : WildcardAccessLevel) (write : supports level .Write = true) :
    supports level .Read = true := by
  cases level <;> simp_all [supports,GeneralBorrowExposureAncestorFold.supportsRead,GeneralBorrowExposureAncestorFold.supportsWrite]

theorem contributes_write_read (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) (row : UniIndex × TreeNode) (write : contributes nodes levels query .Write row = true) :
    contributes nodes levels query .Read row = true := by
  simp only [contributes,Bool.and_eq_true] at write ⊢
  exact ⟨⟨write.1.1,supports_write_read _ write.1.2⟩,write.2⟩

theorem write_cardinality_le_read (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) : cardinality nodes levels query .Write ≤ cardinality nodes levels query .Read := by
  exact (filter_sublist_of_imp nodes.entries.toList (contributes nodes levels query .Write)
    (contributes nodes levels query .Read) (fun row _ => contributes_write_read nodes levels query row)).length_le

/-- Coverage plus equal Read counts implies equality of the actual finite
Read contributor lists. This retains set information lost by count bounds. -/
theorem read_contributors_equal (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (root index : UniIndex) (covers : Covers nodes root index)
    (equal : cardinality nodes levels root .Read = cardinality nodes levels index .Read) :
    nodes.entries.toList.filter (contributes nodes levels root .Read) =
      nodes.entries.toList.filter (contributes nodes levels index .Read) := by
  apply Eq.symm
  apply List.Sublist.eq_of_length
  · apply filter_sublist_of_imp
    intro row member localQuery
    simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at localQuery ⊢
    exact ⟨localQuery.1,covers row member localQuery.2⟩
  · exact equal.symm

/-- Every Write contributor is a Read contributor. Consequently equality of
the Read contributor lists forces equality of the actual Write lists too. -/
theorem write_contributors_equal (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (root index : UniIndex) (covers : Covers nodes root index)
    (equal : cardinality nodes levels root .Read = cardinality nodes levels index .Read) :
    nodes.entries.toList.filter (contributes nodes levels root .Write) =
      nodes.entries.toList.filter (contributes nodes levels index .Write) := by
  have readLists := read_contributors_equal nodes levels root index covers equal
  apply List.filter_congr
  intro row member
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro rootWrite
    have rootRead := contributes_write_read nodes levels root row rootWrite
    have memberRead : row ∈ nodes.entries.toList.filter (contributes nodes levels root .Read) := List.mem_filter.mpr ⟨member,rootRead⟩
    rw [readLists] at memberRead
    have localRead := (List.mem_filter.mp memberRead).2
    simp only [contributes,Bool.and_eq_true] at rootWrite localRead ⊢
    exact ⟨rootWrite.1,localRead.2⟩
  · intro localWrite
    simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at localWrite ⊢
    exact ⟨localWrite.1,covers row member localWrite.2⟩

theorem local_classification (rootCount localCount : Nat) (virtual onlyForeign : Bool)
    (bounded : localCount ≤ rootCount)
    (localQuery : classify rootCount localCount virtual onlyForeign = some .LocalAccess) :
    virtual = false ∧ onlyForeign = false ∧ rootCount = localCount ∧ 0 < localCount := by
  cases virtual <;> cases onlyForeign <;>
    by_cases rootZero : rootCount = 0 <;> by_cases equal : rootCount = localCount <;>
    by_cases plusEqual : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

/-- Exact Local Read covers every current Read supporter under this index.
The finite contributor proof above then forces Write to be Local or absent,
with the same source root position and maximum-tag filter. -/
theorem local_read_write (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : Covers tree.nodes root index)
    (localQuery : relation location root index node maximum .Read rootPosition = some .LocalAccess) :
    relation location root index node maximum .Write rootPosition = some .LocalAccess ∨
      relation location root index node maximum .Write rootPosition = none := by
  have counts (query : UniIndex) (kind : AccessKind) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind := by
    have exact := nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query kind
    cases kind <;> exact exact
  have readBound := cardinality_dominates tree.nodes (effective location protections) root index .Read covers
  have rawLocal : classify (cardinality tree.nodes (effective location protections) root .Read)
      (cardinality tree.nodes (effective location protections) index .Read) (rootPosition != 0) (aboveMaximum node maximum) = some .LocalAccess := by
    simpa only [relation,counts] using localQuery
  obtain ⟨virtualFalse,clampFalse,readEqual,_⟩ := local_classification _ _ _ _ readBound rawLocal
  have writeLists := write_contributors_equal tree.nodes (effective location protections) root index covers readEqual
  have writeEqual : cardinality tree.nodes (effective location protections) root .Write =
      cardinality tree.nodes (effective location protections) index .Write := congrArg List.length writeLists
  simp only [relation,counts,virtualFalse,clampFalse,writeEqual]
  by_cases zero : cardinality tree.nodes (effective location protections) index .Write = 0
  · right; simp [classify,zero]
  · left; simp [classify,zero]

/-- A Local Write has positive current Write support and no tag clamp. Since
Write supporters are also Read supporters, the same Read query cannot be exact
Foreign. This uses coherent finite counts, not an assumed query relation. -/
theorem local_write_not_foreign_read (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (covers : Covers tree.nodes root index)
    (localQuery : relation location root index node maximum .Write rootPosition = some .LocalAccess) :
    relation location root index node maximum .Read rootPosition ≠ some .ForeignAccess := by
  have counts (query : UniIndex) (kind : AccessKind) : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query kind =
      cardinality tree.nodes (effective location protections) query kind := by
    have exact := nat_exact location.exposedCache tree.nodes (effective location protections) coherent short query kind
    cases kind <;> exact exact
  have writeBound := cardinality_dominates tree.nodes (effective location protections) root index .Write covers
  have rawLocal : classify (cardinality tree.nodes (effective location protections) root .Write)
      (cardinality tree.nodes (effective location protections) index .Write) (rootPosition != 0) (aboveMaximum node maximum) = some .LocalAccess := by
    simpa only [relation,counts] using localQuery
  obtain ⟨_,clampFalse,_,writePositive⟩ := local_classification _ _ _ _ writeBound rawLocal
  have readPositive : 0 < cardinality tree.nodes (effective location protections) index .Read :=
    Nat.lt_of_lt_of_le writePositive (write_cardinality_le_read tree.nodes (effective location protections) index)
  intro foreign
  have rawForeign : classify (cardinality tree.nodes (effective location protections) root .Read)
      (cardinality tree.nodes (effective location protections) index .Read) (rootPosition != 0) (aboveMaximum node maximum) = some .ForeignAccess := by
    simpa only [relation,counts] using foreign
  have clampTrue := DuplicatePrefixResidualWriteTransition.classify_foreign_above _ _ _ _ readPositive rawForeign
  rw [clampFalse] at clampTrue
  cases clampTrue
end DuplicatePrefix.DuplicatePrefixCrossKindQueryGuard
