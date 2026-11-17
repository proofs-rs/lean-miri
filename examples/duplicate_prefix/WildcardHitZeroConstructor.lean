import duplicate_prefix.GeneralBorrowZeroSharedConstructor

namespace DuplicatePrefix.WildcardHitZeroConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- A live wildcard hit creates a genuine additional root, even for an empty
reference. No exposed-cache or location permission mutation occurs in this
zero-length constructor. Resolution, protector registration and invocation are
separate obligations. -/
def rootNode (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess) : TreeNode :=
  ⟨tag, none, #[], outside, sifa, false, none⟩

def installed (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex)
    (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess) : BorrowTree :=
  { tree with
    tagMapping := mapping
    nodes := tree.nodes.insert index (rootNode tag outside sifa)
    roots := tree.roots.push index }

theorem exact (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (outside : Permission) (sifa : IdempotentForeignAccess) (isProtected : Bool)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess isProtected = .Access sifa)
    (inside : LocationState) (offset : UInt64) :
    tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new Size.ZERO inside) outside isProtected =
      ⟨installed tree mapping index tag outside sifa, .ok ()⟩ := by
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Bool.false_eq_true, ↓reduceIte, initial, nonunique, foreign,
    Bool.not_true, Id.run, bind, pure]
  simp only [DedupRangeMap.iterAll, DedupRangeMap.new, Size.ZERO, Size.ofBytes,
    beq_self_eq_true, ↓reduceIte, ← Array.forIn_toList, List.forIn_nil, pure]
  rfl

theorem append (tree : BorrowTree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (isProtected : Bool)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess isProtected = .Access sifa)
    (inside : LocationState) (offset : UInt64) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new Size.ZERO inside) outside isProtected =
      ⟨installed tree ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
        index tag outside sifa, .ok ()⟩ := by
  exact exact tree tag _ _ (GeneralBorrowTagMap.insert_append _ tag fresh noFree fits)
    outside sifa isProtected initial nonunique foreign inside offset

theorem reuse (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (available : tree.tagMapping.deassigned.back? = some index)
    (outside : Permission) (sifa : IdempotentForeignAccess) (isProtected : Bool)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess isProtected = .Access sifa)
    (inside : LocationState) (offset : UInt64) :
    tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new Size.ZERO inside) outside isProtected =
      ⟨installed tree ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned.pop⟩
        index tag outside sifa, .ok ()⟩ := by
  exact exact tree tag _ _ (GeneralBorrowTagMap.insert_free _ tag fresh index available)
    outside sifa isProtected initial nonunique foreign inside offset

/-- The miss-chain's unchanged-tree postcondition cannot describe a successful
live hit: the genuine constructor has one more root, independently of exposure
counts and of the allocation's byte size. -/
theorem installed_ne (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex)
    (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess) :
    installed tree mapping index tag outside sifa ≠ tree := by
  intro equal
  have sizes := congrArg (fun t : BorrowTree => t.roots.size) equal
  simp only [installed, Array.size_push] at sizes
  omega

end DuplicatePrefix.WildcardHitZeroConstructor
