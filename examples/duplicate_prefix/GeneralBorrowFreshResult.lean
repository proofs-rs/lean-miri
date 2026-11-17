import duplicate_prefix.GeneralBorrowFreshAnchor
import duplicate_prefix.GeneralBorrowFreshOwnedOn
import duplicate_prefix.GeneralBorrowFreshRange
import duplicate_prefix.GeneralBorrowTagMap
namespace DuplicatePrefix.GeneralBorrowFreshResult
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

open DuplicatePrefix.GeneralBorrowFreshChild
private theorem weaker_none : source_fresh_weaker_sifa .None .None = .None := rfl

/-- The actual constructor tree is exactly the range-modified, attached tree
after the real ancestor SIFA update. No operation success is assumed. -/
theorem mutable_tree (tree : BorrowTree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true).tree =
      (sourceUpdateSifa
        { (GeneralBorrowFreshGraph.attached tree ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ parent parentNode (child newTag parent)) with
          tagMapping := {mapping := tree.tagMapping.mapping.push (newTag,⟨UInt32.ofNat tree.tagMapping.mapping.size⟩),deassigned := tree.tagMapping.deassigned},
          locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
            (fun _ location => GeneralBorrowFreshMaterialization.materialized location ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ inside)).state }
        parent .None).1 := by
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    dsimp only [index,UniIndex.toNat]
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
    exact aligned
  let mapping : UniKeyMap BorTag := {
    mapping := tree.tagMapping.mapping.push (newTag,index),deassigned := tree.tagMapping.deassigned }
  have inserted : tree.tagMapping.insert newTag = .Inserted mapping index :=
    GeneralBorrowTagMap.insert_append tree.tagMapping newTag fresh noFree fits
  have different := parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent
  have nodeLookup : (tree.nodes.insert index (child newTag parent)).get parent = some parentNode :=
    (append_get_other tree.nodes index parent (child newTag parent) atEnd different).trans parentPresent
  let modify : ByteRange → LocationTree → LocationTree :=
    fun _ location => {location with perms := location.perms.insert index inside}
  let changed := tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len) modify
  have modifyOK : changed.outcome = .ok () :=
    GeneralBorrowFreshRange.modify_success tree.locations (Size.ofBytes offset) (Size.ofBytes len) modify well bounds
  have zeroAdd : ({bytes := 0} : Size).add {bytes := offset} = .ok {bytes := offset} := by
    simp [Size.add,Size.ofBytes]
  have rawModifyOK : (tree.locations.modifyRange ({bytes := offset} : Size) {bytes := len}
      (fun _ location => {perms := location.perms.insert index ⟨.ReservedFrz false,true,.None⟩,exposedCache := location.exposedCache})).outcome = .ok () := by
    simpa only [changed,modify,inside,Size.ofBytes] using modifyOK
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [parentTagPresent,Option.map_some,Bool.false_eq_true,↓reduceIte]
  simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
    Bool.not_true,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure]
  simp only [child] at nodeLookup
  rw [nodeLookup]
  simp only [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes,inside,nonzero,beq_iff_eq,↓reduceIte,
    ←Array.forIn_toList,List.forIn_cons,List.forIn_nil,Id.run,bind,pure,
    Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
    Bool.not_true,Bool.false_eq_true,bne_self_eq_false,↓reduceIte]
  simp only [weaker_none,UInt64.sub_zero,zeroAdd,Id.run,bind,pure,rawModifyOK]
  dsimp only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshMaterialization.materialized,
    attachedNodes,inside,child,Size.ofBytes]
end DuplicatePrefix.GeneralBorrowFreshResult
#print axioms DuplicatePrefix.GeneralBorrowFreshResult.mutable_tree
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshResult." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual child-result dependency {dependency}"
