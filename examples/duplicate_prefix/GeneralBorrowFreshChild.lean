import duplicate_prefix.GeneralBorrowFreshNode
import duplicate_prefix.GeneralBorrowFreshRange
import duplicate_prefix.GeneralBorrowTagMap
namespace DuplicatePrefix.GeneralBorrowFreshChild
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

def inside : LocationState := ⟨.ReservedFrz false,true,.None⟩
def child (tag : BorTag) (parent : UniIndex) : TreeNode := {
  tag, parent := some parent,children := #[],defaultInitialPermission := .ReservedFrz false,
  defaultInitialSifa := .None,isExposed := false }

elab "source_fresh_weaker_sifa" : term => do
  let candidates := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.weakerSifa" then some name else none
  match candidates with
  | [name] => return mkConst name
  | _ => throwError "expected pinned weakerSifa helper"
private theorem weaker_none : source_fresh_weaker_sifa .None .None = .None := rfl

/-- The actual protected mutable child constructor succeeds for a nonempty
bounded slice of an arbitrary well-formed location partition and parent-depth
history. This is the append-index branch: the reusable-index pool is empty,
node and tag-map lengths agree, and the new u32 index fits. All map/node/range/
SIFA operation successes are derived. New-anchor ownership and the surrounding
retag/invocation are separate obligations. -/
theorem mutable_success (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
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
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true).outcome = .ok () := by
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
  have sifaOK := sifa_after_attach {tree with tagMapping := mapping,locations := changed.state} depth
    index parent parentNode (child newTag parent) atEnd parentPresent rfl .None
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
  simpa only [attachedNodes,changed,modify,inside,child,Size.ofBytes] using sifaOK
end DuplicatePrefix.GeneralBorrowFreshChild

#print axioms DuplicatePrefix.GeneralBorrowFreshChild.mutable_success
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshChild." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh child dependency {dependency}"
