import duplicate_prefix.GeneralBorrowSifa
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.GeneralBorrowFreshNode
/-- The append-index branch of the actual newChild node insertion. Existing
node data and parent depth are arbitrary; free-index reuse is a separate case. -/
theorem insert_append {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) :
 (nodes.insert index value).data = nodes.data.push (some value) := by
 simp [UniValMap.insert,UniValMap.extendTo,atEnd,Id.run,pure,Array.set_push]
theorem append_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) : (nodes.insert index value).size = nodes.size+1 := by
 unfold UniValMap.size
 rw [insert_append nodes index value atEnd]
 simp
theorem append_get_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) : (nodes.insert index value).get index = some value := by
 unfold UniValMap.get
 rw [insert_append nodes index value atEnd]
 simp [atEnd]
theorem append_get_other {α : Type} (nodes : UniValMap α) (index query : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) (different : query ≠ index) :
 (nodes.insert index value).get query = nodes.get query := by
 have notEnd : query.toNat ≠ nodes.data.size := fun same => different (index_injective query index (same.trans atEnd.symm))
 unfold UniValMap.get
 rw [insert_append nodes index value atEnd]
 by_cases valid : query.toNat < nodes.data.size
 · simp [Array.getElem?_push,valid,notEnd]
 · simp [Array.getElem?_push,valid,notEnd]
def append_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
 (index parent : UniIndex) (parentNode newNode : TreeNode)
 (atEnd : index.toNat = nodes.data.size)
 (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent) :
 ParentDepth (nodes.insert index newNode) where
 depth := fun query => if query = index then before.depth parent + 1 else before.depth query
 bounded := by
   intro query node lookup
   rw [append_size nodes index newNode atEnd]
   by_cases same : query = index
   · subst query
     simp only [ite_true]
     have bound := before.bounded parent parentNode parentPresent
     omega
   · simp only [same,ite_false]
     rw [append_get_other nodes index query newNode atEnd same] at lookup
     have bound := before.bounded query node lookup
     omega
 parent := by
   intro query node lookup earlier edge
   have parentNotNew : parent ≠ index := by
     intro same
     have bound := lookup_valid nodes parent parentNode parentPresent
     rw [same,atEnd] at bound
     omega
   by_cases same : query = index
   · subst query
     rw [append_get_same nodes index newNode atEnd] at lookup
     cases lookup
     have earlierEq : earlier = parent := Option.some.inj (edge.symm.trans childParent)
     subst earlier
     refine ⟨parentNode,(append_get_other nodes index parent newNode atEnd parentNotNew).trans parentPresent,?_⟩
     simp only [parentNotNew,ite_false,ite_true]
     omega
   · rw [append_get_other nodes index query newNode atEnd same] at lookup
     obtain ⟨ancestor,present,smaller⟩ := before.parent query node lookup earlier edge
     have earlierNotNew : earlier ≠ index := by
       intro equal
       have bound := lookup_valid nodes earlier ancestor present
       rw [equal,atEnd] at bound
       omega
     refine ⟨ancestor,(append_get_other nodes index earlier newNode atEnd earlierNotNew).trans present,?_⟩
     simpa only [earlierNotNew,same,ite_false] using smaller


/-- The second source-ordered node insertion in newChild attaches the new
index to its parent's children, without changing either node's parent link. -/
def attachedNodes (nodes : UniValMap TreeNode) (index parent : UniIndex)
    (parentNode newNode : TreeNode) : UniValMap TreeNode :=
  (nodes.insert index newNode).insert parent {parentNode with children := parentNode.children.push index}

theorem parent_not_fresh (nodes : UniValMap TreeNode) (index parent : UniIndex) (parentNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode) : parent ≠ index := by
  intro same
  have valid := lookup_valid nodes parent parentNode parentPresent
  rw [same,atEnd] at valid
  omega

def attached_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) : ParentDepth (attachedNodes nodes index parent parentNode newNode) :=
  update_depth (nodes.insert index newNode)
    (append_depth nodes before index parent parentNode newNode atEnd parentPresent childParent)
    parent parentNode {parentNode with children := parentNode.children.push index}
    ((append_get_other nodes index parent newNode atEnd (parent_not_fresh nodes index parent parentNode atEnd parentPresent)).trans parentPresent) rfl

theorem attached_parent_strict (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) :
    (attached_depth nodes before index parent parentNode newNode atEnd parentPresent childParent).depth parent <
      (attachedNodes nodes index parent parentNode newNode).size := by
  have different := parent_not_fresh nodes index parent parentNode atEnd parentPresent
  have lookup := (append_get_other nodes index parent newNode atEnd different).trans parentPresent
  change (if parent = index then before.depth parent+1 else before.depth parent) < _
  simp only [different,ite_false]
  unfold attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ lookup,
    append_size nodes index newNode atEnd]
  have bound := before.bounded parent parentNode parentPresent
  omega

/-- The real ancestor-SIFA stage invoked by newChild succeeds after its two
actual node insertions. The new index and original parent's presence are data
conditions; no successful child insertion or SIFA update is a premise. -/
theorem sifa_after_attach (tree : BorrowTree) (before : ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) (strongest : IdempotentForeignAccess) :
    (sourceUpdateSifa
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} parent strongest).2 = .ok () := by
  let nodes := tree.nodes.insert index newNode
  let updatedParent := {parentNode with children := parentNode.children.push index}
  have lookup : nodes.get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  let current : BorrowTree := {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
  let certificate : ParentDepth current.nodes := by
    dsimp only [current]
    exact attached_depth tree.nodes before index parent parentNode newNode atEnd parentPresent childParent
  have present : current.nodes.get parent = some updatedParent := by
    dsimp only [current,attachedNodes,updatedParent]
    exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode
      {parentNode with children := parentNode.children.push index} lookup
  have strict : certificate.depth parent < current.nodes.size := by
    dsimp only [certificate,current]
    exact attached_parent_strict tree.nodes before index parent parentNode newNode atEnd parentPresent childParent
  change (sourceUpdateSifa current parent strongest).2 = .ok ()
  exact GeneralBorrowSifa.succeeds current certificate parent updatedParent present strict strongest
end DuplicatePrefix.GeneralBorrowFreshNode
#print axioms DuplicatePrefix.GeneralBorrowFreshNode.sifa_after_attach
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshNode." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh node dependency {dependency}"
