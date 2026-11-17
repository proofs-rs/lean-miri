import duplicate_prefix.GeneralBorrowFreshLocation
namespace DuplicatePrefix.GeneralBorrowFreshReuseNode
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Insertion at a bounded sparse slot retains the table length. Vacancy is a
separate caller condition: this operation itself also permits overwriting. -/
theorem insert_bounded {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (valid : index.toNat < nodes.data.size) :
    (nodes.insert index value).data = nodes.data.set index.toNat (some value) valid := by
  have noExtra : index.toNat+1-nodes.data.size = 0 := by omega
  simp [UniValMap.insert,UniValMap.extendTo,noExtra,valid,Id.run,pure]

theorem bounded_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (valid : index.toNat < nodes.data.size) : (nodes.insert index value).size = nodes.size := by
  unfold UniValMap.size
  rw [insert_bounded nodes index value valid]
  simp

theorem parent_not_vacant (nodes : UniValMap TreeNode) (index parent : UniIndex) (parentNode : TreeNode)
    (vacant : nodes.get index = none) (parentPresent : nodes.get parent = some parentNode) : parent ≠ index := by
  intro same
  rw [same,vacant] at parentPresent
  cases parentPresent

/-- A bounded vacant slot can hold a fresh child. The explicit rank slack
ensures the child's parent-rank-plus-one fits without enlarging the table.
Every old parent edge remains valid; none can point to the vacant slot. -/
def vacant_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) : ParentDepth (nodes.insert index newNode) where
  depth := fun query => if query = index then before.depth parent+1 else before.depth query
  bounded := by
    intro query node lookup
    rw [bounded_size nodes index newNode valid]
    by_cases same : query = index
    · subst query
      simp only [ite_true]
      omega
    · simp only [same,ite_false]
      rw [GeneralBorrowFreshLocation.get_other nodes index query newNode same] at lookup
      exact before.bounded query node lookup
  parent := by
    intro query node lookup earlier edge
    have parentNotNew := parent_not_vacant nodes index parent parentNode vacant parentPresent
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at lookup
      cases lookup
      have earlierEq : earlier = parent := Option.some.inj (edge.symm.trans childParent)
      subst earlier
      refine ⟨parentNode,(GeneralBorrowFreshLocation.get_other nodes index parent newNode parentNotNew).trans parentPresent,?_⟩
      simp only [parentNotNew,ite_false,ite_true]
      omega
    · rw [GeneralBorrowFreshLocation.get_other nodes index query newNode same] at lookup
      obtain ⟨ancestor,present,smaller⟩ := before.parent query node lookup earlier edge
      have earlierNotNew : earlier ≠ index := by
        intro equal
        rw [equal,vacant] at present
        cases present
      refine ⟨ancestor,(GeneralBorrowFreshLocation.get_other nodes index earlier newNode earlierNotNew).trans present,?_⟩
      simpa only [earlierNotNew,same,ite_false] using smaller

/-- Both source node insertions preserve the depth certificate on a reusable
slot. No absence of per-location permissions is inferred from node vacancy. -/
def attached_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) :
    ParentDepth (GeneralBorrowFreshNode.attachedNodes nodes index parent parentNode newNode) :=
  update_depth (nodes.insert index newNode)
    (vacant_depth nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack)
    parent parentNode {parentNode with children := parentNode.children.push index}
    ((GeneralBorrowFreshLocation.get_other nodes index parent newNode
      (parent_not_vacant nodes index parent parentNode vacant parentPresent)).trans parentPresent) rfl

theorem attached_parent_strict (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) :
    (attached_depth nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack).depth parent <
      (GeneralBorrowFreshNode.attachedNodes nodes index parent parentNode newNode).size := by
  have different := parent_not_vacant nodes index parent parentNode vacant parentPresent
  have lookup := (GeneralBorrowFreshLocation.get_other nodes index parent newNode different).trans parentPresent
  change (if parent = index then before.depth parent+1 else before.depth parent) < _
  simp only [different,ite_false]
  unfold GeneralBorrowFreshNode.attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ lookup,bounded_size nodes index newNode valid]
  exact parentSlack

theorem sifa_after_attach (tree : BorrowTree) (before : ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < tree.nodes.size) (strongest : IdempotentForeignAccess) :
    (sourceUpdateSifa {tree with nodes := GeneralBorrowFreshNode.attachedNodes tree.nodes index parent parentNode newNode}
      parent strongest).2 = .ok () := by
  let current : BorrowTree := {tree with nodes := GeneralBorrowFreshNode.attachedNodes tree.nodes index parent parentNode newNode}
  let updatedParent := {parentNode with children := parentNode.children.push index}
  let certificate : ParentDepth current.nodes := by
    dsimp only [current]
    exact attached_depth tree.nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack
  have lookup := (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode
    (parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  have present : current.nodes.get parent = some updatedParent := by
    dsimp only [current,GeneralBorrowFreshNode.attachedNodes,updatedParent]
    exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ lookup
  have strict : certificate.depth parent < current.nodes.size := by
    dsimp only [certificate,current]
    exact attached_parent_strict tree.nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack
  exact GeneralBorrowSifa.succeeds current certificate parent updatedParent present strict strongest
end DuplicatePrefix.GeneralBorrowFreshReuseNode
#print axioms DuplicatePrefix.GeneralBorrowFreshReuseNode.sifa_after_attach
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReuseNode." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reusable node dependency {dependency}"
