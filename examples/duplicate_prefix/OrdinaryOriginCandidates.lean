import duplicate_prefix.OrdinaryBorrowAuthority
import duplicate_prefix.S05DiagnosticFnEntryRead

namespace DuplicatePrefix.OrdinaryOriginCandidates
open Miri Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false

/-! Candidate attachments only, following pinned tree.rs:293–303. A wildcard
subtree approximates attachment below some older exposed tag in an earlier
physical component. This does not select a hidden parent or require every
candidate to be usable. Per-byte origin meaning, compatibility among alternatives
and witness survival remain open. No reference-authority or validity claim is
made, and no permission/cache/operation outcome is a field. -/

/-- Actual stored parents connect a present grant to a parentless physical root.
The finite path has no allocator, cache or chronological formation premise. -/
def PhysicalComponent (tree : BorrowTree) (root grant : UniIndex) : Prop :=
  (∃ node, tree.nodes.get root = some node ∧ node.parent = none) ∧
    Path tree root grant

/-- The original allocation root is exempt from inherited-origin candidates.
This recognizes its position; it does not assert that it is exposed or usable. -/
def OriginalRoot (tree : BorrowTree) (root : UniIndex) : Prop :=
  tree.roots[0]? = some root ∧
    ∃ node, tree.nodes.get root = some node ∧ node.parent = none

/-- A possible cross-component attachment, not an assertion of its accessibility.
Positions are explicit because the source orders physical roots by creation tag.
The root-order invariant itself is separate from this candidate relation. -/
structure Attachment (tree : BorrowTree) (virtualRoot exposed : UniIndex) where
  virtualPosition : Nat
  originPosition : Nat
  originRoot : UniIndex
  virtualNode : TreeNode
  exposedNode : TreeNode
  virtualNoninitial : 0 < virtualPosition
  earlierComponent : originPosition < virtualPosition
  virtualListed : tree.roots[virtualPosition]? = some virtualRoot
  originListed : tree.roots[originPosition]? = some originRoot
  virtualPresent : tree.nodes.get virtualRoot = some virtualNode
  virtualParentless : virtualNode.parent = none
  exposedPresent : tree.nodes.get exposed = some exposedNode
  exposedFlag : exposedNode.isExposed = true
  olderTag : exposedNode.tag.value < virtualNode.tag.value
  component : PhysicalComponent tree originRoot exposed

/-- Existence of finite attachment data, with no permission interpretation. -/
def Candidate (tree : BorrowTree) (virtualRoot exposed : UniIndex) : Prop :=
  Nonempty (Attachment tree virtualRoot exposed)

/-- Extract the actual tag inequality without granting any permission. -/
theorem Candidate.older {tree : BorrowTree} {virtualRoot exposed : UniIndex}
    (candidate : Candidate tree virtualRoot exposed) :
    ∃ virtualNode exposedNode,
      tree.nodes.get virtualRoot = some virtualNode ∧
      tree.nodes.get exposed = some exposedNode ∧
      exposedNode.isExposed = true ∧ exposedNode.tag.value < virtualNode.tag.value := by
  obtain ⟨candidate⟩ := candidate
  exact ⟨candidate.virtualNode,candidate.exposedNode,candidate.virtualPresent,
    candidate.exposedPresent,candidate.exposedFlag,candidate.olderTag⟩

/-- The six-node diagnostic's original allocation root is the first root. -/
theorem diagnostic_original :
    OriginalRoot S05DiagnosticFnEntryRead.tree (S05DiagnosticFnEntryRead.ix 0) :=
  ⟨rfl,S05DiagnosticFnEntryRead.original,rfl,rfl⟩

/-- A has the original exposed tag as an attachment candidate. This says
nothing about a reference through A, byte-wise permissions or other roots. -/
def diagnostic_a_attachment :
    Attachment S05DiagnosticFnEntryRead.tree (S05DiagnosticFnEntryRead.ix 1)
      (S05DiagnosticFnEntryRead.ix 0) where
  virtualPosition := 1
  originPosition := 0
  originRoot := S05DiagnosticFnEntryRead.ix 0
  virtualNode := S05DiagnosticFnEntryRead.a
  exposedNode := S05DiagnosticFnEntryRead.original
  virtualNoninitial := by decide
  earlierComponent := by decide
  virtualListed := rfl
  originListed := rfl
  virtualPresent := rfl
  virtualParentless := rfl
  exposedPresent := rfl
  exposedFlag := rfl
  olderTag := by decide
  component := ⟨⟨S05DiagnosticFnEntryRead.original,rfl,rfl⟩,
    .refl _ S05DiagnosticFnEntryRead.original rfl⟩

/-- B has the same original exposed tag as a candidate, independently of A. -/
def diagnostic_b_attachment :
    Attachment S05DiagnosticFnEntryRead.tree (S05DiagnosticFnEntryRead.ix 3)
      (S05DiagnosticFnEntryRead.ix 0) where
  virtualPosition := 2
  originPosition := 0
  originRoot := S05DiagnosticFnEntryRead.ix 0
  virtualNode := S05DiagnosticFnEntryRead.b
  exposedNode := S05DiagnosticFnEntryRead.original
  virtualNoninitial := by decide
  earlierComponent := by decide
  virtualListed := rfl
  originListed := rfl
  virtualPresent := rfl
  virtualParentless := rfl
  exposedPresent := rfl
  exposedFlag := rfl
  olderTag := by decide
  component := ⟨⟨S05DiagnosticFnEntryRead.original,rfl,rfl⟩,
    .refl _ S05DiagnosticFnEntryRead.original rfl⟩

theorem diagnostic_a_candidate :
    Candidate S05DiagnosticFnEntryRead.tree (S05DiagnosticFnEntryRead.ix 1)
      (S05DiagnosticFnEntryRead.ix 0) := ⟨diagnostic_a_attachment⟩

theorem diagnostic_b_candidate :
    Candidate S05DiagnosticFnEntryRead.tree (S05DiagnosticFnEntryRead.ix 3)
      (S05DiagnosticFnEntryRead.ix 0) := ⟨diagnostic_b_attachment⟩

end DuplicatePrefix.OrdinaryOriginCandidates

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.OrdinaryOriginCandidates." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved origin candidate dependency {dependency}"
