import duplicate_prefix.S02ConstructorOutsideGenericProjection
import duplicate_prefix.GeneralBorrowSharedNormalRelations

namespace DuplicatePrefix.S02ConstructorOutsideGenericNormal
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshGraph GeneralBorrowExposedScopedNormal
open S02ConstructorOutsideGenericProjection S02ConstructorNormalTopology
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Exact normal permission transport for an arbitrary old source. -/
theorem from_extension (tree after : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (parent child source : UniIndex) (old : DuplicatePrefixBorrowAuthorization.Normal tree location protections source)
    (sourceValid : source.toNat < tree.nodes.data.size) (different : source.toNat ≠ child.toNat)
    (state : LocationState) (foreign : ∀ kind held,DuplicatePrefixScalarAuthorization.Compatible state kind .ForeignAccess held)
    (extension : Extension (source_normal_projection tree location protections)
      (source_normal_projection after location protections) parent.toNat child.toNat state)
    (component : Component (source_normal_projection after default protections).topology source.toNat)
    (supportEq : component.support = Rebased old.component.support parent.toNat child.toNat) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after location protections source) := by
  refine ⟨⟨component,?_⟩⟩
  intro kind query included valid
  have queryValid : query < (source_normal_projection after location protections).topology.nodes.size := by
    rw [topology_size]
    exact valid
  rw [supportEq] at included
  rcases included with ⟨previous,notFresh⟩ | ⟨fresh,_⟩
  · have oldValid := extension.oldValid query queryValid notFresh
    obtain ⟨state,present,compatible⟩ := old.permissions kind query previous (by rw [←topology_size tree location protections];exact oldValid)
    refine ⟨state,(extension.oldState query oldValid notFresh).trans present,?_⟩
    rw [GeneralBorrowSharedNormalRelations.original _ _ parent.toNat child.toNat source.toNat query extension.paths
      (by rw [topology_size];exact sourceValid) different,extension.oldProtected query oldValid notFresh]
    exact compatible
  · subst query
    refine ⟨state,extension.newState,?_⟩
    rw [GeneralBorrowSharedNormalRelations.original_child_foreign _ _ parent.toNat child.toNat source.toNat extension.paths
      (by rw [topology_size];exact sourceValid) different]
    exact foreign kind _

/-- Actual append/reuse preserves every old source's full both-kind normal
capability on a row outside materialization. Sparse/vacant old support is handled
by the rebased component, without an old-support exclusion assumption. -/
theorem normal (tree : BorrowTree) (index parent source : UniIndex) (parentNode sourceNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (sourcePresent : tree.nodeAt source = some sourceNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (foreign : ∀ kind held,DuplicatePrefixScalarAuthorization.Compatible newNode.defaultLocationState kind .ForeignAccess held)
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location protections source) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (attached tree index parent parentNode newNode) location protections source) := by
  have sourceValid := (GeneralBorrowProjection.array_of_node tree source sourceNode sourcePresent).1
  have different : source.toNat ≠ index.toNat := by
    intro equal
    have same := GeneralBorrowNodeUpdate.index_injective source index equal
    change tree.nodes.get source = some sourceNode at sourcePresent
    rw [same,vacant] at sourcePresent
    cases sourcePresent
  rcases slot with atEnd | bounded
  · have projected := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode
      newNode atEnd parentPresent childParent leaf location location protections
    have size := topology_size tree location protections
    let component := S02ConstructorNormalTopology.of_append _ _ parent.toNat source.toNat projected forest old.component
      (by rw [size];exact sourceValid)
    have supportEq : component.support = Rebased old.component.support parent.toNat index.toNat := by
      dsimp only [component,S02ConstructorNormalTopology.of_append,S02ConstructorNormalTopology.of_forests,
        S02ConstructorNormalTopology.component]
      rw [size,←atEnd]
    exact from_extension tree _ location protections parent index source old sourceValid different newNode.defaultLocationState foreign
      (append_extension tree index parent parentNode newNode atEnd vacant parentPresent fits childParent leaf location protections clean forest)
      component supportEq
  · have projected := GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode
      newNode bounded vacant parentPresent childParent leaf location location protections
    let component := S02ConstructorNormalTopology.of_reuse _ _ parent.toNat index.toNat source.toNat projected forest old.component different
    exact from_extension tree _ location protections parent index source old sourceValid different newNode.defaultLocationState foreign
      (reuse_extension tree index parent parentNode newNode bounded vacant parentPresent fits childParent leaf location protections clean forest)
      component rfl

end DuplicatePrefix.S02ConstructorOutsideGenericNormal

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ConstructorOutsideGenericNormal.from_extension,``DuplicatePrefix.S02ConstructorOutsideGenericNormal.normal] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
