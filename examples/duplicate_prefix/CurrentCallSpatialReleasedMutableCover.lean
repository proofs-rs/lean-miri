import duplicate_prefix.CurrentCallSpatialLenRelease
import duplicate_prefix.CurrentCallSpatialFutureCover
import duplicate_prefix.CurrentCallSpatialSharedCover
import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.S05CurrentReleaseIterator
namespace DuplicatePrefix.CurrentCallSpatialReleasedMutableCover
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {before tracker ctx offset length} (role : RoleCover before tracker ctx .mut offset length)
    {post : Before} {next : MachineHooks.BorrowState} {tree : BorrowTree}

private theorem authority_weaken (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (before after : ProtectedTags) (grant : UniIndex)
    (weaken : ∀tag,after.contains tag=true→before.contains tag=true)
    (old : S05CompletedAncestryReadMutable.Authority tree completion before grant location) :
    S05CompletedAncestryReadMutable.Authority tree completion after grant location := by
  intro index node present
  have prior:=old index node present
  constructor
  · intro below
    have rights:=prior.1 below
    exact ⟨rights.1,rights.2.1,rights.2.2.1,fun active=>rights.2.2.2 (weaken node.tag active)⟩
  · intro outside
    have rights:=prior.2 outside
    exact ⟨rights.1,fun active=>rights.2 (weaken node.tag active)⟩

def updates
    (live : Present (ActualWorld post) role.backing.id (role.backing.allocation.setExtra tree))
    (rootTag : next.global.rootTag? role.backing.id=tracker.global.rootTag? role.backing.id)
    (shape : tree={role.backing.allocation.extra with locations:=tree.locations})
    (capacity : tree.locations.size=role.backing.allocation.extra.locations.size)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree next.global)
    (flags : ∀tag,next.global.protectedTags.contains tag=true→tracker.global.protectedTags.contains tag=true)
    (rows : S05CurrentReleaseIterator.Rows (fun range location=>∃original∈role.backing.allocation.extra.locations.entries.toList,
      original.range=range ∧CurrentCallSpatialRows.Frame role original.data location) tree.locations)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) :
    CurrentCallSpatialSourceCover.Update role post next (role.backing.allocation.setExtra tree) role.family (role.roles i overlap).grant i overlap := by
  have nodes : tree.nodes=role.backing.allocation.extra.nodes := by rw [shape]
  have roots : tree.roots=role.backing.allocation.extra.roots := by rw [shape]
  have parents : ParentInterpretation tree role.backing.cells[i].completion := by
    rw [shape]
    exact (spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.parent_locations") role.backing.allocation.extra
      role.backing.cells[i].completion tree.locations role.backing.cells[i].parents
  refine ⟨⟨role.backing.cells[i].offset,role.backing.cells[i].length,role.backing.cells[i].completion,parents⟩,rfl,rfl,?_,?_,?_⟩
  · obtain ⟨node,present,mapped,binding⟩:=(role.roles i overlap).binding
    have nextPresent : tree.nodes.get (role.roles i overlap).grant=some node := by rw [nodes];exact present
    exact ⟨node,nextPresent,runtime.formed.allocator.nodeTags _ _ nextPresent,binding⟩
  · apply CurrentCallAllocationLicense.spatial (role.roles i overlap).issued post next (role.backing.allocation.setExtra tree)
    · exact live
    · exact rootTag
    · rfl
    · rfl
    · exact capacity
    · intro position root found;change tree.roots[position]?=some root;rw [roots];exact found
    · intro index node found;exact ⟨node,by change tree.nodes.get index=some node;rw [nodes];exact found,rfl,rfl,rfl,rfl⟩
    · intro first second edge;exact edge
  · intro point request cell
    refine ⟨((role.roles i overlap).available point request cell).1,?_⟩
    intro segment member lower upper index node present
    simp only [Allocation.setExtra,Allocation.mapExtra] at member lower upper present ⊢
    obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    obtain ⟨original,oldMember,rangeEq,frame⟩:=rows position valid
    have oldLower : original.range.start.toNat≤point.2 := by rw [rangeEq];exact lower
    have oldUpper : point.2<original.range.stop.toNat := by rw [rangeEq];exact upper
    have raw:=frame original oldMember rfl i overlap ⟨point,request,cell,oldLower,oldUpper⟩ index node (by rw [←nodes];exact present)
    have realized:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node present)
      ((runtime.formed.profile position valid).present index node present)
    have localRights := fun below=>raw.1 below
    have foreignRights := fun outside=>raw.2 outside
    have raw : (Below role.backing.cells[i].completion index (role.roles i overlap).grant→OrdinaryBorrowAuthority.LocalWrite (RawState tree.locations.entries[position].data index node) (next.global.protectedTags.contains node.tag)) ∧
        (¬Below role.backing.cells[i].completion index (role.roles i overlap).grant→OrdinaryBorrowAuthority.ForeignWrite (RawState tree.locations.entries[position].data index node) (next.global.protectedTags.contains node.tag)):=by
      constructor
      · intro below
        have rights:=localRights below
        exact ⟨rights.1,rights.2.1,rights.2.2.1,fun active=>rights.2.2.2 (flags node.tag active)⟩
      · intro outside
        have rights:=foreignRights outside
        exact ⟨rights.1,fun active=>rights.2 (flags node.tag active)⟩
    constructor
    · intro below
      exact (spatial_install_rule ".CurrentCallSpatialSharedCover.local_token") _ _ realized (raw.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact (spatial_install_rule ".CurrentCallSpatialSharedCover.foreign_no_clash") _ _ realized (raw.2 outside) clash
def fixed_updates
    (live : Present (ActualWorld post) role.backing.id (role.backing.allocation.setExtra tree))
    (rootTag : next.global.rootTag? role.backing.id=tracker.global.rootTag? role.backing.id)
    (shape : tree={role.backing.allocation.extra with locations:=tree.locations})
    (capacity : tree.locations.size=role.backing.allocation.extra.locations.size)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree next.global)
    (flags : ∀tag,next.global.protectedTags.contains tag=true→tracker.global.protectedTags.contains tag=true)
    (rows : S05CurrentReleaseIterator.Rows (fun range location=>∃original∈role.backing.allocation.extra.locations.entries.toList,
      original.range=range ∧CurrentCallSpatialRows.Frame role original.data location) tree.locations)
    (tag : BorTag) (parent : UniIndex)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (tagged : role.backing.allocation.extra.indexOfTag tag=some parent)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) :
    CurrentCallSpatialSourceCover.Update role post next (role.backing.allocation.setExtra tree) role.family parent i overlap := by
  have same := CurrentCallSpatialSharedCover.grant_eq role concrete tagged i overlap
  have result := updates role live rootTag shape capacity runtime flags rows i overlap
  simpa only [same] using result

end
end DuplicatePrefix.CurrentCallSpatialReleasedMutableCover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialReleasedMutableCover" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved released mutable cover dependency {dependency}"
