import duplicate_prefix.CurrentCallCheckpointMutableCurrent
import duplicate_prefix.CurrentCallResourceLenCapability
import duplicate_prefix.S05CompletedChildReanchor
namespace DuplicatePrefix.CurrentCallSpatialUnheldParentCover
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

private theorem root_below_parent {before tracker id allocation C child parent}
    (issued : SpatialDelegation before tracker id allocation C child)
    (parents : ParentInterpretation allocation.extra C)
    (node : TreeNode) (present : allocation.extra.nodes.get child=some node) (physical : node.parent=some parent) :
    Below C allocationRoot parent := by
  have below:=issued.root_below parents
  cases below with
  | refl =>
    obtain ⟨root,rootAt,parentless,_⟩:=issued.capability.rootNode
    have same : root=node:=Option.some.inj (rootAt.symm.trans present)
    rw [same,physical] at parentless
    cases parentless
  | @step previous _ edge prior =>
    have same : previous=parent:=Option.some.inj (Option.some.inj (edge.symm.trans (parents.physical child node present parent physical)))
    subst previous
    exact prior

variable {before tracker ctx offset length} (role : RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (child parent : UniIndex) (node parentNode : TreeNode)
    (present : role.backing.allocation.extra.nodes.get child=some node)
    (parentAt : role.backing.allocation.extra.nodes.get parent=some parentNode)
    (physical : node.parent=some parent)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (tagged : role.backing.allocation.extra.indexOfTag tag=some child)
    (unheld : tracker.global.protectedTags.contains node.tag=false)

def family (parentNode : TreeNode) : Family:=⟨role.family.slot,role.backing.id,Pointer.new (.concrete role.backing.id parentNode.tag) role.family.value.offset⟩

/-- Reanchor a released concrete child at its real unprotected parent, keeping
all chosen current completions fixed. This is a resource consequence, not a
second interpreter operation. -/
def updates (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) :
    CurrentCallSpatialSourceCover.Update role before tracker role.backing.allocation (family role parentNode) parent i overlap := by
  have grant : (role.roles i overlap).grant=child:=CurrentCallSpatialSharedCover.grant_eq role concrete tagged i overlap
  let parents:=role.backing.cells[i].parents
  have issued : SpatialDelegation before tracker role.backing.id role.backing.allocation role.backing.cells[i].completion child:=by rw [←grant];exact (role.roles i overlap).issued
  refine ⟨role.backing.cells[i],rfl,rfl,?_,?_,?_⟩
  · exact ⟨parentNode,parentAt,runtime.formed.allocator.nodeTags _ _ parentAt,rfl,rfl⟩
  · exact CurrentCallResourceLenCapability.issued_of_rootBelow issued.capability parents (root_below_parent issued parents node present physical)
  · intro point request cell
    refine ⟨((role.roles i overlap).available point request cell).1,?_⟩
    intro segment member lower upper index actual actualAt
    have frames:=CurrentCallSpatialRows.initial_authority role rfl
      (by intro segment member;obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member);rw [←same];exact runtime.formed.profile position valid)
      (by intro segment member;obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member);rw [←same];exact runtime.possible position valid)
    have raw:=frames segment.data segment member rfl i overlap ⟨point,request,cell,lower,upper⟩
    rw [grant] at raw
    have restored:=S05CompletedChildReanchor.authority role.backing.allocation.extra role.backing.cells[i].completion segment.data tracker.global.protectedTags tracker.global.protectedTags child parent node
      (parents.physical child node present parent physical) present (fun _ held=>held) unheld raw
    have rights:=restored index actual actualAt
    obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    have realized:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index actual actualAt)
      ((runtime.formed.profile position valid).present index actual actualAt)
    rw [same] at realized
    constructor
    · intro below
      exact (spatial_install_rule ".CurrentCallResourceFnEntry.local_token") _ _ realized (rights.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact (spatial_install_rule ".CurrentCallResourceFnEntry.foreign_no_clash") _ _ realized (rights.2 outside) clash

end
end DuplicatePrefix.CurrentCallSpatialUnheldParentCover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialUnheldParentCover" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved unheld parent cover dependency {dependency}"
