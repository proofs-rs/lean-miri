import duplicate_prefix.CurrentCallSpatialSubrange
import duplicate_prefix.CurrentCallSpatialReleasedCover
namespace DuplicatePrefix.CurrentCallSpatialSubrangeInstall
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open GeneralBorrowExposedConditionalRangeFrames
open CurrentCallSpatialCover CurrentCallResourceNormalization GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {before tracker ctx offset length} (role : RoleCover before tracker ctx .mut offset length)
    {post : Before} (updated : Allocation Provenance BorrowTree)
    (live : Present (ActualWorld post) role.backing.id updated)
    (lengthEq : updated.len=role.backing.allocation.len)
    (bytesEq : updated.byteSize=role.backing.allocation.byteSize)
    (shape : updated.extra={role.backing.allocation.extra with locations:=updated.extra.locations})
    (capacity : updated.extra.locations.size=role.backing.allocation.extra.locations.size)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global)
    (frames : Origins (CurrentCallSpatialRows.Frame role) role.backing.allocation.extra.locations updated.extra.locations)

/-- Reuse the existing full-source assembler on the actual updated allocation.
Byte storage may change; the retained row/cell bank and metadata license it. -/
def updates (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) :
    CurrentCallSpatialSourceCover.Update role post tracker updated role.family (role.roles i overlap).grant i overlap := by
  have nodes : updated.extra.nodes=role.backing.allocation.extra.nodes:=by rw [shape]
  have roots : updated.extra.roots=role.backing.allocation.extra.roots:=by rw [shape]
  have parents : ParentInterpretation updated.extra role.backing.cells[i].completion:=by
    rw [shape]
    exact (spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.parent_locations") role.backing.allocation.extra
      role.backing.cells[i].completion updated.extra.locations role.backing.cells[i].parents
  refine ⟨⟨role.backing.cells[i].offset,role.backing.cells[i].length,role.backing.cells[i].completion,parents⟩,rfl,rfl,?_,?_,?_⟩
  · obtain ⟨node,present,mapped,binding⟩:=(role.roles i overlap).binding
    have nextPresent : updated.extra.nodes.get (role.roles i overlap).grant=some node:=by rw [nodes];exact present
    exact ⟨node,nextPresent,runtime.formed.allocator.nodeTags _ _ nextPresent,binding⟩
  · apply CurrentCallAllocationLicense.spatial (role.roles i overlap).issued post tracker updated live rfl lengthEq bytesEq capacity
    · intro position root found;rw [roots];exact found
    · intro index node found;exact ⟨node,by rw [nodes];exact found,rfl,rfl,rfl,rfl⟩
    · intro first second edge;exact edge
  · intro point request cell
    refine ⟨by rw [lengthEq];exact ((role.roles i overlap).available point request cell).1,?_⟩
    intro segment member lower upper index node present
    obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have bound:=((role.roles i overlap).available point request cell).1
    rw [(role.roles i overlap).issued.capability.extent] at bound
    have fit : point.2<2^64:=Nat.lt_trans bound role.backing.allocation.byteSize.bytes.toNat_lt
    have pointEq : (UInt64.ofNat point.2).toNat=point.2:=Nat.mod_eq_of_lt fit
    have atPoint : ValueAt updated.extra.locations (UInt64.ofNat point.2) updated.extra.locations.entries[position].data:=
      ⟨position,valid,by rw [pointEq];exact lower,by rw [pointEq];exact upper,rfl⟩
    have pointRequest : Window role.backing.id offset length (role.backing.id,(UInt64.ofNat point.2).toNat):=
      ⟨rfl,by rw [pointEq];exact request.2.1,by rw [pointEq];exact request.2.2⟩
    have pointCell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length
        (role.backing.id,(UInt64.ofNat point.2).toNat):=
      ⟨rfl,by rw [pointEq];exact cell.2.1,by rw [pointEq];exact cell.2.2⟩
    have rights:=CurrentCallSpatialRows.recover role updated.extra.locations frames (UInt64.ofNat point.2)
      _ atPoint pointRequest i overlap pointCell
    have raw:=rights index node (by rw [←nodes];exact present)
    have realized:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node present)
      ((runtime.formed.profile position valid).present index node present)
    constructor
    · intro below
      exact (spatial_install_rule ".CurrentCallSpatialSharedCover.local_token") _ _ realized (raw.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact (spatial_install_rule ".CurrentCallSpatialSharedCover.foreign_no_clash") _ _ realized (raw.2 outside) clash

include live lengthEq bytesEq shape capacity runtime frames in
theorem cover (tag : BorTag) (grant : UniIndex)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (tagged : role.backing.allocation.extra.indexOfTag tag=some grant) :
    ∃context : Context post,∃current : RoleCover post tracker context .mut offset length,
      current.backing.allocation=updated ∧current.backing.id=role.backing.id ∧current.family=role.family := by
  let next : ∀i overlap,CurrentCallSpatialSourceCover.Update role post tracker updated role.family grant i overlap:=by
    intro i overlap
    have result:=updates role updated live lengthEq bytesEq shape capacity runtime frames i overlap
    have same:=CurrentCallSpatialSharedCover.grant_eq role concrete tagged i overlap
    simpa only [same] using result
  exact ⟨CurrentCallSpatialSourceCover.context role live next,
    CurrentCallSpatialSourceCover.assemble role live next role.id,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallSpatialSubrangeInstall
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialSubrangeInstall" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved subrange actual-allocation transport dependency {dependency}"
