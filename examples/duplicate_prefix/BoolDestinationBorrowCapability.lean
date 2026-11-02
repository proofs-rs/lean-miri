import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.ChildBorrow
import Miri.Interpreter.MachineHooks

namespace DuplicatePrefix.BoolDestinationBorrowCapability
open Miri Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open DuplicatePrefixScalarAuthorization GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The actual return-place protector policy creates an accessed reservation
and therefore requests a parent Tree Borrows Read. This is an aliasing access,
not a load of the old bool byte: no initialization or bool value occurs here.
Pinned sources: tree_borrows/mod.rs tb_protect_place and tb_reborrow, and
perms.rs associated_access. Call.initStackFrame protects destinationMplace even
for the direct bool return ABI; TypedRetag then writes uninit via the child. -/
theorem return_protector_read (frozen : Bool) :
    RetagPolicy.initialLocationState MachineHooks.protectionPolicy frozen =
      .ok ChildBorrow.fnEntryLocation ∧
    ChildBorrow.fnEntryLocation.permission.associatedAccess = some .Read := by
  cases frozen <;> exact ⟨rfl, rfl⟩

/-- At the SAME exact relation, raw Write-compatible scalar permissions already
supply Read compatibility. Possible-state invariants exclude an inactive
protected Unique; no successful access or old-byte initialization is assumed.
This does not compare wildcard classifications or their support counts. -/
theorem write_implies_read (state : LocationState) (related : AccessRelatedness)
    (held : Bool) (write : Compatible state .Write related held) :
    Compatible state .Read related held := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp_all [Compatible, GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible, LocationState.possible,
        Permission.isUnique]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp_all [Compatible, GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible, LocationState.possible,
        Permission.isUnique]

/-- The parent's scalar Read is derived from raw write capability; the actual
transition is the conclusion. This does not certify the whole forest visitor. -/
theorem scalar_parent_read (state : LocationState) (related : AccessRelatedness)
    (held : Bool) (write : Compatible state .Write related held) :
    ∃ next delta, state.performAccess .Read related held = .Success next delta := by
  have read := write_implies_read state related held write
  exact (compatible_iff state .Read related held read.1).mp read

/-- Initial Write capability also survives the real scalar parent Read when
the exact relation is unchanged. Thus the protector's aliasing Read imposes no
additional scalar capability on that relation. Changes to traversal relations
or callback queries are outside this local theorem. -/
theorem read_preserves_write (state : LocationState) (related : AccessRelatedness)
    (held : Bool) (write : Compatible state .Write related held) :
    ∃ next delta, state.performAccess .Read related held = .Success next delta ∧
      Compatible next .Write related held := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible, GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique] at write <;>
      (refine ⟨_, _, rfl, ?_⟩; simp [Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible, LocationState.possible,
        Permission.isUnique, AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible, GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique] at write <;>
      (refine ⟨_, _, rfl, ?_⟩; simp [Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible, LocationState.possible,
        Permission.isUnique, AccessRelatedness.isForeign])

/-- The concrete normal component's separate initial Read clause is redundant:
raw Write-compatible node data constructs the existing two-kind normal packet.
This is a useful relaxation ONLY for exact normal relations. Whole-row callback
Read authorization cannot be dropped by this theorem: Read and Write compute
different wildcard relations and residual supporter/removal queries.

Consequently the weakest raw scalar destination requirement is Write at each
actually visited exact relation (plus possible-state WF already inside it).
Complete ordinary destination coverage still requires the actual Read retag,
child Write/uninit, protector release and final caller-pointer Write traversal
obligations, with their evolving query states. No all-destination claim follows. -/
theorem normal_from_writes (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (source : UniIndex)
    (component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection tree default protections).topology source.toNat)
    (writes : ∀ index, component.support index → index < tree.nodes.data.size →
      ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
        Compatible state .Write
          (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index)
          ((source_normal_projection tree location protections).protectedNodes.contains index)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location protections source) := by
  refine ⟨⟨component, ?_⟩⟩
  intro kind index supported bound
  obtain ⟨state, present, write⟩ := writes index supported bound
  refine ⟨state, present, ?_⟩
  cases kind with
  | Read => exact write_implies_read state _ _ write
  | Write => exact write

end DuplicatePrefix.BoolDestinationBorrowCapability
