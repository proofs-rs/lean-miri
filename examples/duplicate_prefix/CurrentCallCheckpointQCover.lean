import duplicate_prefix.CurrentCallCheckpointMutableParents
import duplicate_prefix.CurrentCallSpatialUnheldParentCover
namespace DuplicatePrefix.CurrentCallCheckpointQCover
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
noncomputable section
variable {options remaining span len count place limits} (cp : Checkpoint options remaining span len count place)
  (control : CurrentCallCheckpointLenReturn.Result cp limits) (source : CurrentCallCheckpointLenSource.Data cp control)

/-- After the actual copy retained the full S bank, reanchor the SAME fixed
current completions at P and then q. No new operation or completion selection
occurs here. The structural equations are derived by the actual copy producer. -/
theorem restore {post tracker ctx}
    (role : RoleCover post tracker ctx .mut cp.offset len.toNat)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (concrete : role.family.value.provenance=.concrete role.backing.id (CurrentCallCheckpointMutable.sOutput cp control source).tag)
    (nodes : role.backing.allocation.extra.nodes=(CurrentCallCheckpointMutable.sOutput cp control source).child.tree.nodes)
    (flags : tracker.global.protectedTags=((CurrentCallCheckpointMutable.sOutput cp control source).global.endCall (CurrentCallCheckpointMutable.sOutput cp control source).frame).protectedTags) :
    ∃context : CurrentCallSpatialCover.Context post, ∃current : RoleCover post tracker context .mut cp.offset len.toNat,
      current.backing.allocation=role.backing.allocation ∧current.backing.id=role.backing.id ∧
      current.family.value.provenance=.concrete current.backing.id cp.source.tag ∧
      current.family.value.offset=role.family.value.offset ∧
      current.backing.allocation.extra.indexOfTag cp.source.tag=some cp.source.grant := by
  obtain ⟨pIndex,sIndex,pNode,qNode,sNode,sLookup,sAt,sTag,sParent,pAt,pTag,pParent,qAt,qTag,qHidden,qActivity⟩:=CurrentCallCheckpointMutableParents.s_frame cp control source
  have currentS : role.backing.allocation.extra.nodes.get sIndex=some sNode:=by rw [nodes];exact sAt
  have currentP : role.backing.allocation.extra.nodes.get pIndex=some pNode:=by rw [nodes];exact pAt
  have currentQ : role.backing.allocation.extra.nodes.get cp.source.grant=some qNode:=by rw [nodes];exact qAt
  have sMapped : role.backing.allocation.extra.indexOfTag (CurrentCallCheckpointMutable.sOutput cp control source).tag=some sIndex:=by
    have mapped:=runtime.formed.allocator.nodeTags _ _ currentS
    rw [sTag] at mapped
    exact mapped
  have sUnheld : tracker.global.protectedTags.contains sNode.tag=false:=by rw [flags,sTag];exact CurrentCallCheckpointMutableParents.child_unheld cp control source
  let pUpdates:=CurrentCallSpatialUnheldParentCover.updates role runtime sIndex pIndex sNode pNode currentS currentP sParent
    (CurrentCallCheckpointMutable.sOutput cp control source).tag concrete sMapped sUnheld
  let pContext:=CurrentCallSpatialSourceCover.context role role.backing.live pUpdates
  let pRole:=CurrentCallSpatialSourceCover.assemble role role.backing.live pUpdates rfl
  have pConcrete : pRole.family.value.provenance=.concrete pRole.backing.id pNode.tag:=rfl
  have pMapped : pRole.backing.allocation.extra.indexOfTag pNode.tag=some pIndex:=runtime.formed.allocator.nodeTags _ _ currentP
  have pUnheld : tracker.global.protectedTags.contains pNode.tag=false:=by rw [flags,pTag];exact CurrentCallCheckpointMutableParents.parent_unheld cp control source
  let qUpdates:=CurrentCallSpatialUnheldParentCover.updates pRole runtime pIndex cp.source.grant pNode qNode currentP currentQ pParent
    pNode.tag pConcrete pMapped pUnheld
  let qContext:=CurrentCallSpatialSourceCover.context pRole pRole.backing.live qUpdates
  let qRole:=CurrentCallSpatialSourceCover.assemble pRole pRole.backing.live qUpdates rfl
  refine ⟨qContext,qRole,rfl,rfl,?_,rfl,?_⟩
  · change Provenance.concrete role.backing.id qNode.tag=Provenance.concrete role.backing.id cp.source.tag
    rw [qTag]
  · have mapped:=runtime.formed.allocator.nodeTags _ _ currentQ
    rw [qTag] at mapped
    exact mapped
end
end DuplicatePrefix.CurrentCallCheckpointQCover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointQCover" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved q-cover dependency {dependency}"
