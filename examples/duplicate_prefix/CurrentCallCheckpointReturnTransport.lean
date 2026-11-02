import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.CurrentCallSpatialControlView
import duplicate_prefix.CurrentCallResourceCurrentRelease

namespace DuplicatePrefix.CurrentCallCheckpointReturnTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint
set_option autoImplicit false
noncomputable section

private def window {before after tracker data owner id offset length mode}
    (old : UniformWindow before tracker data owner id offset length mode) (memory : after.memory=before.memory) :
    UniformWindow after tracker data owner id offset length mode where
  loan:=old.loan;pointer:=old.pointer;allocation:=old.allocation;precise:=old.precise
  loanAt:=old.loanAt;pointerAt:=old.pointerAt;pointerId:=old.pointerId
  present:=by unfold ActualWorld;rw [memory];exact old.present
  preciseAt:=old.preciseAt
  binding:=old.binding
  issued:=CurrentCallSpatialControlView.issued old.issued (by unfold ActualWorld;rw [memory])
  parents:=old.parents
  window:=old.window

/-- Accounting-only control steps retain the same actual allocation/family. -/
def move {before tracker place} (old : Return before tracker place) (after : Before)
    (memory : after.memory=before.memory) (addresses : after.user.addresses=before.user.addresses)
    (extras : after.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras) :
    Return after tracker place where
  data:=old.data;owner:=old.owner;id:=old.id;offset:=old.offset
  window:=window old.window memory
  physical:={old.physical with
    live:=by rw [memory];exact old.physical.live
    cachedBase:=by rw [addresses];exact old.physical.cachedBase}
  physicalId:=old.physicalId;physicalOffset:=old.physicalOffset;physicalAllocation:=old.physicalAllocation
  binding:=by
    obtain ⟨entry,base,live,cached,storage,room,bounds,address,nonnull,provenance⟩:=old.binding
    refine ⟨entry,base,?_,?_,storage,room,bounds,address,nonnull,?_⟩
    · rw [memory];exact live
    · rw [addresses];exact cached
    · cases value : old.physical.pointer.provenance with
      | concrete id tag => simpa only [value] using provenance
      | wildcard =>
        change after.user.addresses.provenanceMode≠.strict ∧after.user.addresses.exposed.contains old.id=true ∧
          WildcardGeneralHitReborrow.Geometry after.user.addresses.intToPtrMap old.physical.pointer.offset.bytes base old.id entry.allocation.byteSize
        rw [addresses]
        simpa only [value] using provenance
  original:=old.original;originalId:=old.originalId;originalPointer:=old.originalPointer
  originalIssued:=CurrentCallSpatialControlView.issued old.originalIssued (by unfold ActualWorld;rw [memory])
  originalBinding:=old.originalBinding;edge:=old.edge
  runtime:=old.runtime;distinct:=old.distinct;short:=old.short
  node:=old.node;nodeAt:=old.nodeAt;leaf:=old.leaf;hidden:=old.hidden;activity:=old.activity
  profile:=old.profile.transport extras

def released {before tracker place} (old : Return before tracker place) (after : Before)
    (memory : after.memory=before.memory) (addresses : after.user.addresses=before.user.addresses)
    (extras : after.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras)
    (frame : FrameState)
    (ready : CurrentCallResourceCurrentRelease.Released old.window frame old.original.grant old.physical.offset old.physical.entry) :
    CurrentCallResourceCurrentRelease.Released (move old after memory addresses extras).window frame
      old.original.grant old.physical.offset old.physical.entry where
  memory:=ready.memory;tree:=ready.tree
  plan:=by rw [memory];exact ready.plan
  live:=ready.live;runtime:=ready.runtime;parents:=ready.parents;shape:=ready.shape;capacity:=ready.capacity
  distinct:=ready.distinct;short:=ready.short;owned:=ready.owned

end
end DuplicatePrefix.CurrentCallCheckpointReturnTransport
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointReturnTransport" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current return transport dependency {dependency}"
