import duplicate_prefix.CurrentCallResourceCurrentRelease
import duplicate_prefix.CurrentCallResourceRootPhysical
namespace DuplicatePrefix.CurrentCallResourceSameHeap
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
/-- Pure control steps change neither allocation/family interpretation nor
protector flags. Transport only the exact current heap, with no new charge. -/
theorem issued {before after tracker id allocation completion grant}
    (memory : after.memory=before.memory)
    (old : SpatialDelegation before tracker id allocation completion grant) :
    SpatialDelegation after tracker id allocation completion grant := by
  induction old with
  | allocated cap =>
    exact .allocated ⟨by simpa only [ActualWorld,memory] using cap.live,cap.extent,cap.treeExtent,cap.rootSlot,cap.rootNode⟩
  | concrete _ path ih => exact .concrete ih path
  | @wildcard origin root originNode rootNode earlier position originRoot prior originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge

def window {before after tracker data owner id offset length mode}
    (memory : after.memory=before.memory)
    (W : UniformWindow before tracker data owner id offset length mode) :
    UniformWindow after tracker data owner id offset length mode where
  loan:=W.loan;pointer:=W.pointer;allocation:=W.allocation;precise:=W.precise
  loanAt:=W.loanAt;pointerAt:=W.pointerAt;pointerId:=W.pointerId
  present:=by simpa only [ActualWorld,memory] using W.present
  preciseAt:=W.preciseAt;binding:=W.binding;issued:=issued memory W.issued
  parents:=W.parents;window:=W.window

theorem binding {before after pointer id offset length}
    (memory : after.memory=before.memory) (addresses : after.user.addresses=before.user.addresses)
    (old : CandidateCallBindings.WindowBinding before pointer id offset length) :
    CandidateCallBindings.WindowBinding after pointer id offset length := by
  simpa only [CandidateCallBindings.WindowBinding,memory,addresses] using old

def scalar {before after place}
    (memory : after.memory=before.memory) (addresses : after.user.addresses=before.user.addresses)
    (W : CurrentCallBoolScalarWrite.Window before place) : CurrentCallBoolScalarWrite.Window after place :=
  {W with live:=by rw [memory];exact W.live,cachedBase:=by rw [addresses];exact W.cachedBase}

def released {before : DuplicatePrefixCallSpecification.Before} {after : DuplicatePrefixCallSpecification.Before} {tracker data owner id offset frame original start entry}
    {B : UniformWindow before tracker data owner id offset 1 .ret}
    (memory : after.memory=before.memory)
    (old : CurrentCallResourceCurrentRelease.Released B frame original start entry) :
    CurrentCallResourceCurrentRelease.Released (window memory B) frame original start entry where
  memory:=old.memory;tree:=old.tree
  plan:=by change StackPopRelease.Plan _ _ after.memory _;rw [memory];exact old.plan
  live:=old.live;runtime:=old.runtime;parents:=old.parents;shape:=old.shape;capacity:=old.capacity
  distinct:=old.distinct;short:=old.short;owned:=old.owned
end
end DuplicatePrefix.CurrentCallResourceSameHeap
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSameHeap" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved exact same-heap resource dependency {dependency}"
