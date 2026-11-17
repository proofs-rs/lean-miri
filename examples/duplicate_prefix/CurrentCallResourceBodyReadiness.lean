import duplicate_prefix.CurrentCallResourceEntryFacets

namespace DuplicatePrefix.CurrentCallResourceBodyReadiness
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false

/-- Initial finite resource headroom for the body specialization. Both bounds
refer to ORIGINAL input counters, independently of any operation outcome.
The eight-slot margin is conservative, not a minimality claim. Entry itself
continues to use its unchanged, weaker Conditions. -/
structure Ready {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) : Prop where
  sourceNodes : W.allocation.extra.nodes.size+8<65536
  pointerTags : tracker.global.nextPointerTag.value.toNat+8<18446744073709551615

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : Ready C)

include ready

theorem current_nodes : (CurrentCallResourceSourceFinal.entry out).allocation.extra.nodes.size+6<65536 := by
  have growth := CurrentCallResourceEntryFacets.current_growth out
  have initial := ready.sourceNodes
  split at growth <;> omega

theorem current_tags : out.boolOutput.global.nextPointerTag.value.toNat+6<18446744073709551615 := by
  rw [CurrentCallResourceEntryFacets.tag_growth out]
  have initial := ready.pointerTags
  omega

theorem current_short : (CurrentCallResourceSourceFinal.entry out).allocation.extra.nodes.size<65536 := by
  have budget := current_nodes out ready
  omega

theorem current_room : out.boolOutput.global.nextPointerTag.value<18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  change out.boolOutput.global.nextPointerTag.value.toNat<18446744073709551615
  have budget := current_tags out ready
  omega

end DuplicatePrefix.CurrentCallResourceBodyReadiness

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceBodyReadiness" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved initial body readiness dependency {dependency}"
