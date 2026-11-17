import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentLive
import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentSameSafety
import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentDifferentSafety
/-! CURRENT empty-source endpoints dispatch only on actual return backing and
allocation identity. Every operation is discharged by the selected branch. -/
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536

theorem concrete_raw {options limits remaining span before place}
    (id : AllocId) (rootTag : BorTag) (base offset : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 place)
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (registry : InitialRegistryVacant before id)
    (cachedRoot : input.tracker.global.rootTag? id=some rootTag)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (nonnull : base+offset≠0)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 count place := by
  rcases input.returnBacking with live | latent
  · exact CurrentCallOrdinaryEmptyCurrentLive.concrete_raw id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull live count
  · by_cases same : id=input.returnFamily.allocation
    · exact CurrentCallOrdinaryEmptyCurrentSameSafety.concrete_raw id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull latent same count
    · exact CurrentCallOrdinaryEmptyCurrentDifferentSafety.concrete_raw id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull latent same count

theorem wildcard_raw {options limits remaining span before place}
    (id : AllocId) (rootTag : BorTag) (base offset : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0 place)
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (registry : InitialRegistryVacant before id)
    (cachedRoot : input.tracker.global.rootTag? id=some rootTag)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (nonnull : base+offset≠0)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : before.user.addresses.exposed.contains id=true)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0 count place := by
  rcases input.returnBacking with live | latent
  · exact CurrentCallOrdinaryEmptyCurrentLive.wildcard_raw id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull geometry exposed live count
  · by_cases same : id=input.returnFamily.allocation
    · exact CurrentCallOrdinaryEmptyCurrentSameSafety.wildcard_raw id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull geometry exposed latent same count
    · exact CurrentCallOrdinaryEmptyCurrentDifferentSafety.wildcard_raw id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull geometry exposed latent same count

end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentSafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyCurrentSafety.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved CURRENT empty Result dependency {name}: {dependency}"
