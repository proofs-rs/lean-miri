import duplicate_prefix.CurrentCallOrdinaryEmptySafety
import duplicate_prefix.CurrentCallOrdinaryPositiveSafety

/-! The adopted-input dispatcher joins the empty and positive entry producers
to the original all-count Result. Representation choices remain inside those
producers.

The exhaustive entry partition is:

* `len = 0`: the actual `CurrentCallEmptyClassification.Source` constructors
  are `.integer`, `.concrete`, `.miss`, and `.hit`. Concrete and HIT targets use
  exactly `Target.live`, `Target.nonlive`, or `Target.current`. The `.nonlive`
  case packages the existing `Metadata.functionRow`, `.vaListRow`,
  `.nondataGlobal`, or `.dead` alternatives; `.current` supplies the declared
  CURRENT payload and its materialization data. Each is joined with
  an initially LIVE or CURRENT return allocation. When there is a source target,
  SAME and different allocation paths are selected from the actual IDs; a
  purported SAME allocation cannot be both LIVE and absent. Integer and MISS
  introduce no source allocation or dummy source protector. MISS preservation
  across conversion uses the declared current exposed-address cache coherence.
* `len ≠ 0`: source LIVE / return LIVE, source LIVE / return CURRENT, source
  CURRENT / return LIVE, and source CURRENT / return CURRENT. The two mixed
  initial backing cases have different IDs by the LIVE/absent lookup facts.
  The two equal-backing cases include SAME and different IDs. In the SAME
  CURRENT case, source materialization makes the Bool allocation LIVE before
  its protection, so it is not materialized a second time. Concrete and wildcard
  selected LIVE pointers retain their actual provenance; `LatentRole` states
  the CURRENT selected pointer's concrete cached-root representation.

The producers discharge these selections internally and handle every count.
This final theorem assumes neither a selected branch nor a producer factory.
`OrdinaryInput` is the declared current representation, configuration, physical
value, ownership, and resource domain. Its independent `protectorsBelow` and
`exposedCached` fields express current allocator freshness and absolute-address
cache coherence, including states without LIVE rows. Bare provenance exposure
does not imply the latter. This theorem does not establish formation of that
domain for every Rust execution history. -/
namespace DuplicatePrefix.CurrentCallOrdinarySafety
open Miri Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open CurrentCallOrdinaryInput
set_option autoImplicit false

/-- Every count is handled for the adopted current-input domain. -/
theorem invoke {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  by_cases empty : len = 0
  · exact CurrentCallOrdinaryEmptySafety.invoke input empty count
  · exact CurrentCallOrdinaryPositiveSafety.invoke input empty count

end DuplicatePrefix.CurrentCallOrdinarySafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinarySafety.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved ordinary safety dependency {name}: {dependency}"
