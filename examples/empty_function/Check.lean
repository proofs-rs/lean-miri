import empty_function.ActualNoUBFinal
import Lean

-- This type check forbids additional resource, success, or family hypotheses.
example (s : EmptyFunction.WholeCall.Static) : EmptyFunction.TotalCallGoal.Target s :=
  EmptyFunction.ActualNoUBFinal.target s

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    let spelling := name.toString
    if #["EmptyFunction.","Miri."].any (fun needle => (spelling.splitOn needle).length != 1) then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty_function UB-freedom dependency {name}: {dependency}"
  logInfo m!"Audited {count} imported EmptyFunction/Miri declarations (private/generated included)"

#print axioms EmptyFunction.ActualNoUBFinal.noUB
#print axioms EmptyFunction.ActualNoUBFinal.target
