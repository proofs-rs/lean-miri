import Miri.Input.CompilerTables
import Miri.MIR.SyntaxTables

namespace Miri.Input.Reader.MIRReader
open Miri.MIR

structure State where
  tables : SyntaxTables
  compiler : CompilerTables
  definitions : Std.HashMap (Nat × Nat) Nat
  regions : SharedTable Region
  arguments : SharedTable (Array GenericArg)
  typeConstantIds : SharedTable TypeConstId
  spanIds : SharedTable SpanRef
  patternReferences : SharedTable Nat
  patterns : Array PatternData := #[]
  projectionLocals : SharedTable Nat
  listLocals : SharedTable Nat
  placeLocals : SharedTable Nat
  threadLocals : Array (DefId × Except String ThreadLocalQueryData) := #[]

abbrev Decode := StateT State (Except String)

def initial (slots : Nat) (compiler : CompilerTables) : State := Id.run do
  let mut definitions := {}
  for (id, index) in compiler.definitions.toList.zipIdx do
    definitions := definitions.insert (id.crateIndex, id.index) index
  return {
    compiler, definitions
    tables := {
      projections := Array.replicate slots none
      projectionLists := Array.replicate slots none
      places := Array.replicate slots none
      operands := Array.replicate slots none
      operandLists := Array.replicate slots none
      constants := Array.replicate slots none
      rvalues := Array.replicate slots none
      statements := Array.replicate slots none
      terminators := Array.replicate slots none
      blocks := Array.replicate slots none
      bodies := Array.replicate slots none }
    regions := Array.replicate slots none
    arguments := Array.replicate slots none
    typeConstantIds := Array.replicate slots none
    spanIds := Array.replicate slots none
    patternReferences := Array.replicate slots none
    projectionLocals := Array.replicate slots none
    listLocals := Array.replicate slots none
    placeLocals := Array.replicate slots none }

end Miri.Input.Reader.MIRReader
