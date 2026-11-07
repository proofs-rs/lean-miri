import Miri.Input.Reader.PlaceTypes

open Miri.MIR Miri.Input.Reader

private def tables : SyntaxTables := Id.run do
  let info : SourceInfo := ⟨⟨0⟩,0⟩
  let places := (Array.range 3).map fun ty => some (PlaceNode.mk ty 0 ⟨0⟩)
  let operands := (Array.range 3).map fun id => some (OperandNode.Copy ⟨id⟩)
  let rvalues : SharedTable RvalueNode := (Array.range 3).map fun id => some (.Use ⟨id⟩ .No)
  let statements := (Array.range 3).map fun id => some (StatementNode.mk info (.Assign ⟨id⟩ ⟨id⟩))
  let mut blocks := (Array.range 3).map fun id => some (BlockNode.mk #[⟨id⟩] ⟨0⟩ false)
  blocks := blocks.push (some ⟨#[⟨0⟩,⟨0⟩],⟨0⟩,false⟩)
  blocks := blocks.push (some ⟨#[⟨1⟩,⟨2⟩],⟨0⟩,false⟩)
  let bodies := (Array.range 5).map fun id => some (BodyNode.mk (.Runtime .Optimized) 0 none #[0] #[⟨id⟩] 1 #[])
  return {
    places, operands, rvalues, statements, blocks, bodies
    projectionLists := #[some #[]]
    terminators := #[some ⟨info,.Return⟩]}

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let .ok first := PlaceTypeReader.build tables ⟨0⟩ ⟨1⟩ | throw (IO.userError "first normalized body failed")
  let .ok second := PlaceTypeReader.build tables ⟨0⟩ ⟨2⟩ | throw (IO.userError "second normalized body failed")
  require (first.places.lookup 0 == .ok 1 && second.places.lookup 0 == .ok 2) "normalized type escaped its body mapping"
  require (!(first.places.lookup 1).isOk && !(second.places.lookup 2).isOk) "normalized counterpart accepted as source place"
  require (!(PlaceTypeReader.build tables ⟨3⟩ ⟨4⟩).isOk) "conflicting normalized types accepted"
  require (!(PlaceTypeReader.build tables ⟨0⟩ ⟨3⟩).isOk) "changed block length accepted"
  require (!(PlaceTypeReader.build tables ⟨5⟩ ⟨0⟩).isOk) "invalid source body ID accepted"
  IO.println "place type maps: PASS (body isolation, source IDs, conflicts, shape and bounds)"
