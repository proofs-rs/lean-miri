import Miri.Input.RelativeDiscriminants
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open Miri.Input
private def representation : ReprOptions := ⟨none,none,none,0,none,0⟩
private def declaration (count : Nat) : AdtDeclaration.Material :=
  ⟨representation,1,none,(Array.range count).map (fun index =>
    ⟨⟨0,index⟩,none,toString index,.relative index,0,0⟩),#[],false⟩
private def rejects (result : Except String α) : Bool := !result.isOk
example : RelativeDiscriminants.values 64 (declaration 3) =
    .ok (some #[0,1,2]) := by cbv
example : RelativeDiscriminants.values 32 (declaration 0) = .ok (some #[]) := by cbv
example : rejects (RelativeDiscriminants.values 64 {declaration 1 with flagsBits := 2}) = true := by cbv
example : rejects (RelativeDiscriminants.values 64 {declaration 2 with variants :=
    #[⟨⟨0,0⟩,none,"a",.relative 0,0,0⟩,⟨⟨0,1⟩,none,"b",.relative 0,0,0⟩]}) = true := by cbv
example : RelativeDiscriminants.values 64 {declaration 1 with variants :=
    #[⟨⟨0,0⟩,none,"a",.explicit ⟨0,5⟩,0,0⟩]} = .ok none := by cbv
#eval (show IO Unit from do
  unless rejects (RelativeDiscriminants.values 64 {declaration 129 with
      representation := {representation with integer := some (.fixed (.known .i8) 8 true)}}) do
    throw (IO.userError "signed default discriminant overflow accepted")
  unless rejects (RelativeDiscriminants.values 64 {declaration 257 with
      representation := {representation with integer := some (.fixed (.known .u8) 8 false)}}) do
    throw (IO.userError "unsigned default discriminant overflow accepted"))
example : rejects (RelativeDiscriminants.values 64 {declaration 1 with
    representation := {representation with integer := some (.fixed (.known .u8) 16 false)}}) = true := by cbv
example : rejects (RelativeDiscriminants.values 7 (declaration 1)) = true := by cbv
