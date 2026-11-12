import Miri.Input.DefinitionPath
open Miri.Input.DefinitionPath
private def root : Component := ⟨"crate_root",some "source_crate",0⟩
private def nested : Material := ⟨#[root,⟨"type",some "nested",0⟩,⟨"type",some "Wrap",0⟩],0,#[false],none⟩
private def succeeds (value : Except String String) (expected : String) : Bool :=
  match value with | .ok value => value == expected | .error _ => false
private def fails (value : Except String String) : Bool :=
  match value with | .ok _ => false | .error _ => true
example : succeeds (localNamedPath nested false false false) "nested::Wrap" = true := by decide
example : fails (localNamedPath nested false true true) = true := by decide
example : fails (localNamedPath nested true false false) = true := by decide
example : fails (localNamedPath {nested with components := #[root,⟨"impl",none,0⟩,⟨"type",some "Wrap",0⟩]} false false false) = true := by decide
example : fails (localNamedPath {nested with components := #[root,⟨"type",some "type",0⟩]} false false false) = true := by decide
