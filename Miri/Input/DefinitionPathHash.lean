import Miri.Input.DefinitionPath
import Miri.Input.StableSipHash

/-! Pinned rustc DefKey::compute_stable_hash. StableCrateId is an atomic
identity stored in compiled crate metadata. DefPathHash is reconstructed from
that identity and the complete raw DefKey chain, never seeded as a hash answer.
The local crate uses the same identity format as external crates. -/
namespace Miri.Input.DefinitionPathHash

private def le (width value : Nat) : ByteArray :=
  ⟨(Array.range width).map (fun index => UInt8.ofNat (value / 2^(8*index)))⟩

private def discriminator : String → Except String Nat
  | "crate_root" => pure 0 | "impl" => pure 1 | "foreign_module" => pure 2
  | "use" => pure 3 | "global_asm" => pure 4 | "type" => pure 5
  | "value" => pure 6 | "macro" => pure 7 | "lifetime" => pure 8
  | "closure" => pure 9 | "test_binder_constraints" => pure 10
  | "constructor" => pure 11 | "anonymous_constant" => pure 12
  | "opaque_type" => pure 13 | "opaque_lifetime" => pure 14
  | "anonymous_associated_type" => pure 15 | "synthetic_coroutine_body" => pure 16
  | "nested_static" => pure 17 | _ => throw "unknown DefPathData hash discriminator"

/-- The root local hash is the StableCrateId itself. Each child hashes the
parent's local u64, its exact enum payload and its u32 disambiguator.
StableHasher::write_isize encodes these nonnegative discriminants (all below
255) as one byte; this is not an assumption about Rust enum memory layout. -/
def query (material : DefinitionPath.Material) : Except String Miri.ABI.U128 := do
  let some root := material.components[0]? | throw "DefPathHash source root is absent"
  unless root.kind == "crate_root" && root.disambiguator == 0 && root.name.isSome do
    throw "DefPathHash source root is malformed"
  let mut localHash := material.stableCrateId
  for component in material.components.extract 1 material.components.size do
    unless component.kind != "crate_root" && component.disambiguator < 2^32 do
      throw "DefPathHash source component is malformed"
    let ordinal ← discriminator component.kind
    let named := [5,6,7,8,14,15].contains ordinal
    unless named == component.name.isSome do throw "DefPathHash symbol/family mismatch"
    let mut bytes := le 8 localHash.toNat ++ le 1 ordinal
    if let some name := component.name then
      bytes := bytes ++ name.toUTF8 ++ ⟨#[255]⟩
    bytes := bytes ++ le 4 component.disambiguator
    localHash := UInt64.ofNat (StableSipHash.hash bytes).toNat
  pure (BitVec.ofNat 128 (material.stableCrateId.toNat + localHash.toNat * 2^64))

end Miri.Input.DefinitionPathHash
