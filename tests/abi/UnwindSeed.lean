import Miri.ABI.FnAbi
open Miri.ABI

def main : IO Unit := do
  for abi in #[ExternAbi.C false, .C true, .System true, .Rust, .RustCall,
      .Custom, .LlvmIntrinsic] do
    for definition in #[none, some ⟨false,false,false⟩, some ⟨true,false,false⟩,
        some ⟨false,true,false⟩, some ⟨true,true,false⟩, some ⟨false,false,true⟩,
        some ⟨true,false,true⟩, some ⟨false,true,true⟩, some ⟨true,true,true⟩] do
      for panic in #[false,true] do
        for drop in #[false,true] do
          let seed : UnwindSeed := ⟨abi,definition,panic,drop⟩
          IO.println seed.canUnwind
