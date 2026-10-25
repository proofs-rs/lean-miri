import Miri.Input.Decoder

/- The profiler wrapper is definitionally transparent, including for arbitrary
   options, so it cannot alter either successful values or diagnostics. -/
theorem runtime_decoder_profile_identity (text : String) (opts : Lean.Options) :
    Miri.Input.decodeRuntimeJsonProfiled text opts =
      Miri.Input.decodeRuntimeJson text := rfl

#print axioms runtime_decoder_profile_identity
