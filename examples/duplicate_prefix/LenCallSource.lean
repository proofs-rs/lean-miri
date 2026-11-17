import duplicate_prefix.LenCallFacts
namespace DuplicatePrefix.LenCallSource
open Miri Miri.Input Miri.Interpreter
noncomputable def callTerminator := (RootBody.reflected.body.body.basicBlocks[2]'(by decide +kernel)).terminator
end DuplicatePrefix.LenCallSource
