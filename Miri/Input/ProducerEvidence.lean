import Miri.Input.Model

/-! Explicit MIR producer settings and consumed-artifact identities. Source:
Miri lib.rs::MIRI_DEFAULT_ARGS (190-211), bin/miri.rs driver setup; exporter
producer.rs records actual compiler session settings and hashes the consumed
crate artifacts. Comparison to a reference is conditional on that reference's
provenance; it does not certify Rust behavior or establish UB freedom. -/
namespace Miri.Input.ProducerEvidence
abbrev Result := Except String
abbrev Artifact := Catalog.Artifact
abbrev Settings := Catalog.ProducerSettings

def ofDocument (document : ImportDocument) : Result Settings :=
  pure document.producerSettings

def pinnedMiriDefaultArgs : Array String := #[
  "--cfg=miri", "-Zalways-encode-mir", "-Zextra-const-ub-checks", "-Zmir-preserve-ub",
  "-Zmir-opt-level=0", "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
  "-Zmir-enable-passes=-ReferencePropagation,-GVN", "-Zdeduplicate-diagnostics=no"]

/-- Retain every explicit cfg argument in its original compiler syntax.
This does not infer built-in target cfgs from a target triple. -/
def requestedCfgs (settings : Settings) : Array String := Id.run do
  let mut values := #[]
  let mut pending := false
  for arg in settings.rustcArgs do
    if pending then values := values.push arg; pending := false
    else if arg == "--cfg" then pending := true
    else if arg.startsWith "--cfg=" then values := values.push (arg.drop 6).toString
  return values

/-- Compare actual producer inputs to an independently pinned reference.
Reference trust and source-to-MIR correctness remain explicit external
assumptions. Both sysroot and non-sysroot consumed artifacts must match. -/
def compareReferenceInputs (actual reference : Settings) : Result Unit := do
  unless actual.miriDefaultArgs == pinnedMiriDefaultArgs && reference.miriDefaultArgs == pinnedMiriDefaultArgs do
    throw "producer does not record the pinned Miri default arguments"
  unless actual.requestedCfgMiri && reference.requestedCfgMiri do throw "cfg(miri) was not requested for both producers"
  unless requestedCfgs actual == requestedCfgs reference do throw "producer cfg inputs differ"
  unless actual.mirOptLevel == some 0 && reference.mirOptLevel == some 0 do
    throw "producer MIR optimization settings do not match supported pinned configuration"
  unless actual.mirPreserveUb && actual.extraConstUbChecks && actual.alwaysEncodeMir && !actual.deduplicateDiagnostics do
    throw "actual producer does not preserve required Miri MIR settings"
  unless reference.mirPreserveUb && reference.extraConstUbChecks && reference.alwaysEncodeMir && !reference.deduplicateDiagnostics do
    throw "reference does not preserve required Miri MIR settings"
  unless actual.mirEnablePasses == reference.mirEnablePasses do throw "producer MIR pass overrides differ"
  unless actual.effectivePanicStrategy == reference.effectivePanicStrategy do throw "producer panic strategies differ"
  unless actual.sysrootManifestSha256 == reference.sysrootManifestSha256 do throw "producer sysroot artifact manifests differ"
  unless actual.loadedArtifactsManifestSha256 == reference.loadedArtifactsManifestSha256 do throw "producer consumed dependency artifacts differ"

end Miri.Input.ProducerEvidence
