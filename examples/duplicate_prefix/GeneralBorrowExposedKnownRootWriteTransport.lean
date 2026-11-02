import duplicate_prefix.GeneralBorrowExposedKnownRootWritePrimaryWitness
import duplicate_prefix.GeneralBorrowExposedScopedNormalCache
namespace DuplicatePrefix.GeneralBorrowExposedKnownRootWriteTransport
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootWriteState
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Rebase other-component input records on the derived normal poststate.
Only global coherence and scoped readability change with location data. -/
def rebase {tree initial root protections} (data : Data tree initial root protections) (current : LocationTree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (profile : Profile tree current protections) : Data tree current root protections where
  support := data.support
  rooted := data.rooted
  present := data.present
  children := data.children
  covers := data.covers
  coherent := coherent
  short := data.short
  depth := data.depth
  included := data.included
  profile := profile

/-- Scoped normal access cannot change any other-component condition,
including initial cache-sensitive protected Unique/ReservedIM allowances. -/
theorem profile (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (cache : current.exposedCache = initial.exposedCache)
    (perms : ∀ index node,area.support index → tree.nodes.get index = some node → current.perms.get index = initial.perms.get index)
    (profile : Profile tree initial protections) : Profile tree current protections := by
  intro index node member present
  simpa only [GeneralBorrowWildcardVirtualLeaf.effective,zero,cache,perms index node member present] using profile index node member present

def primary {tree initial root protections} (data : GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree initial root protections)
    (current : LocationTree) (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (profile : Profile tree current protections)
    (perms : ∀ index node,area.support index → tree.nodes.get index = some node → current.perms.get index = initial.perms.get index) :
    GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree current root protections where
  base := rebase data.base current coherent profile
  graph := data.graph
  witness := data.witness
  node := data.node
  present := data.present
  exposed := data.exposed
  support := by
    have included := data.base.included data.witness (GeneralBorrowExposedKnownRootWritePrimaryWitness.path_supported data data.path)
    simpa only [GeneralBorrowExposureCardinality.effective,perms data.witness data.node included data.present] using data.support
  path := data.path
end DuplicatePrefix.GeneralBorrowExposedKnownRootWriteTransport
