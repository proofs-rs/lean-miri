import duplicate_prefix.GeneralBorrowExposedKnownRootPrimaryWitness
import duplicate_prefix.GeneralBorrowExposedScopedNormalCache
namespace DuplicatePrefix.GeneralBorrowExposedKnownRootTransport
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Rebase other-component input records on the derived normal poststate.
Only global coherence and scoped readability change with location data. -/
def rebase {tree initial root protections} (data : Data tree initial root protections) (current : LocationTree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (readable : Readable tree current protections) : Data tree current root protections where
  support := data.support
  rooted := data.rooted
  present := data.present
  children := data.children
  covers := data.covers
  coherent := coherent
  short := data.short
  depth := data.depth
  included := data.included
  readable := readable

/-- Scoped normal access cannot change any other-component condition,
including initial cache-sensitive protected Unique/ReservedIM allowances. -/
theorem readable (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (cache : current.exposedCache = initial.exposedCache)
    (perms : ∀ index node,area.support index → tree.nodes.get index = some node → current.perms.get index = initial.perms.get index)
    (profile : Readable tree initial protections) : Readable tree current protections := by
  intro index node member present
  simpa only [GeneralBorrowWildcardVirtualLeaf.effective,zero,cache,perms index node member present] using profile index node member present

def primary {tree initial root protections} (data : GeneralBorrowExposedKnownRootPrimaryWitness.Data tree initial root protections)
    (current : LocationTree) (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (readable : Readable tree current protections)
    (perms : ∀ index node,area.support index → tree.nodes.get index = some node → current.perms.get index = initial.perms.get index) :
    GeneralBorrowExposedKnownRootPrimaryWitness.Data tree current root protections where
  base := rebase data.base current coherent readable
  graph := data.graph
  witness := data.witness
  node := data.node
  present := data.present
  exposed := data.exposed
  support := by
    have included := data.base.included data.witness (GeneralBorrowExposedKnownRootPrimaryWitness.path_supported data data.path)
    simpa only [GeneralBorrowExposureCardinality.effective,perms data.witness data.node included data.present] using data.support
  path := data.path
end DuplicatePrefix.GeneralBorrowExposedKnownRootTransport
