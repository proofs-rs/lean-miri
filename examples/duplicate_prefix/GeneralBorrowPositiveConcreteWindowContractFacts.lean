import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalInput
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowContractFacts
open Miri Miri.Memory Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- This ancestor-specialized domain constrains selected exposed permissions
on EVERY location: on-path exposed nodes are Unique, retained off-path exposed
nodes are Disabled. Only ordinary ownership is window-local. Other components
are exposed leaves with effective writable permissions, and their tags are at
most the selected ROOT tag. Unsupported selected profiles and newer outside
roots belong to the later general exposed-forest gate. -/
theorem selected_profile (s : GeneralBorrowPositiveConcreteWindowOriginalInput.Base) :
    GeneralRangeMapState.Every (fun location=>GeneralBorrowExposedInactiveConstructor.Profile
      s.entry.allocation.extra location s.data.input.parent s.data.resources.component.support)
      s.entry.allocation.extra.locations := by
  simpa only [s.data.treeEq] using s.data.resources.exposures

/-- Both explicit modes supply selected permissions on the actual borrowed
window. This does not recover allocation-wide permissions from window mode;
the existing selected_profile theorem above stays global-only. -/
theorem selected_profile_onWindow {profileMode : ProfileMode}
    (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) :
    GeneralRangeMapOrigins.OwnedOn (fun location => GeneralBorrowExposedInactiveConstructor.Profile
      s.entry.allocation.extra location s.data.input.parent s.data.resources.component.support)
      s.offset (s.offset+s.len) s.entry.allocation.extra.locations := by
  have localProfile := ProfileMode.toOwned profileMode _ _ _ _ s.data.resources.exposures
  simpa only [s.data.treeEq, s.data.offsetEq, s.data.lenEq] using localProfile

theorem outside_tags {profileMode : ProfileMode}
    (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) :
    ∀ index node,area.support index→s.entry.allocation.extra.nodeAt index=some node→
      node.tag.value≤s.data.resources.selectedNode.tag.value := by
  simpa only [s.data.treeEq] using s.data.resources.tags
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowContractFacts
