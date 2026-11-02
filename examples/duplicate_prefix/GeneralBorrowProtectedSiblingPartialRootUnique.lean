import duplicate_prefix.GeneralBorrowProtectedSiblingPartialRangeInvariant
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationStep
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialRootUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem read (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (initial : Every (At input.parent (some .Unique)) input.tree.locations) :
    Every (At input.parent (some .Unique)) (GeneralBorrowProtectedReadableStage.read input protections).tree.locations := by
  have result := GeneralBorrowProtectedSiblingPartialRangeInvariant.ranged input.tree protections input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.depth input.children input.parentNode input.parentPresent
    roots input.covered input.parentTagPresent input.well (At input.parent (some .Unique)) initial (by
      intro location profile unique
      obtain ⟨⟨forest⟩,data⟩ := profile
      have stored : ∃ state,location.perms.get input.parent = some state ∧ state.permission = .Unique := by
        cases found : location.perms.get input.parent with
        | none => simp only [At,found,Option.map_none] at unique;cases unique
        | some state => exact ⟨state,rfl,by simpa only [At,found,Option.map_some,Option.some.injEq] using unique⟩
      obtain ⟨state,present,permission⟩ := GeneralBorrowProtectedSiblingRootRead.normal input.tree location protections input.parent input.parent
        input.parentNode input.parentNode .VisitChildrenOfAccessed input.parentPresent input.parentPresent roots input.covered input.depth forest stored
      simp only [At,present,Option.map_some,permission])
    input.offset (input.offset+input.len) (fun position valid _ _ _ => readable position valid) (Nat.le_refl _) (Nat.le_refl _) input.bounds
  exact result.2.1

theorem step {input global frame allocation selected future}
    (ready : GeneralBorrowProtectedSiblingGenerationStep.Ready input global frame allocation selected future)
    (roots : input.tree.roots = #[input.parent])
    (initial : Every (At input.parent (some .Unique)) input.tree.locations) :
    Every (At ready.next.parent (some .Unique)) ready.next.tree.locations := by
  have afterRead := read input ready.output.global.protectedTags roots ready.registeredProfile initial
  have nextRead : Every (At input.parent (some .Unique)) ready.prepared.next.tree.locations := by rw [ready.prepared.tree];exact afterRead
  have parentEq := ready.prepared.parent
  have readFrame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read ready.output.global.protectedTags .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input ready.output.global.protectedTags).tree =
    {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input ready.output.global.protectedTags).tree.locations} at readFrame
  have present : ready.prepared.next.tree.nodeAt input.parent = some input.parentNode := by
    rw [ready.prepared.tree,readFrame]
    exact input.parentPresent
  have different : input.parent ≠ GeneralBorrowFreshMetadataChildMutable.index ready.prepared.next := by
    intro same
    have bound := GeneralBorrowNodeUpdate.lookup_valid ready.prepared.next.tree.nodes input.parent input.parentNode present
    rw [same,GeneralBorrowFreshMetadataChildMutable.at_end] at bound
    omega
  have retained := (GeneralBorrowConstructorPriorPermission.protected_append ready.prepared.next input.parent (some .Unique) different nextRead).2
  rw [ready.parent]
  exact GeneralBorrowConstructorPriorPermission.shape _ _ ready.shape input.parent (some .Unique) retained
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialRootUnique
