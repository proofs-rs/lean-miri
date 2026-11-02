import duplicate_prefix.GeneralBorrowExposedInactiveConstructor
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
namespace DuplicatePrefix.GeneralBorrowExposedInactiveConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralRangeMapState GeneralBorrowFreshGraph GeneralBorrowExposedConstructorAncestry
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem protected_mutable (input : GeneralBorrowFreshMetadataChildMutable.Input) (support : Nat → Prop)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : Every (fun location => Profile input.tree location input.parent support) input.tree.locations) :
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildMutable.result input) location (GeneralBorrowFreshMetadataChildMutable.index input)
      (extended support (GeneralBorrowFreshMetadataChildMutable.index input))) (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildMutable.result input
  let index := GeneralBorrowFreshMetadataChildMutable.index input
  let metadata := GeneralBorrowFreshMetadataChildMutable.append input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value,child.nodeAt index=some value → value.isExposed=false := by
    intro value found
    have equal : value=node := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have size : (topology input.tree).nodes.size=index.toNat := by
    rw [GeneralBorrowFreshMetadataChildMutable.at_end]
    unfold topology
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat (metadata.extension default default default) forest
  change GeneralBorrowFreshSharedPaths.Attach (topology input.tree) (topology child) input.parent.toNat (topology input.tree).nodes.size at paths
  rw [size] at paths
  let predicate := fun location => Profile child location index (extended support index)
  have base : Every predicate input.tree.locations := by
    intro position valid
    exact append_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildMutable.mapping input) (GeneralBorrowFreshMetadataChildMutable.locations input) support _ (GeneralBorrowFreshMetadataChildMutable.at_end input)
      input.parentPresent (GeneralBorrowFreshMetadataChildMutable.shape input) (GeneralBorrowFreshMetadataChildMutable.exposure input) paths hidden (initial position valid)
  have modified := GeneralBorrowExposureChildAttach.modify_every predicate input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside) input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshChild.inside _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildMutable.shape input)
  exact every_shape child (GeneralBorrowFreshMetadataChildMutable.stage input).locations child.locations index _ rows modified

end DuplicatePrefix.GeneralBorrowExposedInactiveConstructor
