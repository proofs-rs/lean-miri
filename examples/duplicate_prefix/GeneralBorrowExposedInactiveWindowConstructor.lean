import duplicate_prefix.GeneralBorrowExposedInactiveProtectedMutable
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowExposedInactiveWindowConstructor
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralRangeMapState GeneralBorrowFreshGraph GeneralBorrowExposedConstructorAncestry
open GeneralRangeMapOrigins GeneralBorrowExposedInactiveConstructor
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- A data callback preserves a window-local invariant through the actual
range modifier, including its real splitting/merging preparation. No condition
is imposed on stored rows disjoint from the ownership window. -/
theorem modify_owned {α : Type} [DecidableEq α] (predicate : α → Prop) (lower upper : UInt64)
    (map : DedupRangeMap α) (offset len : Size) (modify : ByteRange → α → α)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (initial : OwnedOn predicate lower upper map)
    (step : ∀ range value, predicate value → predicate (modify range value)) :
    OwnedOn predicate lower upper (map.modifyRange offset len modify).state := by
  have prepared := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := GeneralRangeMapOrigins.refines_owned_on map (map.iterMut offset len).state
    predicate lower upper prepared.1.wellFormed prepared.2.1 initial
  have update : ∀ (current : DedupRangeMap α) (position : Nat),
      OwnedOn predicate lower upper current →
      OwnedOn predicate lower upper (GeneralBorrowFreshModify.atPosition current position modify) := by
    intro current position good query valid positive beforeUpper afterLower
    have bounded : query < current.entries.size := by
      rw [GeneralBorrowFreshModify.atPosition_size] at valid
      exact valid
    have row := GeneralBorrowFreshModify.atPosition_get current position query modify bounded
    by_cases same : position = query
    · subst position
      simp only [↓reduceIte] at row
      have oldBefore : current.entries[query].range.start.toNat < upper.toNat := by
        rw [row] at beforeUpper
        exact beforeUpper
      have oldAfter : lower.toNat < current.entries[query].range.stop.toNat := by
        rw [row] at afterLower
        exact afterLower
      rw [row]
      exact step _ _ (good query bounded positive oldBefore oldAfter)
    · simp only [same, ↓reduceIte] at row
      rw [row] at beforeUpper afterLower ⊢
      exact good query bounded positive beforeUpper afterLower
  have fold : ∀ positions : List Nat, ∀ current : DedupRangeMap α,
      OwnedOn predicate lower upper current →
      OwnedOn predicate lower upper (positions.foldl
        (fun current position => GeneralBorrowFreshModify.atPosition current position modify) current) := by
    intro positions
    induction positions with
    | nil => intro current good; exact good
    | cons position rest ih =>
      intro current good
      exact ih _ (update current position good)
  rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds]
  exact fold _ _ preparedOwned

/-- The allocation-wide SIFA shape transport preserves only the requested
window's exposure profile. Permissions on other rows remain unconstrained. -/
theorem owned_shape (tree : BorrowTree) (before after : DedupRangeMap LocationTree)
    (anchor : UniIndex) (support : Nat → Prop) (lower upper : UInt64)
    (same : after.entries.map (fun segment => (segment.range,locationShape segment.data))=
      before.entries.map (fun segment => (segment.range,locationShape segment.data)))
    (initial : OwnedOn (fun location => Profile tree location anchor support) lower upper before) :
    OwnedOn (fun location => Profile tree location anchor support) lower upper after := by
  have sizes : after.entries.size=before.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size same
  intro position valid positive beforeUpper afterLower
  have oldValid : position<before.entries.size := by rw [←sizes];exact valid
  have locationEq := congrArg (fun values => values[position]?) same
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] at locationEq
  have oldBefore : before.entries[position].range.start.toNat < upper.toNat := by
    rw [←locationEq.1]
    exact beforeUpper
  have oldAfter : lower.toNat < before.entries[position].range.stop.toNat := by
    rw [←locationEq.1]
    exact afterLower
  exact location_transport tree _ _ anchor support locationEq.2
    (initial position oldValid positive oldBefore oldAfter)

/-- Actual constructor preserves the selected exposure profile on an arbitrary
borrowed byte window, without any profile premise outside that window. -/
theorem shared (input : GeneralBorrowFreshMetadataChildShared.Input) (support : Nat → Prop) (lower upper : UInt64)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OwnedOn (fun location => Profile input.tree location input.parent support) lower upper input.tree.locations) :
    OwnedOn (fun location => Profile (GeneralBorrowFreshMetadataChildShared.result input) location (GeneralBorrowFreshMetadataChildShared.index input)
      (extended support (GeneralBorrowFreshMetadataChildShared.index input))) lower upper (GeneralBorrowFreshMetadataChildShared.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildShared.result input
  let index := GeneralBorrowFreshMetadataChildShared.index input
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value,child.nodeAt index=some value → value.isExposed=false := by
    intro value found
    have equal : value=node := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have size : (topology input.tree).nodes.size=index.toNat := by
    rw [GeneralBorrowFreshMetadataChildShared.at_end]
    unfold topology
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat (metadata.extension default default default) forest
  change GeneralBorrowFreshSharedPaths.Attach (topology input.tree) (topology child) input.parent.toNat (topology input.tree).nodes.size at paths
  rw [size] at paths
  let predicate := fun location => Profile child location index (extended support index)
  have base : OwnedOn predicate lower upper input.tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact append_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildShared.mapping input) (GeneralBorrowFreshMetadataChildShared.locations input) support _ (GeneralBorrowFreshMetadataChildShared.at_end input)
      input.parentPresent (GeneralBorrowFreshMetadataChildShared.shape input) (GeneralBorrowFreshMetadataChildShared.exposure input) paths hidden (initial position valid positive beforeUpper afterLower)
  have modified := modify_owned predicate lower upper input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshAnchor.sharedState) input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshAnchor.sharedState _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildShared.shape input)
  exact owned_shape child (GeneralBorrowFreshMetadataChildShared.stage input).locations child.locations index _ lower upper rows modified

/-- Actual constructor preserves the selected exposure profile on an arbitrary
borrowed byte window, without any profile premise outside that window. -/
theorem default_child (input : GeneralBorrowFreshMetadataChildDefault.Input) (support : Nat → Prop) (lower upper : UInt64)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OwnedOn (fun location => Profile input.tree location input.parent support) lower upper input.tree.locations) :
    OwnedOn (fun location => Profile (GeneralBorrowFreshMetadataChildDefault.result input) location (GeneralBorrowFreshMetadataChildDefault.index input)
      (extended support (GeneralBorrowFreshMetadataChildDefault.index input))) lower upper (GeneralBorrowFreshMetadataChildDefault.result input).locations := by
  let child := GeneralBorrowFreshMetadataChildDefault.result input
  let index := GeneralBorrowFreshMetadataChildDefault.index input
  let metadata := GeneralBorrowFreshMetadataChildDefault.append input
  obtain ⟨node,present,_,_,_,_,notExposed⟩ := metadata.newNode
  have hidden : ∀ value,child.nodeAt index=some value → value.isExposed=false := by
    intro value found
    have equal : value=node := Option.some.inj (found.symm.trans present)
    exact equal ▸ notExposed
  have size : (topology input.tree).nodes.size=index.toNat := by
    rw [GeneralBorrowFreshMetadataChildDefault.at_end]
    unfold topology
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat (metadata.extension default default default) forest
  change GeneralBorrowFreshSharedPaths.Attach (topology input.tree) (topology child) input.parent.toNat (topology input.tree).nodes.size at paths
  rw [size] at paths
  let predicate := fun location => Profile child location index (extended support index)
  have base : OwnedOn predicate lower upper input.tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact append_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildDefault.mapping input) (GeneralBorrowFreshMetadataChildDefault.locations input) support _ (GeneralBorrowFreshMetadataChildDefault.at_end input)
      input.parentPresent (GeneralBorrowFreshMetadataChildDefault.shape input) (GeneralBorrowFreshMetadataChildDefault.exposure input) paths hidden (initial position valid positive beforeUpper afterLower)
  have modified := modify_owned predicate lower upper input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside) input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshDefaultChild.inside _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildDefault.shape input)
  exact owned_shape child (GeneralBorrowFreshMetadataChildDefault.stage input).locations child.locations index _ lower upper rows modified

/-- Actual constructor preserves the selected exposure profile on an arbitrary
borrowed byte window, without any profile premise outside that window. -/
theorem protected_mutable (input : GeneralBorrowFreshMetadataChildMutable.Input) (support : Nat → Prop) (lower upper : UInt64)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OwnedOn (fun location => Profile input.tree location input.parent support) lower upper input.tree.locations) :
    OwnedOn (fun location => Profile (GeneralBorrowFreshMetadataChildMutable.result input) location (GeneralBorrowFreshMetadataChildMutable.index input)
      (extended support (GeneralBorrowFreshMetadataChildMutable.index input))) lower upper (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
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
  have base : OwnedOn predicate lower upper input.tree.locations := by
    intro position valid positive beforeUpper afterLower
    exact append_location input.tree child index input.parent input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent)
      (GeneralBorrowFreshMetadataChildMutable.mapping input) (GeneralBorrowFreshMetadataChildMutable.locations input) support _ (GeneralBorrowFreshMetadataChildMutable.at_end input)
      input.parentPresent (GeneralBorrowFreshMetadataChildMutable.shape input) (GeneralBorrowFreshMetadataChildMutable.exposure input) paths hidden (initial position valid positive beforeUpper afterLower)
  have modified := modify_owned predicate lower upper input.tree.locations
    (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside) input.well input.bounds base
    (fun _ location good => materialize child location index index GeneralBorrowFreshChild.inside _ hidden good)
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowFreshMetadataChildMutable.shape input)
  exact owned_shape child (GeneralBorrowFreshMetadataChildMutable.stage input).locations child.locations index _ lower upper rows modified

end DuplicatePrefix.GeneralBorrowExposedInactiveWindowConstructor
