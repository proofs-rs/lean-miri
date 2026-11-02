import duplicate_prefix.GeneralBorrowRootOnlyRangeCache

namespace DuplicatePrefix.GeneralBorrowRootOnlyPartitionExposure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowRootOnlyRangeCache DuplicatePrefix.GeneralBorrowUniqueRootExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A dependent source loop invariant indexed by its actual unprocessed suffix. -/
theorem progress {α β : Type} (items : List α)
    (scan : (item : α) → item ∈ items → β → Id (ForInStep β))
    (property : List α → β → Prop) (unique : items.Nodup)
    (step : ∀ item rest member state, (item :: rest).Nodup → property (item :: rest) state →
      ∃ next, scan item member state = .yield next ∧ property rest next)
    (initial : β) (good : property items initial) : property [] (forIn' items initial scan) := by
  induction items generalizing initial with
  | nil => exact good
  | cons item rest ih =>
    obtain ⟨next,actual,valid⟩ := step item rest (by simp) initial unique good
    simp only [List.forIn'_cons,actual,bind]
    exact ih (fun later member => scan later (by simp [member])) (List.nodup_cons.mp unique).2
      (fun later tail member current distinct valid => step later tail (by simp [member]) current distinct valid) next valid

/-- A first real root exposure updates the exact cache independently at EVERY
stored partition location. Permission maps are retained and no cache-success or
operation-success premise is supplied. -/
theorem expose (tree : BorrowTree) (tag : BorTag) (root : UniIndex) (node : TreeNode)
    (cache : ExposedCache) (protections : ProtectedTags)
    (tagged : tree.indexOfTag tag = some root) (present : tree.nodeAt root = some node)
    (parentless : node.parent = none) (unexposed : node.isExposed = false)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    (tree.exposeTag protections tag).outcome = .ok () ∧
    Every (LocationInvariant (bump cache root) root) (tree.exposeTag protections tag).tree.locations := by
  let marked := {tree with nodes := tree.nodes.insert root {node with isExposed := true}}
  have markedPresent : marked.nodes.get root = some {node with isExposed := true} :=
    GeneralBorrowFreshLocation.get_same tree.nodes root _
  unfold BorrowTree.exposeTag
  simp only [tagged,present,unexposed,Bool.false_eq_true,↓reduceIte,Id.run,pure]
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_release_exposure_scan
  let property := fun remaining : List Nat => fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
    state.1 = none ∧ state.2.locations.entries.size = tree.locations.entries.size ∧
    ∀ query (valid : query < state.2.locations.entries.size),
      StoredUnique state.2.locations.entries[query].data root ∧
      state.2.locations.entries[query].data.exposedCache = if query ∈ remaining then cache else bump cache root
  have step : ∀ position rest member state, (position :: rest).Nodup → property (position :: rest) state →
      ∃ next, scan position member state = .yield next ∧ property rest next := by
    intro position rest member state distinct good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,size,all⟩
    dsimp only at returnedEq size all
    subst returned
    have originalBound : position < tree.locations.entries.size := by
      have bound := List.mem_range'_1.mp member
      simpa [marked] using bound.2
    have valid : position < current.locations.entries.size := by rw [size];exact originalBound
    obtain ⟨old,stored,unique⟩ := (all position valid).1
    have oldCache : current.locations.entries[position].data.exposedCache = cache := by
      simpa only [List.mem_cons_self,ite_true] using (all position valid).2
    let location := current.locations.entries[position].data
    let nextLocation := {location with exposedCache := bump cache root}
    let nextTree := {current with locations := (current.locations.setAtPos position nextLocation).state}
    have update := root_cache cache marked.nodes root {node with isExposed := true} markedPresent parentless
    have actual : scan position member (none,current) = .yield (none,nextTree) := by
      simp only [scan,index_exact current.locations position valid,stored,Option.getD_some,unique,
        Permission.strongestAllowedLocalAccess,oldCache]
      erw [update]
      simp only [Except.mapError,setAtPos_success current.locations position valid]
      rfl
    refine ⟨(none,nextTree),actual,rfl,?_,?_⟩
    · exact (setAtPos_length current.locations position valid nextLocation).trans size
    · intro query bounded
      dsimp only [nextTree] at bounded ⊢
      simp only [setAtPos_exact current.locations position valid nextLocation] at bounded ⊢
      have oldBound : query < current.locations.entries.size := by simpa only [replaced_length] using bounded
      by_cases same : position = query
      · subst query
        have absent : position ∉ rest := (List.nodup_cons.mp distinct).1
        simp only [replaced,Array.getElem_set_self,nextLocation,ite_eq_right absent]
        exact ⟨⟨old,stored,unique⟩,True.intro⟩
      · have queryDifferent : query ≠ position := Ne.symm same
        simpa only [replaced,Array.getElem_set,ite_eq_right same,List.mem_cons,queryDifferent,false_or] using all query oldBound
  have start : property (List.range' 0 tree.locations.entries.size) (none,marked) := by
    refine ⟨rfl,rfl,?_⟩
    intro query valid
    have inside : query ∈ List.range' 0 tree.locations.entries.size := List.mem_range'_1.mpr ⟨Nat.zero_le _,by simpa [marked] using valid⟩
    exact ⟨(initial query valid).1,by simpa only [ite_eq_left inside] using (initial query valid).2⟩
  have unique : (List.range' 0 tree.locations.entries.size).Nodup := List.nodup_range'
  have final := progress _ scan property unique step (none,marked) start
  rw [final.1]
  refine ⟨rfl,?_⟩
  intro query valid
  exact ⟨(final.2.2 query valid).1,by simpa only [List.not_mem_nil,ite_false] using (final.2.2 query valid).2⟩

end DuplicatePrefix.GeneralBorrowRootOnlyPartitionExposure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyPartitionExposure." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only partition exposure dependency {dependency}"
