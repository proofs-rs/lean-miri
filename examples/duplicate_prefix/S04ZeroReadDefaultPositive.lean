import duplicate_prefix.S04ZeroReadDefaultMetadata
import duplicate_prefix.S04ZeroReadDefaultNormal
import duplicate_prefix.GeneralBorrowObserverNormalShape

namespace DuplicatePrefix.S04ZeroReadDefaultPositive
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowProjection
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- An old observer's normal Read/Write capability and root path survive the
actual unprotected zero constructor's attachment and its real ancestor-SIFA loop.
No source/constructor-parent relation or allocation separation is assumed. -/
theorem normal_path (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadDefaultEntry.Input tree parentTag tag) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (afterValid : position < input.after.locations.entries.size)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree (tree.locations.entries[position]'valid).data protections).topology)
    (observer : UniIndex) (node : TreeNode) (present : tree.nodeAt observer = some node)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree (tree.locations.entries[position]'valid).data protections observer) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal input.after
      (input.after.locations.entries[position]'afterValid).data protections observer) ∧
    (source_normal_projection input.after (input.after.locations.entries[position]'afterValid).data protections).topology.ancestorPath observer.toNat =
      (source_normal_projection tree (tree.locations.entries[position]'valid).data protections).topology.ancestorPath observer.toNat := by
  obtain ⟨staged,support,path⟩ := S04ZeroReadDefaultNormal.at_row tree parentTag tag input protections fits
    position valid forest observer node present old
  have shape := GeneralBorrowSifaView.preserves input.stage input.parent .Read
  have nodes := congrArg (fun value => value.2.1) shape
  have ranges := congrArg (fun value => value.2.2.1) shape
  change input.after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have point := congrArg (fun rows => rows[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem afterValid,Option.map_some] at point
  have locations := congrArg Prod.snd (Option.some.inj point)
  have projection := GeneralBorrowFreshOwnership.projection_shape input.stage input.after
    (tree.locations.entries[position]'valid).data (input.after.locations.entries[position]'afterValid).data protections nodes locations
  obtain ⟨next,kept⟩ := GeneralBorrowObserverNormalShape.normal input.stage input.after _ _ protections observer projection staged
  refine ⟨⟨next⟩,?_⟩
  have topology := congrArg (fun value => value.1) projection
  change (source_normal_projection input.after (input.after.locations.entries[position]'afterValid).data protections).topology =
    (source_normal_projection input.stage (tree.locations.entries[position]'valid).data protections).topology at topology
  rw [topology]
  exact path

/-- The REAL zero-length unprotected Default child preserves the original
positive observer window, including both normal kinds and every physical root
callback. In particular the empty reference and destination may occupy the
same allocation, with unrelated parents/components and sparse slot reuse.
No successful operation or post-operation capability is assumed. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag : BorTag) (input : S04ZeroReadDefaultEntry.Input tree parentTag tag)
    (fits : tree.nodes.data.size ≤ 4294967296) (offset : UInt64)
    (source selected : Option UniIndex) (maximum : Option BorTag) (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen)
    (notHeld : global.protectedTags.contains tag = false) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    result.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree global.protectedTags source selected maximum ownerOffset ownerLen) := by
  rw [input.child offset]
  refine ⟨rfl,⟨{positive := positive.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}⟩⟩
  · rw [S04ZeroReadDefaultMetadata.capacity tree parentTag tag input]
    exact positive.bounds
  · intro observer sourceEq
    obtain ⟨node,present⟩ := positive.sourcePresent observer sourceEq
    obtain ⟨next,found,tagEq⟩ := S04ZeroReadDefaultMetadata.old_node tree parentTag tag input observer node present
    exact ⟨next,found⟩
  · intro sourceEq
    rw [S04ZeroReadDefaultMetadata.roots tree parentTag tag input]
    exact positive.wildcardRoot sourceEq
  · intro position valid nonzero start stop
    have oldValid : position < tree.locations.entries.size := by
      rw [←S04ZeroReadDefaultMetadata.length tree parentTag tag input]
      exact valid
    have range := S04ZeroReadDefaultMetadata.row_range tree parentTag tag input position oldValid valid
    rw [range] at start stop
    obtain ⟨old⟩ := positive.rows position oldValid nonzero start stop
    obtain ⟨forest⟩ := runtime.formed.forest (tree.locations.entries[position]'oldValid).data global.protectedTags
    have normalPath (observer : UniIndex) (sourceEq : source = some observer) :
        Nonempty (DuplicatePrefixBorrowAuthorization.Normal input.after
          (input.after.locations.entries[position]'valid).data global.protectedTags observer) ∧
        (source_normal_projection input.after (input.after.locations.entries[position]'valid).data global.protectedTags).topology.ancestorPath observer.toNat =
          (source_normal_projection tree (tree.locations.entries[position]'oldValid).data global.protectedTags).topology.ancestorPath observer.toNat := by
      obtain ⟨normal⟩ := old.normal observer sourceEq
      obtain ⟨node,present⟩ := positive.sourcePresent observer sourceEq
      exact normal_path tree parentTag tag input global.protectedTags fits position oldValid valid forest observer node present normal
    refine ⟨{wildcard := old.wildcard,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := ?_}⟩
    · intro observer sourceEq
      rw [(normalPath observer sourceEq).2]
      exact old.rootPath observer sourceEq
    · intro root selectedEq
      obtain ⟨node,present⟩ := old.rootPresent root selectedEq
      obtain ⟨next,found,tagEq⟩ := S04ZeroReadDefaultMetadata.old_node tree parentTag tag input root node present
      exact ⟨next,found⟩
    · cases selected with
      | none => exact old.cutoff
      | some root =>
        obtain ⟨node,present⟩ := old.rootPresent root rfl
        obtain ⟨next,found,tagEq⟩ := S04ZeroReadDefaultMetadata.old_node tree parentTag tag input root node present
        simpa only [Option.bind_some,present,found,Option.map_some,tagEq] using old.cutoff
    · intro observer sourceEq
      exact (normalPath observer sourceEq).1
    · intro rootPosition rootValid different
      have roots := S04ZeroReadDefaultMetadata.roots tree parentTag tag input
      have oldRootValid : rootPosition < tree.roots.size := by rw [←roots];exact rootValid
      have rootEq : input.after.roots[rootPosition]'rootValid = tree.roots[rootPosition]'oldRootValid := by
        have indexed := congrArg (fun rows => rows[rootPosition]?) roots
        simpa only [Array.getElem?_eq_getElem rootValid,Array.getElem?_eq_getElem oldRootValid,Option.some.injEq] using indexed
      rw [rootEq] at different
      obtain ⟨support,read,write⟩ := old.callbacks rootPosition oldRootValid different
      have profile := runtime.formed.profile position oldValid
      have readProof := S04ZeroReadDefaultCallbacks.actual tree parentTag tag input offset global.protectedTags
        position oldValid profile notHeld (tree.roots[rootPosition]'oldRootValid) rootPosition maximum .Read support read
      have writeProof := S04ZeroReadDefaultCallbacks.actual tree parentTag tag input offset global.protectedTags
        position oldValid profile notHeld (tree.roots[rootPosition]'oldRootValid) rootPosition maximum .Write support write
      rw [input.child offset] at readProof writeProof
      obtain ⟨doneRead,readValid,readAfter⟩ := readProof
      obtain ⟨doneWrite,writeValid,writeAfter⟩ := writeProof
      refine ⟨S04ZeroReadDefaultAttach.extended support input.parent input.index,?_,?_⟩
      · rw [rootEq]
        exact readAfter
      · rw [rootEq]
        exact writeAfter

end DuplicatePrefix.S04ZeroReadDefaultPositive
