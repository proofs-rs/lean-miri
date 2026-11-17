import duplicate_prefix.S04ZeroRootObserverCallbacks
import duplicate_prefix.GeneralBorrowRootMembership

namespace DuplicatePrefix.S04ZeroRootObserverPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowNodeUpdate DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
attribute [local irreducible] UniValMap.insert

/-- Existing concrete ownership has a physical root by graph coverage;
wildcard ownership already requires a root. The added root is therefore secondary. -/
theorem roots_positive (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len : UInt64) (old : Positive tree protections source selected maximum offset len) :
    0 < tree.roots.size := by
  cases source with
  | none => exact old.wildcardRoot rfl
  | some observer =>
    obtain ⟨node,present⟩ := old.sourcePresent observer rfl
    obtain ⟨depth⟩ := formed.depth
    obtain ⟨forest⟩ := formed.forest default protections
    obtain ⟨root,value,found,parentless,member,path⟩ := GeneralBorrowRootMembership.terminal tree default protections
      forest depth formed.covered observer node present (by rw [S04ZeroRootObserverNormal.size];exact lookup_valid _ _ _ present)
    have listed : root ∈ tree.roots := Array.mem_toList_iff.mp member
    obtain ⟨position,valid,equal⟩ := Array.mem_iff_getElem.mp listed
    omega

/-- All initial row metadata and both arbitrary-cutoff callback tables survive
the actual isolated root insertion, including its new secondary callback. -/
theorem row (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.size ≤ 4294967296) (nonempty : 0 < tree.roots.size)
    (clean : location.perms.get slot.index = none)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (sourcePresent : ∀ observer,source = some observer → ∃ node,tree.nodeAt observer = some node)
    (old : Row tree location protections source selected maximum) :
    Nonempty (Row (slot.after tag) location protections source selected maximum) := by
  have frame : ∀ query node,tree.nodeAt query = some node → (slot.after tag).nodeAt query = some node :=
    S04ZeroRootObserverNormal.old_node tree slot tag
  refine ⟨{wildcard := old.wildcard,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := ?_}⟩
  · intro observer same
    obtain ⟨node,present⟩ := sourcePresent observer same
    rw [S04ZeroRootObserverNormal.old_path tree slot tag depth location protections observer node present]
    exact old.rootPath observer same
  · intro root same
    obtain ⟨node,present⟩ := old.rootPresent root same
    exact ⟨node,frame root node present⟩
  · rw [old.cutoff]
    cases selected with
    | none => rfl
    | some root =>
      obtain ⟨node,present⟩ := old.rootPresent root rfl
      simp only [Option.bind_some,frame root node present,present]
  · intro observer same
    obtain ⟨node,present⟩ := sourcePresent observer same
    obtain ⟨normal⟩ := old.normal observer same
    obtain ⟨next,_⟩ := S04ZeroRootObserverNormal.normal tree slot tag depth location protections fits clean observer node present normal
    exact ⟨next⟩
  · intro position valid different
    change position < (tree.roots.push slot.index).size at valid
    by_cases oldPosition : position < tree.roots.size
    · have rootEq : (slot.after tag).roots[position]'valid = tree.roots[position]'oldPosition :=
        Array.getElem_push_lt oldPosition
      rw [rootEq] at different ⊢
      obtain ⟨support,read,write⟩ := old.callbacks position oldPosition different
      exact ⟨support,S04ZeroRootObserverCallbacks.old tree slot tag depth location protections _ position maximum .Read support read,
        S04ZeroRootObserverCallbacks.old tree slot tag depth location protections _ position maximum .Write support write⟩
    · have last : position = tree.roots.size := by rw [Array.size_push] at valid;omega
      subst position
      have rootEq : (slot.after tag).roots[tree.roots.size]'valid = slot.index := Array.getElem_push_eq
      rw [rootEq]
      exact ⟨(fun query => query = slot.index),
        S04ZeroRootObserverCallbacks.new tree slot tag depth location protections nonempty clean maximum .Read,
        S04ZeroRootObserverCallbacks.new tree slot tag depth location protections nonempty clean maximum .Write⟩

/-- A zero wildcard retag preserves any old positive byte window (including a
return place in the same allocation), with the same source, root and cutoff.
All assumptions are initial graph, sparse-slot and ownership metadata. -/
theorem positive (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len : UInt64) (old : Positive tree protections source selected maximum offset len) :
    Nonempty (Positive (slot.after tag) protections source selected maximum offset len) := by
  obtain ⟨depth⟩ := formed.depth
  have nonempty := roots_positive tree formed protections source selected maximum offset len old
  refine ⟨{positive := old.positive,bounds := old.bounds,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}⟩
  · intro observer same
    obtain ⟨node,present⟩ := old.sourcePresent observer same
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag observer node present⟩
  · intro same
    change 0 < (tree.roots.push slot.index).size
    simp only [Array.size_push]
    omega
  · intro position valid positive beforeUpper afterLower
    obtain ⟨oldRow⟩ := old.rows position valid positive beforeUpper afterLower
    exact row tree slot tag depth _ protections formed.fits nonempty
      (clean slot.index slot.vacant position valid) source selected maximum old.sourcePresent oldRow

/-- The preserved observer belongs to the literal zero protected FnEntry
constructor output. Successful construction is derived from fresh allocator data. -/
theorem actual (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (retagOffset : UInt64)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len : UInt64) (old : Positive tree protections source selected maximum offset len) :
    let result := tree.newChild (Size.ofBytes retagOffset) .wildcard tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    result.outcome = .ok () ∧ Nonempty (Positive result.tree protections source selected maximum offset len) := by
  rw [slot.child tag fresh retagOffset]
  exact ⟨rfl,positive tree slot tag formed clean protections source selected maximum offset len old⟩

end DuplicatePrefix.S04ZeroRootObserverPositive
