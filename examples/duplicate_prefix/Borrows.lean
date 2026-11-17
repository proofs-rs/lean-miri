import Miri.TreeBorrows.RetagPolicy

/-! Tree Borrows component evidence for the mutable u8 slice borrow. The tree
shape and location states below are explicit premises of the actual
NormalTreeState access API: one allocation root and the FnEntry slice tag as
its child. The theorem covers both FnEntry permission branches (reserved and
implicit-write unique), the two disjoint byte locations, and the protected
return access. It does not prove that the MIR interpreter constructs this
tree or resolves its pointers to these locations. -/

namespace DuplicatePrefix.Borrows

open Miri.Memory Miri.TreeBorrows

private def childTag : BorTag := ⟨2, by decide⟩

private def sliceFacts : RetagPolicy.TypeFacts := {
  isUnpin := true, isUnsafeUnpin := true, isFreeze := true }

private def entryPermission (implicitWrites : Bool) : Permission :=
  if implicitWrites then .Unique else .ReservedFrz false

private def entryPolicy (implicitWrites : Bool) : Option RetagPolicy.NewPermission :=
  RetagPolicy.create sliceFacts .Mutable .FnEntry
    { implicitWrites, rustcNoWritable := false }

theorem mutable_fnentry_policy (implicitWrites : Bool) :
    entryPolicy implicitWrites = some {
      freezePermission := entryPermission implicitWrites
      nonfreezePermission := entryPermission implicitWrites
      outsidePermission := .ReservedFrz false
      protector := some .StrongProtector } := by
  cases implicitWrites <;> decide

private def accessed (permission : Permission) : Tree.LocationState :=
  ⟨permission, true, .None⟩

private def sliceLocation (implicitWrites : Bool) : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩
  defaultStates := #[accessed .Unique, accessed (entryPermission implicitWrites)]
  protectedNodes := [1]
  locationStates := #[none, none]
}

private def sourceRead (implicitWrites : Bool) : Tree.NormalAccessResult :=
  (sliceLocation implicitWrites).performAccess 1 .Read .VisitChildrenOfAccessed

private def sourceProtectorEnd (implicitWrites : Bool) : Tree.NormalAccessResult :=
  (sourceRead implicitWrites).tree.performAccess 1
    ((entryPermission implicitWrites).associatedAccess.getD .Read) .SkipChildrenOfAccessed

private def destinationWrite (implicitWrites : Bool) : Tree.NormalAccessResult :=
  (sliceLocation implicitWrites).performAccess 1 .Write .VisitChildrenOfAccessed

private def destinationProtectorEnd (implicitWrites : Bool) : Tree.NormalAccessResult :=
  (destinationWrite implicitWrites).tree.performAccess 1
    .Write .SkipChildrenOfAccessed

/-- With the actual NormalTreeState visitor and permission transitions, the
same protected mutable tag can read the source byte and then return cleanly;
on a disjoint byte with the same initial slice state it can write and return
cleanly. The FnEntry policy theorem above establishes that these are exactly
the source's ReservedFrz and implicit-write Unique branches. -/
theorem mutable_fnentry_read_write_and_return (implicitWrites : Bool) :
    (sourceRead implicitWrites).status = Tree.NormalAccessStatus.Completed ∧
    (sourceProtectorEnd implicitWrites).status = Tree.NormalAccessStatus.Completed ∧
    (destinationWrite implicitWrites).status = Tree.NormalAccessStatus.Completed ∧
    (destinationProtectorEnd implicitWrites).status = Tree.NormalAccessStatus.Completed := by
  cases implicitWrites <;> decide

#print axioms mutable_fnentry_policy
#print axioms mutable_fnentry_read_write_and_return

end DuplicatePrefix.Borrows
