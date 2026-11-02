import duplicate_prefix.GeneralBorrowFreshSharedTargetActivity
import duplicate_prefix.GeneralBorrowFreshSharedNext
namespace DuplicatePrefix.GeneralBorrowFreshSharedTwoTargetWithin
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Mixed ownership derived from the initial mutable anchor supplies both
real shared stages; its strong Write activity survives both Reads, both
Frozen installations and both SIFA.Read stages. -/
theorem two (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (second : Data (child first protections false).tree nextTag (index first) offset len)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations)
    (lower upper : UInt64) (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (child second protections true).tree target .Write lower upper := by
  have initial : OwnedOn (Combined tree protections target (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive start stop
    exact write_combined tree _ protections target (owned position valid positive start stop)
  have firstActive := GeneralBorrowFreshSharedTargetActivity.preserves_target tree exprTag target offset len first protections false
    (fun _ => true) initial target lower upper requestLower requestUpper active
  have completed := GeneralBorrowFreshSharedSequence.run tree exprTag target offset len first protections false (fun _ => true) initial
  have firstOwned := completed.2.2.1
  have regFalse : registered protections exprTag false = protections := by simp only [registered,Bool.false_eq_true,↓reduceIte]
  rw [regFalse] at firstOwned
  exact GeneralBorrowFreshSharedTargetActivity.preserves_target (child first protections false).tree nextTag (index first) offset len
    second protections true (extend (fun _ => true) (index first).toNat) firstOwned target lower upper requestLower requestUpper firstActive

/-- The exact second Data is constructed from initial allocator/freshness and
cleanliness data, so no post-state strong profile or metadata premise remains. -/
theorem two_append (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations)
    (lower upper : UInt64) (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : ActiveWithin tree target .Write lower upper) :
    let choice := GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
      freshTag freshProtector different cleanFuture owned
    ActiveWithin (child choice.val protections true).tree target .Write lower upper := by
  generalize nextEq : GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
    freshTag freshProtector different cleanFuture owned = choice
  rcases choice with ⟨second,nextIndex⟩
  dsimp only at ⊢
  exact two tree protections target exprTag nextTag offset len first second owned lower upper requestLower requestUpper active
end DuplicatePrefix.GeneralBorrowFreshSharedTwoTargetWithin
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedTwoTargetWithin." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared two target within dependency {dependency}"
