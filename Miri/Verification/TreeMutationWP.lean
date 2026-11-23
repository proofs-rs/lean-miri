import Miri.Verification.TreeBorrowsWP

/-! Exact, ordered continuation rules for exposure, retag insertion and
provenance collection within an allocation's Tree Borrows state. -/
namespace Miri.Verification.TreeMutationWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree.MutationVerification

@[spec high] theorem spec_expose (tags : ProtectedTags) (tag : BorTag)
    (post : Unit → BorrowTree → Prop)
    (failure : BorrowTree.TreeMutationError → BorrowTree → Prop) :
    Triple (TreeBorrowsWP.expose tags tag)
      (fun tree => exposePre tree tags tag (post ()) failure) post failure := by
  apply Triple.iff.mpr
  intro tree checked
  have result := (exposePre_iff tree tags tag (post ()) failure).mp checked
  unfold wp WP.wpTrans EStateM.wpInst TreeBorrowsWP.expose TreeBorrowsWP.mutation
  cases outcome : (tree.exposeTag tags tag).outcome with
  | error => simpa only [outcome] using result
  | ok value =>
    cases value
    simpa only [outcome] using result

@[spec high] theorem spec_collect (live : Array BorTag) (post : Unit → BorrowTree → Prop)
    (failure : BorrowTree.TreeGcError → BorrowTree → Prop) :
    Triple (TreeBorrowsWP.collect live)
      (fun tree => collectPre tree live (post ()) failure) post failure := by
  apply Triple.iff.mpr
  intro tree checked
  have result := (collectPre_iff tree live (post ()) failure).mp checked
  unfold wp WP.wpTrans EStateM.wpInst TreeBorrowsWP.collect TreeBorrowsWP.mutation
  cases outcome : (tree.removeUnreachableTags live).outcome with
  | error => simpa only [outcome] using result
  | ok value =>
    cases value
    simpa only [outcome] using result

@[spec high] theorem spec_insertChild (offset : Size) (parent : ProvenanceExtra) (tag : BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (post : Unit → BorrowTree → Prop)
    (failure : BorrowTree.ChildInsertError → BorrowTree → Prop) :
    Triple (TreeBorrowsWP.insertChild offset parent tag inside outside held)
      (fun tree => insertChildPre tree offset parent tag inside outside held (post ()) failure)
      post failure := by
  apply Triple.iff.mpr
  intro tree checked
  have result := (insertChildPre_iff tree offset parent tag inside outside held (post ()) failure).mp checked
  unfold wp WP.wpTrans EStateM.wpInst TreeBorrowsWP.insertChild TreeBorrowsWP.mutation
  cases outcome : (tree.newChild offset parent tag inside outside held).outcome with
  | error => simpa only [childResultPre, outcome] using result
  | ok value =>
    cases value
    simpa only [childResultPre, outcome] using result

end Miri.Verification.TreeMutationWP
