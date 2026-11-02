import empty_function.RootReservedPost
namespace EmptyFunction.RootFramePost
open Miri Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
/-- Root/address conversion does not change the current protector ledger or
tracked-tag selection. The dynamic root cache and counter may grow. -/
def Frame (before after : GlobalState) : Prop :=
  after.protectedTags = before.protectedTags ∧ after.trackedPointerTags = before.trackedPointerTags ∧
    (∀ id tag, before.rootTag? id = some tag → after.rootTag? id = some tag)

theorem root (before after : GlobalState) (id : AllocId) (tag : BorTag)
    (actual : before.rootPointerTag id = .ok (after,tag)) : Frame before after := by
  have post := RootTagPost.root before id after tag actual
  exact ⟨post.2.2.1,post.2.2.2.1,post.2.1⟩

theorem trans (first middle last : GlobalState) (left : Frame first middle) (right : Frame middle last) :
    Frame first last := ⟨right.1.trans left.1,right.2.1.trans left.2.1,by intro id tag prior; exact right.2.2 id tag (left.2.2 id tag prior)⟩
end EmptyFunction.RootFramePost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RootFramePost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root frame post axiom {dependency} in {name}"
