import duplicate_prefix.GeneralBorrowGcChildFold

namespace DuplicatePrefix.GeneralBorrowGcNodeFields
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree

/-- Source GC may change only parent/children. Parent rewrites never create a
new parentless root; all other stored node metadata is retained exactly. -/
structure Preserved (before after : TreeNode) : Prop where
  tag : after.tag = before.tag
  permission : after.defaultInitialPermission = before.defaultInitialPermission
  sifa : after.defaultInitialSifa = before.defaultInitialSifa
  exposed : after.isExposed = before.isExposed
  debugName : after.debugName = before.debugName
  root : after.parent = none → before.parent = none

theorem refl (node : TreeNode) : Preserved node node := ⟨rfl,rfl,rfl,rfl,rfl,id⟩

theorem trans (before middle after : TreeNode) (first : Preserved before middle) (second : Preserved middle after) : Preserved before after :=
  ⟨second.tag.trans first.tag,second.permission.trans first.permission,second.sifa.trans first.sifa,
    second.exposed.trans first.exposed,second.debugName.trans first.debugName,fun edge => first.root (second.root edge)⟩

theorem reparent (node : TreeNode) (parent : UniIndex) : Preserved node {node with parent := some parent} :=
  ⟨rfl,rfl,rfl,rfl,rfl,by intro impossible;cases impossible⟩

theorem children (node : TreeNode) (kept : Array UniIndex) : Preserved node {node with children := kept} :=
  ⟨rfl,rfl,rfl,rfl,rfl,id⟩

end DuplicatePrefix.GeneralBorrowGcNodeFields
