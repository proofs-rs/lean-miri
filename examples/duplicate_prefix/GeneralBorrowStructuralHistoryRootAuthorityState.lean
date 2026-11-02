import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityAt
import duplicate_prefix.GeneralBorrowDisjointProtectors
import duplicate_prefix.GeneralBorrowRelease
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryRootAuthorityState
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowStructuralHistoryRootAuthorityAt GeneralBorrowProjection GeneralRangeMapState GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- This is latent authority, NOT Write ownership under active foreign
protectors. The actual table is intentionally absent from the permission policy. -/
structure Formed (tree : BorrowTree) (root : UniIndex) : Prop extends State tree where
  member : root∈tree.roots.toList
  policy : Profile tree root

theorem allocation (tag : BorTag) (size : Size) : Formed (BorrowTree.new tag size) ⟨0⟩ := by
  refine ⟨GeneralBorrowStructuralHistorySeed.initial tag size,?_,?_⟩
  · change (⟨0⟩:UniIndex)∈[(⟨0⟩:UniIndex)]
    simp
  · by_cases zero : size.bytes=0
    · intro position valid
      simp only [BorrowTree.new,Id.run,bind,pure,DedupRangeMap.new,zero,Size.ofBytes,beq_self_eq_true,ite_true,Array.size_empty] at valid
      omega
    · change Profile (GeneralBorrowFullSharedSeed.tree size.bytes zero tag) ⟨0⟩
      rw[GeneralBorrowFullSharedSeed.tree_eq]
      intro position valid
      have atZero : position=0 := by change position<1 at valid;omega
      subst position
      constructor
      · intro query node present
        have bound:=GeneralBorrowNodeUpdate.lookup_valid (⟨#[some (GeneralBorrowFullSharedSeed.node tag)]⟩:UniValMap TreeNode) query node present
        have same : query=(⟨0⟩:UniIndex) := GeneralBorrowNodeUpdate.index_injective _ _ (by change query.toNat=0;change query.toNat<1 at bound;omega)
        subst query
        change some (GeneralBorrowFullSharedSeed.node tag)=some node at present
        cases present
        simp [Allowed,GeneralBorrowGcPartitionOwnership.Allowed,GeneralBorrowPermissions.LocalOwned,
          GeneralBorrowFullSharedSeed.location,GeneralBorrowWildcardLeaf.unique,RangeMapNonempty.homogeneous,UniIndex.toNat,UniValMap.get,LocationState.possible,Permission.isUnique]
      · intro query vacant
        have different : query.toNat≠0 := by
          intro equal
          have same : query=(⟨0⟩:UniIndex):=GeneralBorrowNodeUpdate.index_injective _ _ equal
          subst query
          change some (GeneralBorrowFullSharedSeed.node tag)=none at vacant
          cases vacant
        change GeneralBorrowFullSharedSeed.location.perms.get query=none
        simp [GeneralBorrowFullSharedSeed.location,UniValMap.get,different]

theorem gc (tree : BorrowTree) (root : UniIndex) (initial : Formed tree root) (live : Array BorTag) :
    (tree.removeUnreachableTags live).outcome=.ok () ∧ Formed (tree.removeUnreachableTags live).tree root := by
  have structural:=GeneralBorrowStructuralHistoryState.gc tree initial.toState live
  have roots:=(GeneralBorrowGcResourceFrame.preserves (n:=0) (fun index=>Fin.elim0 index) tree live (by intro index;exact Fin.elim0 index)).roots
  exact ⟨structural.1,⟨structural.2.1,by rw[roots];exact initial.member,GeneralBorrowStructuralHistoryRootAuthorityAt.gc tree root live initial.policy⟩⟩

/-- A real parentless root and latent effective-permission policy form exact
range-local Write ownership under an empty protector view. -/
theorem empty_owned (tree : BorrowTree) (root : UniIndex) (initial : Formed tree root) (lower upper : UInt64) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) lower upper tree.locations := by
  obtain ⟨node,present,parentless⟩:=initial.rootNodes root initial.member
  have globalPolicy:=GeneralBorrowStructuralHistoryRootAuthorityAt.to_policy tree root initial.policy
  let policy : GeneralBorrowGcLocalEffectivePolicy.Policy (Allowed root) lower upper tree :=
    ⟨fun query node present position valid _ _ _=>globalPolicy.live query node present position valid,globalPolicy.vacant⟩
  exact GeneralBorrowGcForestRootOwnership.ownership tree root node present parentless
    (fun location=>Classical.choice (initial.forest location {})) lower upper policy initial.fits

/-- The global table may still protect other allocations. Only this allocation's
real node tags need be unheld when latent authority becomes current ownership. -/
theorem owned (tree : BorrowTree) (root : UniIndex) (initial : Formed tree root) (protections : ProtectedTags)
    (unheld : GeneralBorrowDisjointProtectors.Unheld tree protections) (lower upper : UInt64) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree protections root .Write) lower upper tree.locations := by
  intro position valid positive before after
  have owner:=empty_owned tree root initial lower upper position valid positive before after
  change Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree _ protections).topology) ∧
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree _ protections) root.toNat .Write
  rw[GeneralBorrowDisjointProtectors.projection tree _ protections unheld]
  exact owner

/-- Raw chronological coverage of every currently held local tag by the real
ending frame is enough. The exact source endCall fold derives absence; no final
unheld, ownership or operation-success proposition is an input. This theorem
covers global bookkeeping; implicit tree release accesses are separate steps. -/
theorem after_end_call (tree : BorrowTree) (root : UniIndex) (initial : Formed tree root)
    (global : GlobalState) (frame : FrameState)
    (covered : ∀row∈tree.nodes.entries, global.protectedTags.contains row.2.tag=false ∨
      ∃allocation,(allocation,row.2.tag)∈frame.protectedTags.toList) (lower upper : UInt64) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree (global.endCall frame).protectedTags root .Write) lower upper tree.locations := by
  apply owned tree root initial (global.endCall frame).protectedTags _ lower upper
  intro row member
  rcases covered row member with absent | owned
  · cases held : (global.endCall frame).protectedTags.contains row.2.tag with
    | false => rfl
    | true =>
      have original:=GeneralBorrowRelease.end_call_weakens global frame row.2.tag held
      rw[absent] at original
      cases original
  · obtain ⟨allocation,stored⟩:=owned
    exact GeneralBorrowRelease.end_call_owned_absent global frame allocation row.2.tag stored
end DuplicatePrefix.GeneralBorrowStructuralHistoryRootAuthorityState
