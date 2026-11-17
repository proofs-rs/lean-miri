import duplicate_prefix.CurrentCallOptionalSharedOldAuthority
import duplicate_prefix.CurrentCallSharedConstructorFrame
import duplicate_prefix.S03EmptySharedRuntime
import duplicate_prefix.CurrentCallAllocationLicense
namespace DuplicatePrefix.CurrentCallZeroSharedBoolFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open OrdinaryBorrowAuthority GeneralBorrowView GeneralRangeMapOrigins GeneralRangeMapState
open S05CompletedAncestryReadMutable S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open Lean Elab Term in
elab "zero_shared_rule " suffix:str : term => do
  let found:=(←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked zero-shared helper {suffix.getString}"
noncomputable section

private theorem stage_location (tree : BorrowTree) (C : Completion) (flags : ProtectedTags)
    (parents : ParentInterpretation tree C) (source : UniIndex) (sourceLive : ∃node,tree.nodes.get source=some node)
    (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child=none) (parentAt : tree.nodes.get parent=some parentNode)
    (mapping : UniKeyMap BorTag) (location : LocationTree) (clean : location.perms.get child=none)
    (owned : Authority tree C flags source location) :
    Authority (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent) mapping tree.locations)
      (extend C child parent) flags source location := by
  let stage:=GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent) mapping tree.locations
  intro index node present
  by_cases new : index=child
  · subst index
    have different : parent≠child:=by intro same;rw [same,vacant] at parentAt;cases parentAt
    have childAt : stage.nodes.get child=some (GeneralBorrowFreshAnchor.sharedNode tag parent) := by
      dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
      rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same]
    have nodeEq : node=GeneralBorrowFreshAnchor.sharedNode tag parent:=Option.some.inj (present.symm.trans childAt)
    constructor
    · intro below
      have old:=(CurrentCallResourceChild.old_ancestry_iff tree C parents child parent vacant sourceLive).mp below
      obtain ⟨oldNode,oldAt⟩:=(zero_shared_rule "CurrentCallOptionalSharedOldAuthority.ancestor_live") tree C parents old sourceLive
      rw [vacant] at oldAt
      cases oldAt
    · intro _
      simp [RawState,clean,nodeEq,GeneralBorrowFreshAnchor.sharedNode,TreeNode.defaultLocationState,ForeignWrite,LocationState.possible,Permission.isUnique]
  · have old : ∃old,tree.nodes.get index=some old ∧node.tag=old.tag ∧node.defaultInitialPermission=old.defaultInitialPermission := by
      dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes] at present
      by_cases same : index=parent
      · subst index
        rw [GeneralBorrowFreshLocation.get_same] at present
        have equal : node={parentNode with children:=parentNode.children.push child}:=Option.some.inj present.symm
        exact ⟨parentNode,parentAt,by rw [equal],by rw [equal]⟩
      · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ same,GeneralBorrowFreshLocation.get_other _ _ _ _ new] at present
        exact ⟨node,present,rfl,rfl⟩
    obtain ⟨old,oldAt,tagEq,permission⟩:=old
    have effective : stateShape (RawState location index node)=stateShape (RawState location index old) := by
      simp only [RawState]
      cases location.perms.get index <;> simp [stateShape,TreeNode.defaultLocationState,permission]
    have scalar:=(zero_shared_rule "CurrentCallOptionalSharedOldAuthority.authority_state") _ _ effective (flags.contains node.tag)
    have previous:=owned index old oldAt
    rw [←tagEq] at previous
    have ancestry:=CurrentCallResourceChild.old_ancestry_iff tree C parents child parent vacant (ancestor:=index) sourceLive
    exact ⟨fun below=>scalar.1.mpr (previous.1 (ancestry.mp below)),fun outside=>scalar.2.mpr (previous.2 (fun below=>outside (ancestry.mpr below)))⟩

/-- The newly inserted Frozen row is dormant at every byte. Therefore even a
Strong protector on this zero-extent child does not obstruct the old Bool
reservation. No source/constructor-parent authority is assumed. -/
theorem owned (tree : BorrowTree) (C : Completion) (flags : ProtectedTags)
    (parents : ParentInterpretation tree C) (parentTag tag : BorTag)
    (input : EmptyForestSharedPool.Input tree parentTag tag)
    (source : UniIndex) (sourceLive : ∃node,tree.nodes.get source=some node)
    (lower upper : UInt64) (old : OwnedOn (Authority tree C flags source) lower upper tree.locations) :
    OwnedOn (Authority input.after (extend C input.index input.parent) flags source) lower upper input.after.locations := by
  have staged : OwnedOn (Authority input.stage (extend C input.index input.parent) flags source) lower upper input.stage.locations := by
    intro position valid positive below above
    exact stage_location tree C flags parents source sourceLive input.index input.parent input.parentNode tag input.vacant input.present input.mapping
      tree.locations.entries[position].data (input.clean position valid) (old position valid positive below above)
  exact (zero_shared_rule "CurrentCallOptionalSharedOldAuthority.shape_owned") input.stage input.after _ flags source lower upper
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read) staged

/-- Exact optional parent interpretation for the actual zero Shared pool
constructor, in either append/reuse and either protection branch. -/
theorem metadata (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : tag.value.toNat<global.nextPointerTag.value.toNat)
    (primaryLive : ∃node,tree.nodes.get allocationRoot=some node)
    (parentOrder : input.parentNode.tag.value≤tag.value) :
    DuplicatePrefixBorrowContract.RuntimeFacts input.after global ∧
    LeafFrame tree input.after input.index input.parent ∧
    ParentInterpretation input.after (extend C input.index input.parent) := by
  have afterRuntime:=S03EmptySharedRuntime.construct tree global runtime parentTag tag input room tagBound
  have shape:=GeneralBorrowSifaView.preserves input.stage input.parent .Read
  have exposure:=GeneralBorrowFreshMetadataChildSifa.sifa_exposure input.stage input.parent .Read
  have size : input.after.nodes.data.size=max tree.nodes.data.size (input.index.toNat+1) := by
    have known:=EmptyForestSharedPoolNext.node_size input
    change input.after.nodes.data.size=tree.nodes.data.size+EmptyForestSharedPoolNext.growth input at known
    rw [known]
    cases selected : input.slot with
    | append noFree aligned fits=>
      have endEq : input.index.toNat=tree.nodes.data.size := by
        simp only [EmptyForestSharedPool.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size<2^32)]
        exact aligned
      simp only [EmptyForestSharedPoolNext.growth,selected]
      omega
    | reuse index available bounded missing slack=>
      have same : input.index=index:=by simp only [EmptyForestSharedPool.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index]
      simp only [EmptyForestSharedPoolNext.growth,selected]
      rw [same]
      change index.toNat<tree.nodes.data.size at bounded
      omega
  have roots : input.after.roots=tree.roots:=(GeneralBorrowFreshMetadata.roots input.stage input.after shape).trans rfl
  have frame:=(zero_shared_rule "CurrentCallSharedConstructorFrame.frame_of_stage") tree input.after global afterRuntime input.index input.parent input.parentNode tag
    input.vacant input.present input.mapping tree.locations shape exposure size roots
  have order:=GeneralBorrowFreshParentTagOrder.staged_order tree input.depth parents.order input.index input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present rfl parentOrder input.mapping tree.locations input.after shape
  exact ⟨afterRuntime,frame,CurrentCallParentInsertion.of_leaf tree input.after C parents input.index input.parent frame primaryLive afterRuntime.formed.toGraphState order⟩

/-- The same actual constructor retains a separate current Bool node's tag,
physical parent, hidden leaf and activity, and arbitrary zero-source quiescence. -/
theorem facets (tree : BorrowTree) (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (target : UniIndex) (node : TreeNode) (present : tree.nodes.get target=some node) (different : target≠input.parent)
    (lower upper : UInt64) (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper)
    (zero : UniIndex) (quiet : S04ReturnReleaseInactive.Quiescent tree zero) :
    (∃next,input.after.nodes.get target=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧next.children=node.children ∧next.isExposed=node.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin input.after target .Write lower upper ∧S04ReturnReleaseInactive.Quiescent input.after zero := by
  have notChild : target≠input.index:=by intro same;rw [same,input.vacant] at present;cases present
  have staged : input.stage.nodeAt target=some node := by
    change ((tree.nodes.insert input.index (GeneralBorrowFreshAnchor.sharedNode tag input.parent)).insert input.parent _).get target=some node
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ different,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
    exact present
  obtain ⟨next,found,tagEq,parent,children,_,exposure⟩:=GeneralBorrowFreshMetadataChildSifa.node_fields input.stage input.parent .Read target node staged
  exact ⟨⟨next,found,tagEq,parent,children,exposure⟩,S03EmptySharedFrame.activity input target .Write lower upper active,S03EmptySharedFrame.quiescent input zero quiet⟩
end
end DuplicatePrefix.CurrentCallZeroSharedBoolFrame

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallZeroSharedBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual zero Shared Bool frame dependency {dependency}"
