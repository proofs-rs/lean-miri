import duplicate_prefix.GeneralBorrowAuthorizationMetadata
import duplicate_prefix.DuplicatePrefixResidualWriteRepaired
import duplicate_prefix.CandidateStableCallOwnership

namespace DuplicatePrefix.CurrentCallEmptyEntryRepairedMetadata
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization GeneralBorrowSharedAuthorizationGeometry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Full authorization transport uses permission metadata globally and exact
scalar states only on its support. Hidden extensions and SIFA rewrites fit the
same finite-data interface; no operational success is assumed. -/
theorem transport (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (nextDepth : GeneralBorrowExposure.ParentDepth after.nodes)
    (size : before.nodes.size ≤ after.nodes.size)
    (metadata : ∀ index node,before.nodes.get index = some node →
      ∃ next,after.nodes.get index = some next ∧ next.parent = node.parent ∧
        next.tag = node.tag ∧ next.isExposed = node.isExposed ∧
        ((newLocation.perms.get index).getD next.defaultLocationState).permission =
        ((oldLocation.perms.get index).getD node.defaultLocationState).permission)
    (back : ∀ index next,after.nodes.get index = some next → next.isExposed = true →
      ∃ node,before.nodes.get index = some node)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization before oldLocation protections root position maximum kind support)
    (nodes : ∀ query,support query → after.nodes.get query = before.nodes.get query)
    (slots : ∀ query,support query → newLocation.perms.get query = oldLocation.perms.get query) :
    DuplicatePrefixResidualWriteRepaired.Authorization after newLocation protections root position maximum kind support := by
  have count (query : UniIndex) (removed : List UniIndex) :
      residualCount after newLocation protections kind removed query =
      residualCount before oldLocation protections kind removed query := by
    apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension before after oldLocation newLocation
      protections depth size _ back removed query kind
    intro index node present
    obtain ⟨next,found,parent,tag,exposed,permission⟩ := metadata index node present
    refine ⟨next,found,parent,exposed,?_⟩
    simp only [effective,tag,permission]
  have removal (removed : List UniIndex) (legal : Removal after newLocation protections maximum kind removed) :
      Removal before oldLocation protections maximum kind removed := by
    refine ⟨legal.distinct,?_⟩
    intro index member
    obtain ⟨node,present,allowed⟩ := legal.allowed index member
    have exposed : node.isExposed = true := by
      cases kind with
      | Read => simp only [removable,Bool.false_eq_true] at allowed
      | Write =>
        cases flag : node.isExposed
        · simp only [removable,flag,Bool.false_and,Bool.false_eq_true] at allowed
        · rfl
    obtain ⟨oldNode,oldPresent⟩ := back index node present exposed
    obtain ⟨next,found,parent,tag,exposure,permission⟩ := metadata index oldNode oldPresent
    have equal := Option.some.inj (found.symm.trans present)
    subst next
    refine ⟨oldNode,oldPresent,?_⟩
    simpa only [removable,effective,aboveMaximum,tag,exposure,permission] using allowed
  refine ⟨old.rooted,?_,?_,?_,?_,?_,?_⟩
  · intro query included
    rw [nodes query included];exact old.present query included
  · intro query node included present child member
    rw [nodes query included] at present
    exact old.children query node included present child member
  · intro query included
    obtain ⟨node,present⟩ := old.present query included
    apply covers_of_path after nextDepth root query
    apply path_extension before after _ root query
      (GeneralBorrowWildcardControlWitness.path_of_covers before depth root query node present (old.covers query included))
    intro index node present
    obtain ⟨next,found,parent,_⟩ := metadata index node present
    exact ⟨next,found,parent⟩
  · intro query node included present
    rw [nodes query included] at present
    simpa only [slots query included] using old.possible query node included present
  · intro entry exit legalEntry legalExit subset query node included present retained
    rw [nodes query included] at present
    have initial := old.queries entry exit (removal entry legalEntry) (removal exit legalExit)
      subset query node included present retained
    simpa only [residualRelation,count,slots query included] using initial
  · intro physical
    obtain ⟨query,node,included,present,witness⟩ := old.witness physical
    refine ⟨query,node,included,?_,?_⟩
    · rw [nodes query included];exact present
    · simpa only [Supports,slots query included] using witness

/-- Legal masks and their actual repaired query counts survive the same
hidden metadata extension. This is consumed by the old-root retained Write
classification after the empty helpers; no completion is required. -/
theorem mask_frame (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (size : before.nodes.size ≤ after.nodes.size)
    (metadata : ∀ index node,before.nodes.get index = some node →
      ∃ next,after.nodes.get index = some next ∧ next.parent = node.parent ∧
        next.tag = node.tag ∧ next.isExposed = node.isExposed ∧
        ((newLocation.perms.get index).getD next.defaultLocationState).permission =
        ((oldLocation.perms.get index).getD node.defaultLocationState).permission)
    (back : ∀ index next,after.nodes.get index = some next → next.isExposed = true →
      ∃ node,before.nodes.get index = some node)
    (root query : UniIndex) (position : Nat) (maximum : Option BorTag)
    (kind : AccessKind) (node : TreeNode) (removed : List UniIndex)
    (legal : Removal after newLocation protections maximum kind removed) :
    Removal before oldLocation protections maximum kind removed ∧
      residualRelation after newLocation protections root query node maximum kind position removed =
      residualRelation before oldLocation protections root query node maximum kind position removed := by
  have count (query : UniIndex) (removed : List UniIndex) :
      residualCount after newLocation protections kind removed query =
      residualCount before oldLocation protections kind removed query := by
    apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension before after oldLocation newLocation
      protections depth size _ back removed query kind
    intro index node present
    obtain ⟨next,found,parent,tag,exposed,permission⟩ := metadata index node present
    refine ⟨next,found,parent,exposed,?_⟩
    simp only [effective,tag,permission]
  have removal (removed : List UniIndex) (legal : Removal after newLocation protections maximum kind removed) :
      Removal before oldLocation protections maximum kind removed := by
    refine ⟨legal.distinct,?_⟩
    intro index member
    obtain ⟨node,present,allowed⟩ := legal.allowed index member
    have exposed : node.isExposed = true := by
      cases kind with
      | Read => simp only [removable,Bool.false_eq_true] at allowed
      | Write =>
        cases flag : node.isExposed
        · simp only [removable,flag,Bool.false_and,Bool.false_eq_true] at allowed
        · rfl
    obtain ⟨oldNode,oldPresent⟩ := back index node present exposed
    obtain ⟨next,found,parent,tag,exposure,permission⟩ := metadata index oldNode oldPresent
    have equal := Option.some.inj (found.symm.trans present)
    subst next
    refine ⟨oldNode,oldPresent,?_⟩
    simpa only [removable,effective,aboveMaximum,tag,exposure,permission] using allowed
  exact ⟨removal removed legal,by simp only [residualRelation,count]⟩

/-- The old-root callback and its source-relative repaired classification
move together through actual hidden helper metadata. The endpoint derives the
ancestry equivalence for its own two real child extensions. -/
theorem queries (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (nextDepth : GeneralBorrowExposure.ParentDepth after.nodes)
    (size : before.nodes.size ≤ after.nodes.size)
    (metadata : ∀ index node,before.nodes.get index = some node →
      ∃ next,after.nodes.get index = some next ∧ next.parent = node.parent ∧
        next.tag = node.tag ∧ next.isExposed = node.isExposed ∧
        ((newLocation.perms.get index).getD next.defaultLocationState).permission =
        ((oldLocation.perms.get index).getD node.defaultLocationState).permission)
    (back : ∀ index next,after.nodes.get index = some next → next.isExposed = true →
      ∃ node,before.nodes.get index = some node)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization before oldLocation protections root position maximum kind support)
    (nodes : ∀ query,support query → after.nodes.get query = before.nodes.get query)
    (slots : ∀ query,support query → newLocation.perms.get query = oldLocation.perms.get query)
    (beforeC afterC : CandidateStableCallOwnership.Completion) (source : UniIndex)
    (classification : ∀ removed,Removal before oldLocation protections maximum kind removed →
      ∀ query node,support query → before.nodes.get query = some node →
      let relation := residualRelation before oldLocation protections root query node maximum kind position removed
      (CandidateStableCallOwnership.Below beforeC query source → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
      (¬CandidateStableCallOwnership.Below beforeC query source → relation = some .ForeignAccess ∨ relation = some .EitherAccess))
    (ancestry : ∀ query,support query →
      (CandidateStableCallOwnership.Below afterC query source ↔ CandidateStableCallOwnership.Below beforeC query source)) :
    DuplicatePrefixResidualWriteRepaired.Authorization after newLocation protections root position maximum kind support ∧
      ∀ removed,Removal after newLocation protections maximum kind removed →
      ∀ query node,support query → after.nodes.get query = some node →
      let relation := residualRelation after newLocation protections root query node maximum kind position removed
      (CandidateStableCallOwnership.Below afterC query source → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
      (¬CandidateStableCallOwnership.Below afterC query source → relation = some .ForeignAccess ∨ relation = some .EitherAccess) := by
  refine ⟨transport before after oldLocation newLocation protections depth nextDepth size metadata back
    root position maximum kind support old nodes slots,?_⟩
  intro removed legal query node included present
  have oldPresent : before.nodes.get query = some node := (nodes query included).symm.trans present
  obtain ⟨oldLegal,equal⟩ := mask_frame before after oldLocation newLocation protections depth size metadata back
    root query position maximum kind node removed legal
  have classified := classification removed oldLegal query node included oldPresent
  dsimp only at classified ⊢
  rw [equal]
  exact ⟨fun below => classified.1 ((ancestry query included).mp below),
    fun outside => classified.2 (fun below => outside ((ancestry query included).mpr below))⟩

end DuplicatePrefix.CurrentCallEmptyEntryRepairedMetadata

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryRepairedMetadata" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved repaired metadata dependency {dependency}"
