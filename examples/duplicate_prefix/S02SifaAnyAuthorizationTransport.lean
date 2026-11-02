import duplicate_prefix.S02SifaResidualForeign
import duplicate_prefix.GeneralBorrowAuthorizationMetadata
import duplicate_prefix.GeneralBorrowSifaProfileTransport

namespace DuplicatePrefix.S02SifaAnyAuthorizationTransport
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization GeneralBorrowSharedAuthorizationGeometry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Runtime permission/cache consistency makes a lost Foreign Read skip safe
when the two classifications coincide, including weakening all the way to None. -/
theorem authorized_read_weaken (state : LocationState) (strongest : IdempotentForeignAccess)
    (held : Bool) (query : Option WildcardAccessRelatedness)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state held)
    (old : DuplicatePrefixCallbackVisitAuthorization.Authorized state .Read held query query) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized
      {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1}
      .Read held query query := by
  by_cases foreign : query = some .ForeignAccess
  · subst query
    rcases state with ⟨permission,accessed,cache⟩
    cases permission with
    | ReservedFrz conflicted =>
      cases conflicted <;> cases accessed <;> cases cache <;> cases strongest <;> cases held <;>
        simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,
          Permission.strongestIdempotentForeignAccess,DuplicatePrefixCallbackVisitAuthorization.Authorized,
          DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,
          IdempotentForeignAccess.ensureNoStrongerThan,IdempotentForeignAccess.canSkipForeignAccess,
          IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
          IdempotentForeignAccess.fromForeign,AccessRelatedness.isForeign,Permission.isDisabled,
          Permission.isFrozen,DuplicatePrefixScalarAuthorization.Compatible,
          GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible]
    | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases accessed <;> cases cache <;> cases strongest <;> cases held <;>
        simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,
          Permission.strongestIdempotentForeignAccess,DuplicatePrefixCallbackVisitAuthorization.Authorized,
          DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,
          IdempotentForeignAccess.ensureNoStrongerThan,IdempotentForeignAccess.canSkipForeignAccess,
          IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
          IdempotentForeignAccess.fromForeign,AccessRelatedness.isForeign,Permission.isDisabled,
          Permission.isFrozen,DuplicatePrefixScalarAuthorization.Compatible,
          GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible]
  · exact S02SifaQueryWeakening.authorized_weaken_of_entry_not_foreign state strongest .Read held query query foreign old

/-- Full callback metadata transport permits the exact scalar cache weakening
performed by child constructors on supported ancestors. -/
theorem transport (strongest : IdempotentForeignAccess) (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (nextDepth : GeneralBorrowExposure.ParentDepth after.nodes)
    (size : before.nodes.size ≤ after.nodes.size)
    (metadata : ∀ index node,before.nodes.get index = some node →
      ∃ next,after.nodes.get index = some next ∧ next.parent = node.parent ∧
        next.tag = node.tag ∧ next.children = node.children ∧ next.isExposed = node.isExposed ∧
        ((newLocation.perms.get index).getD next.defaultLocationState).permission =
        ((oldLocation.perms.get index).getD node.defaultLocationState).permission)
    (back : ∀ index next,after.nodes.get index = some next → next.isExposed = true →
      ∃ node,before.nodes.get index = some node)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization before oldLocation protections root position maximum kind support)
    (consistent : ∀ query node,support query → before.nodes.get query = some node →
      GeneralBorrowSifaPermissionConsistency.Consistent
        ((oldLocation.perms.get query).getD node.defaultLocationState) (protections.contains node.tag))
    (states : ∀ query node next,support query → before.nodes.get query = some node → after.nodes.get query = some next →
      ((newLocation.perms.get query).getD next.defaultLocationState) =
        ((oldLocation.perms.get query).getD node.defaultLocationState) ∨
      ((newLocation.perms.get query).getD next.defaultLocationState) =
        {((oldLocation.perms.get query).getD node.defaultLocationState) with
          idempotentForeignAccess :=
            (((oldLocation.perms.get query).getD node.defaultLocationState).idempotentForeignAccess.ensureNoStrongerThan strongest).1}) :
    Authorization after newLocation protections root position maximum kind support := by
  have count (query : UniIndex) (removed : List UniIndex) :
      residualCount after newLocation protections kind removed query =
      residualCount before oldLocation protections kind removed query := by
    apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension before after oldLocation newLocation
      protections depth size _ back removed query kind
    intro index node present
    obtain ⟨next,found,parent,tag,children,exposed,permission⟩ := metadata index node present
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
    obtain ⟨next,found,parent,tag,children,exposure,permission⟩ := metadata index oldNode oldPresent
    have equal := Option.some.inj (found.symm.trans present)
    subst next
    refine ⟨oldNode,oldPresent,?_⟩
    simpa only [removable,effective,aboveMaximum,tag,exposure,permission] using allowed
  have oldNode (query : UniIndex) (included : support query) (node : TreeNode)
      (present : after.nodes.get query = some node) :
      ∃ previous,before.nodes.get query = some previous ∧ node.parent = previous.parent ∧
        node.tag = previous.tag ∧ node.children = previous.children ∧ node.isExposed = previous.isExposed ∧
        ((newLocation.perms.get query).getD node.defaultLocationState).permission =
          ((oldLocation.perms.get query).getD previous.defaultLocationState).permission := by
    obtain ⟨previous,found⟩ := old.present query included
    obtain ⟨next,nextFound,fields⟩ := metadata query previous found
    have equal := Option.some.inj (nextFound.symm.trans present)
    subst next
    exact ⟨previous,found,fields⟩
  refine ⟨old.rooted,?_,?_,?_,?_,?_,?_⟩
  · intro query included
    obtain ⟨node,present⟩ := old.present query included
    obtain ⟨next,found,_⟩ := metadata query node present
    exact ⟨next,found⟩
  · intro query node included present child member
    obtain ⟨previous,found,parent,tag,children,_⟩ := oldNode query included node present
    exact old.children query previous included found child (by simpa only [children] using member)
  · intro query included
    obtain ⟨node,present⟩ := old.present query included
    apply covers_of_path after nextDepth root query
    apply path_extension before after _ root query
      (GeneralBorrowWildcardControlWitness.path_of_covers before depth root query node present (old.covers query included))
    intro index node present
    obtain ⟨next,found,parent,_⟩ := metadata index node present
    exact ⟨next,found,parent⟩
  · intro query node included present
    obtain ⟨previous,found,_⟩ := oldNode query included node present
    rcases states query previous node included found present with same | weakened
    · rw [same];exact old.possible query previous included found
    · rw [weakened];exact old.possible query previous included found
  · intro entry exit legalEntry legalExit subset query node included present retained
    obtain ⟨previous,found,parent,tag,children,exposure,permission⟩ := oldNode query included node present
    have relation (removed : List UniIndex) :
        residualRelation after newLocation protections root query node maximum kind position removed =
          residualRelation before oldLocation protections root query previous maximum kind position removed := by
      simp only [residualRelation,count,aboveMaximum,tag]
    rw [relation entry,relation exit,tag]
    have initial := old.queries entry exit (removal entry legalEntry) (removal exit legalExit)
      subset query previous included found retained
    rcases states query previous node included found present with same | weakened
    · rw [same];exact initial
    · rw [weakened]
      cases kind with
      | Read =>
        have entryEmpty := read_removal_empty before oldLocation protections maximum entry (removal entry legalEntry)
        have exitEmpty := read_removal_empty before oldLocation protections maximum exit (removal exit legalExit)
        subst entry
        subst exit
        exact authorized_read_weaken _ strongest _ _ (consistent query previous included found) initial
      | Write =>
        exact S02SifaResidualForeign.write_query_weaken before oldLocation protections root query previous position maximum
          support old entry exit (removal entry legalEntry) (removal exit legalExit) subset included found retained strongest
          (consistent query previous included found)
  · intro physical
    obtain ⟨query,node,included,present,witness⟩ := old.witness physical
    obtain ⟨next,found,parent,tag,children,exposure,permission⟩ := metadata query node present
    refine ⟨query,next,included,found,?_⟩
    simpa only [Supports,tag,exposure,permission] using witness

end DuplicatePrefix.S02SifaAnyAuthorizationTransport
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SifaAnyAuthorizationTransport.transport,
      ``DuplicatePrefix.S02SifaAnyAuthorizationTransport.authorized_read_weaken] do
   for ax in (← collectAxioms name) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
