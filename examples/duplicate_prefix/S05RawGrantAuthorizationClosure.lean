import duplicate_prefix.S05RawForeignAuthorizationBridge
import duplicate_prefix.GeneralBorrowResidualPrimaryWitness
import duplicate_prefix.DuplicatePrefixResidualWriteSkip

/-! One-mask closure for an internal raw grant at root position zero.
All authority clauses describe current scalar data independently of callback
success. Virtual grants without an internal origin and cross-root authority
remain open; no ordinary-input coverage theorem is asserted. -/
namespace DuplicatePrefix.S05RawGrantAuthorizationClosure
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardParentTagOrder OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Membership in the actual parent walk gives a physical path, provided
parent links are present as guaranteed by ParentDepth. -/
theorem path_of_walk (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (fuel : Nat) (root index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (member : root ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes fuel index) :
    Path tree root index := by
  induction fuel generalizing index node with
  | zero => simp [GeneralBorrowExposureAncestorFold.walk] at member
  | succ fuel ih =>
    simp only [GeneralBorrowExposureAncestorFold.walk,present,List.mem_cons] at member
    rcases member with same | later
    · subst root; exact .refl index node present
    · cases edge : node.parent with
      | none => simp [edge] at later
      | some parent =>
        obtain ⟨parentNode,parentPresent,_⟩ := depth.parent index node present parent edge
        exact .step (ih parent parentNode parentPresent (by simpa [edge] using later)) node present edge

private theorem equal_filter_member {α : Type} (rows : List α) (small large : α → Bool)
    (included : ∀ row ∈ rows, small row = true → large row = true)
    (equal : (rows.filter small).length = (rows.filter large).length) :
    ∀ row ∈ rows, large row = true → small row = true := by
  have filtered : (rows.filter large).filter small = rows.filter small := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro row member
    cases h : small row
    · simp
    · simp [included row member h]
  have sub : List.Sublist (rows.filter small) (rows.filter large) := filtered ▸ List.filter_sublist
  have same := sub.eq_of_length equal
  intro row member qualifies
  have found : row ∈ rows.filter large := List.mem_filter.mpr ⟨member,qualifies⟩
  rw [←same] at found
  exact (List.mem_filter.mp found).2

/-- Equal residual counts force the retained eligible origin below the query.
Coverage makes every query contribution a root contribution. -/
theorem equal_counts_path (tree : BorrowTree) (initial : LocationTree)
    (protections : ProtectedTags) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (maximum : Option BorTag) (removed : List UniIndex)
    (legal : Removal tree initial protections maximum .Write removed)
    (root query origin : UniIndex) (originNode : TreeNode)
    (originPresent : tree.nodes.get origin = some originNode)
    (eligible : Supports initial protections origin originNode maximum .Write)
    (rootPath : Path tree root origin) (covers : Covers tree.nodes root query)
    (equal : residualCount tree initial protections .Write removed query =
      residualCount tree initial protections .Write removed root) : Path tree query origin := by
  let rows := (tree.nodes.entries.toList.filter
    (fun row => !removed.contains row.1))
  have counts (index : UniIndex) : residualCount tree initial protections .Write removed index =
      (rows.filter (contributes tree.nodes (effective initial protections) index .Write)).length := by
    unfold residualCount rows
    rw [List.filter_filter,List.filter_filter]
    congr 1
    apply List.filter_congr
    intro row _
    exact Bool.and_comm _ _
  have retained := GeneralBorrowResidualPrimaryWitness.witness_retained tree initial protections maximum .Write removed legal origin originNode originPresent eligible
  have member : (origin,originNode) ∈ rows := List.mem_filter.mpr
    ⟨(GeneralBorrowFreshReuseProtection.entries_get tree.nodes origin originNode).mpr originPresent,
      by simpa using retained⟩
  have support : supports (effective initial protections origin originNode) .Write = true := by
    have allowed : (effective initial protections origin originNode).allows .Write = true := eligible.2.1
    cases level : effective initial protections origin originNode <;>
      simp_all [supports,GeneralBorrowExposureAncestorFold.supportsWrite,WildcardAccessLevel.allows]
  have qualified : contributes tree.nodes (effective initial protections) root .Write (origin,originNode) = true := by
    simp only [contributes,eligible.1,support,Bool.true_and]
    exact List.contains_iff_mem.mpr (rootPath.walk depth)
  have queryQualified := equal_filter_member rows
    (contributes tree.nodes (effective initial protections) query .Write)
    (contributes tree.nodes (effective initial protections) root .Write) (by
      intro row member qualified
      have original := (List.mem_filter.mp member).1
      simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at qualified ⊢
      exact ⟨qualified.1,covers row original qualified.2⟩)
    (by simpa only [counts] using equal) (origin,originNode) member qualified
  have walkMember : query ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) origin := by
    simpa [contributes,eligible.1,support,List.contains_iff_mem] using queryQualified
  exact path_of_walk tree depth _ query origin originNode originPresent walkMember

/-- An internal eligible grant closes one legal residual mask at any entry
classification. Authority is independent present-state data, not a successful
callback or future Result. -/
theorem authorized (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (maximum : Option BorTag) (removed : List UniIndex)
    (legal : Removal tree initial protections maximum .Write removed)
    (root query origin : UniIndex) (node originNode : TreeNode)
    (present : tree.nodes.get query = some node)
    (originPresent : tree.nodes.get origin = some originNode)
    (eligible : Supports initial protections origin originNode maximum .Write)
    (rootCovers : Covers tree.nodes root origin) (covers : Covers tree.nodes root query)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((initial.perms.get query).getD node.defaultLocationState) (protections.contains node.tag))
    (localAuthority : Path tree query origin → LocalWrite
      ((initial.perms.get query).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignAuthority : ¬ Path tree query origin → ForeignWrite
      ((initial.perms.get query).getD node.defaultLocationState) (protections.contains node.tag))
    (entry : Option WildcardAccessRelatedness) :
    DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
      ((initial.perms.get query).getD node.defaultLocationState) .Write (protections.contains node.tag)
      entry (residualRelation tree initial protections root query node maximum .Write 0 removed) := by
  have selfPath : Path tree origin origin := .refl origin originNode originPresent
  have rootWalk := rootCovers (origin,originNode)
    ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes origin originNode).mpr originPresent)
    (selfPath.walk depth)
  have rootPath := path_of_walk tree depth _ root origin originNode originPresent rootWalk
  have rootPositive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth maximum .Write removed legal root origin originNode originPresent eligible rootPath
  have rootNonzero : (residualCount tree initial protections .Write removed root == 0) = false := by
    simp [Nat.ne_of_gt rootPositive]
  by_cases path : Path tree query origin
  · have raw := localAuthority path
    have localPositive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth maximum .Write removed legal query origin originNode originPresent eligible path
    have localNonzero : (residualCount tree initial protections .Write removed query == 0) = false := by
      simp [Nat.ne_of_gt localPositive]
    have unclamped := path_not_above tree order initial protections maximum .Write query origin node originNode present originPresent path eligible
    apply DuplicatePrefixCallbackVisitAuthorizationRepaired.old_inclusion
    refine ⟨raw.1,Or.inr ?_⟩
    by_cases equal : residualCount tree initial protections .Write removed root =
        residualCount tree initial protections .Write removed query
    · simpa [residualRelation,unclamped,classify,rootNonzero,localNonzero,equal,skip,AccessRelatedness.isForeign]
        using OrdinaryBorrowAuthorityBridge.local_scalar _ _ raw .Write
    · simp [residualRelation,unclamped,classify,rootNonzero,localNonzero,equal]
  · have raw := foreignAuthority path
    have different : residualCount tree initial protections .Write removed root ≠
        residualCount tree initial protections .Write removed query := by
      intro equal
      exact path (equal_counts_path tree initial protections depth maximum removed legal root query origin originNode originPresent eligible rootPath covers equal.symm)
    have foreign := S05RawForeignAuthorizationBridge.foreign_write_authorized _ _ entry consistent raw
    have either : DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
        ((initial.perms.get query).getD node.defaultLocationState) .Write (protections.contains node.tag)
        entry (some .EitherAccess) := .inl ⟨raw.1,Or.inr trivial⟩
    simp only [residualRelation,classify,show (0 != 0) = false from rfl,
      Bool.false_eq_true,ite_false,Nat.add_zero,rootNonzero,
      show (residualCount tree initial protections .Write removed root == residualCount tree initial protections .Write removed query) = false by simp [different]]
    cases aboveMaximum node maximum <;>
      cases zero : (residualCount tree initial protections .Write removed query == 0) <;>
      simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals first | exact foreign | exact either

/-- Concrete raw authority supplies the scalar clauses for its actual mapped
origin. Eligibility and same-component root coverage remain explicit data;
this does not cover virtual grants without an internal origin. -/
theorem concrete_authorized (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (maximum : Option BorTag) (removed : List UniIndex)
    (legal : Removal tree initial protections maximum .Write removed)
    (root query origin : UniIndex) (node originNode : TreeNode) (tag : BorTag)
    (mapped : tree.tagMapping.get tag = some origin)
    (raw : ConcreteComponentAuthority tree initial protections tag)
    (representation : OrdinaryBorrowAuthorityBridge.Representation tree initial protections)
    (present : tree.nodes.get query = some node)
    (originPresent : tree.nodes.get origin = some originNode)
    (eligible : Supports initial protections origin originNode maximum .Write)
    (rootCovers : Covers tree.nodes root origin) (covers : Covers tree.nodes root query)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((initial.perms.get query).getD node.defaultLocationState) (protections.contains node.tag))
    (entry : Option WildcardAccessRelatedness) :
    DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
      ((initial.perms.get query).getD node.defaultLocationState) .Write (protections.contains node.tag)
      entry (residualRelation tree initial protections root query node maximum .Write 0 removed) := by
  obtain ⟨anchor,anchorNode,anchorMapped,anchorPresent,tagged,localRaw,foreignRaw⟩ := raw
  have same : anchor = origin := Option.some.inj (anchorMapped.symm.trans mapped)
  subst anchor
  have rootPath : Path tree root origin := path_of_walk tree depth _ root origin originNode originPresent
    (rootCovers (origin,originNode)
      ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes origin originNode).mpr originPresent)
      ((Path.refl origin originNode originPresent).walk depth))
  have queryPath : Path tree root query := path_of_walk tree depth _ root query node present
    (covers (query,node)
      ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes query node).mpr present)
      ((Path.refl query node present).walk depth))
  apply authorized tree initial protections depth order maximum removed legal root query origin node originNode
    present originPresent eligible rootCovers covers consistent
  · exact localRaw query node present
  · intro unrelated
    obtain ⟨possible,noIM,disabled⟩ := representation query node present
    exact OrdinaryBorrowAuthorityBridge.foreign_scalar _ _ possible noIM disabled
      (foreignRaw query node present ⟨root,rootPath,queryPath⟩ unrelated) .Write

end DuplicatePrefix.S05RawGrantAuthorizationClosure
