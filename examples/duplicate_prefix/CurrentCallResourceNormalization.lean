import duplicate_prefix.CandidateCurrentUniformOwnerWindow
import duplicate_prefix.CandidateCurrentGrantRuntime
import duplicate_prefix.CandidateCurrentWindowAuthority
import duplicate_prefix.OrdinaryPhysicalValidity
import duplicate_prefix.S05CompletedWriteAuthorityRetention
import duplicate_prefix.S05WildcardCompletedWriteQueries

/-! UNADOPTED finite current resource normalization. Allocation-origin issuance
is distinct from scalar availability: an arbitrary Loan.parent=none cannot
mint a nonempty authority. There is no caller trace, successful access, future
permission table or adopted Ordinary predicate here. Constructor/copy/GC
adequacy of this current interpretation remains an explicit separate obligation. -/
namespace DuplicatePrefix.CurrentCallResourceNormalization
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open GeneralBorrowExposureCardinality OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def allocationRoot : UniIndex := ⟨0⟩

/-- One allocation-origin identity/extent license in the current resource
context. It grants NO active bytes by itself: current contents still require
Embeds. Canonical new/rootPointerTag and GC preservation justify these current
representation fields; arbitrary OrderedState alone is not asserted to do so. -/
structure AllocationCapability (before : Before) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree) : Prop where
  live : Present (ActualWorld before) id allocation
  extent : allocation.len = allocation.byteSize.bytes.toNat
  treeExtent : allocation.extra.locations.size = allocation.byteSize
  rootSlot : allocation.extra.roots[0]? = some allocationRoot
  rootNode : ∃ node, allocation.extra.nodes.get allocationRoot = some node ∧
    node.parent = none ∧ node.defaultInitialPermission = .Disabled ∧
    tracker.global.rootTag? id = some node.tag

/-- ONE optional parent interpretation. Every physical edge is retained;
CHOSEN virtual edges have real older exposed origins. There is deliberately no
requirement that every later physical component choose a virtual parent. -/
structure ParentInterpretation (tree : BorrowTree) (completion : Completion) : Prop where
  graph : GeneralBorrowStructuralHistoryState.GraphState tree
  order : ParentTagOrder tree
  dimension : completion.parents.size = tree.nodes.data.size
  physical : ∀ index node, tree.nodes.get index = some node → ∀ parent,
    node.parent = some parent → completion.parents[index.toNat]? = some (some parent)
  edgeLive : ∀ child parent, completion.parents[child.toNat]? = some (some parent) →
    (∃ node, tree.nodes.get child = some node) ∧ (∃ node, tree.nodes.get parent = some node)
  primaryNone : completion.parents[allocationRoot.toNat]? = some none
  virtual : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → ∀ (origin : UniIndex),
    completion.parents[root.toNat]? = some (some origin) →
    ∃ (earlier : Nat) (originRoot : UniIndex) (rootNode originNode : TreeNode),
      earlier < position ∧ tree.roots[earlier]? = some originRoot ∧
      tree.nodes.get root = some rootNode ∧ tree.nodes.get origin = some originNode ∧
      originNode.isExposed = true ∧ originNode.tag.value < rootNode.tag.value ∧
      Path tree originRoot origin

/-- Finite SPATIAL issuance, not an execution/history certificate. Restriction,
splitting and read sharing operate on content fragments without changing this
family issuance. A physical Path summarizes inactive/removed intermediate
handles. Wildcard delegation names an already-issued current origin GRANT and
the fixed parent-map edge, with actual exposure/order data. This grant-indexed
relation does not carry a parent-family record or prove copy correlation; that
broader family-issuance adequacy remains OPEN. It cannot invent a parent edge
for an irrelevant component. -/
inductive SpatialDelegation (before : Before) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree) (completion : Completion) : UniIndex → Prop
  | allocated (capability : AllocationCapability before tracker id allocation) :
      SpatialDelegation before tracker id allocation completion allocationRoot
  | concrete {parent child : UniIndex} :
      SpatialDelegation before tracker id allocation completion parent →
      Path allocation.extra parent child →
      SpatialDelegation before tracker id allocation completion child
  | wildcard {origin root : UniIndex} (originNode rootNode : TreeNode)
      (earlier position : Nat) (originRoot : UniIndex) :
      SpatialDelegation before tracker id allocation completion origin →
      allocation.extra.nodes.get origin = some originNode → originNode.isExposed = true →
      allocation.extra.nodes.get root = some rootNode → rootNode.parent = none →
      originNode.tag.value < rootNode.tag.value → earlier < position →
      allocation.extra.roots[earlier]? = some originRoot → allocation.extra.roots[position]? = some root →
      Path allocation.extra originRoot origin →
      completion.parents[root.toNat]? = some (some origin) →
      SpatialDelegation before tracker id allocation completion root

namespace ParentInterpretation

theorem physical_below {tree completion} (model : ParentInterpretation tree completion)
    {first last : UniIndex} (physical : Path tree first last) : Below completion first last := by
  induction physical with
  | refl => exact .refl _
  | step _ node present edge ih => exact .step (model.physical _ node present _ edge) ih

theorem physical_suffix {tree completion} (model : ParentInterpretation tree completion)
    {root last query : UniIndex} (physical : Path tree root last) (below : Below completion query last) :
    Below completion query root ∨ Path tree root query := by
  induction physical generalizing query with
  | refl => exact .inl below
  | @step parent child earlier node present edge ih =>
    cases below with
    | refl => exact .inr (.step earlier node present edge)
    | @step otherParent _ completed prior =>
      have same : otherParent = parent := Option.some.inj
        (Option.some.inj (completed.symm.trans (model.physical child node present parent edge)))
      subst otherParent
      exact ih prior

theorem virtual_parent {tree completion} (model : ParentInterpretation tree completion)
    {child parent : UniIndex} {childNode : TreeNode}
    (present : tree.nodes.get child = some childNode) (parentless : childNode.parent = none)
    (edge : completion.parents[child.toNat]? = some (some parent)) :
    ∃ parentNode, tree.nodes.get parent = some parentNode ∧ parentNode.isExposed = true ∧
      parentNode.tag.value < childNode.tag.value := by
  have member : child ∈ tree.roots := Array.mem_toList_iff.mp (model.graph.covered child childNode present parentless)
  obtain ⟨position,slot⟩ := Array.getElem?_of_mem member
  obtain ⟨earlier,originRoot,actual,originNode,_,_,actualAt,originAt,exposed,older,_⟩ := model.virtual position child slot parent edge
  have same := Option.some.inj (present.symm.trans actualAt)
  subst actual
  exact ⟨originNode,originAt,exposed,older⟩

theorem tag_le {tree completion} (model : ParentInterpretation tree completion)
    {first last : UniIndex} {firstNode lastNode : TreeNode}
    (firstAt : tree.nodes.get first = some firstNode) (lastAt : tree.nodes.get last = some lastNode)
    (below : Below completion first last) : firstNode.tag.value ≤ lastNode.tag.value := by
  induction below generalizing lastNode with
  | refl => have same := Option.some.inj (firstAt.symm.trans lastAt);subst lastNode;exact Nat.le_refl _
  | @step parent child edge prior ih =>
    obtain ⟨_,parentNode,parentAt⟩ := model.edgeLive child parent edge
    have earlier := ih parentAt
    have later : parentNode.tag.value ≤ lastNode.tag.value := by
      cases physical : lastNode.parent with
      | none =>
        obtain ⟨origin,originAt,_,older⟩ := model.virtual_parent lastAt physical edge
        have same := Option.some.inj (parentAt.symm.trans originAt)
        subst origin
        exact Nat.le_of_lt older
      | some actual =>
        have same : parent = actual := Option.some.inj
          (Option.some.inj (edge.symm.trans (model.physical child lastNode lastAt actual physical)))
        subst actual
        exact model.order child lastNode lastAt parent parentNode physical parentAt
    exact Nat.le_trans earlier later

theorem physical_or_attachment {tree completion} (model : ParentInterpretation tree completion)
    {first last : UniIndex} {firstNode : TreeNode}
    (firstAt : tree.nodes.get first = some firstNode) (below : Below completion first last) :
    Path tree first last ∨ ∃ origin next originNode nextNode,
      Path tree first origin ∧ tree.nodes.get origin = some originNode ∧ originNode.isExposed = true ∧
      tree.nodes.get next = some nextNode ∧ nextNode.parent = none ∧
      completion.parents[next.toNat]? = some (some origin) ∧ Below completion next last := by
  induction below with
  | refl => exact .inl (.refl _ firstNode firstAt)
  | @step parent child edge prior ih =>
    obtain ⟨⟨childNode,childAt⟩,_⟩ := model.edgeLive child parent edge
    rcases ih with physicalPath | ⟨origin,next,originNode,nextNode,path,present,exposed,nextAt,parentless,chosen,after⟩
    · cases physical : childNode.parent with
      | none =>
        obtain ⟨parentNode,parentAt,exposed,_⟩ := model.virtual_parent childAt physical edge
        exact .inr ⟨parent,child,parentNode,childNode,physicalPath,parentAt,exposed,childAt,physical,edge,.refl child⟩
      | some actual =>
        have same : parent = actual := Option.some.inj
          (Option.some.inj (edge.symm.trans (model.physical child childNode childAt actual physical)))
        subst actual
        exact .inl (.step physicalPath childNode childAt physical)
    · exact .inr ⟨origin,next,originNode,nextNode,path,present,exposed,nextAt,parentless,chosen,.step edge after⟩

theorem cross_root_origin {tree completion} (model : ParentInterpretation tree completion)
    {callbackRoot selectedRoot query source : UniIndex} {callbackNode selectedNode queryNode : TreeNode}
    (callbackAt : tree.nodes.get callbackRoot = some callbackNode) (callbackNone : callbackNode.parent = none)
    (selectedAt : tree.nodes.get selectedRoot = some selectedNode) (selectedNone : selectedNode.parent = none)
    (queryAt : tree.nodes.get query = some queryNode) (different : callbackRoot ≠ selectedRoot)
    (callbackPath : Path tree callbackRoot query) (selectedPath : Path tree selectedRoot source)
    (below : Below completion query source) :
    ∃ origin originNode, tree.nodes.get origin = some originNode ∧ originNode.isExposed = true ∧
      Path tree query origin ∧ Below completion origin selectedRoot ∧ Below completion origin source ∧
      originNode.tag.value ≤ selectedNode.tag.value := by
  have short : Below completion query selectedRoot := by
    rcases model.physical_suffix selectedPath below with above | sameComponent
    · exact above
    · exact False.elim (different (CompletedBorrowAncestry.physical_roots_unique callbackAt callbackNone
        selectedAt selectedNone callbackPath sameComponent))
  rcases model.physical_or_attachment queryAt short with physical | attachment
  · exact False.elim (different (CompletedBorrowAncestry.physical_roots_unique callbackAt callbackNone
      selectedAt selectedNone (CompletedBorrowAncestry.path_trans callbackPath physical) (.refl _ selectedNode selectedAt)))
  · obtain ⟨origin,next,originNode,nextNode,path,present,exposed,_,_,edge,after⟩ := attachment
    have originSelected : Below completion origin selectedRoot := CompletedBorrowAncestry.below_trans (.step edge (.refl origin)) after
    exact ⟨origin,originNode,present,exposed,path,originSelected,
      CompletedBorrowAncestry.below_trans originSelected (model.physical_below selectedPath),
      model.tag_le present selectedAt originSelected⟩

end ParentInterpretation

theorem SpatialDelegation.root_below {before tracker id allocation completion grant}
    (issued : SpatialDelegation before tracker id allocation completion grant)
    (model : ParentInterpretation allocation.extra completion) : Below completion allocationRoot grant := by
  induction issued with
  | allocated => exact .refl _
  | concrete _ path ih => exact CompletedBorrowAncestry.below_trans ih (model.physical_below path)
  | wildcard => apply Below.step <;> assumption

/-- Concrete current clauses; not an adopted ordinary-input predicate. No
unused instance is required live or issued. Capability identities are keyed by
actual allocation IDs; affine content compatibility, not capability identity
alone, prevents duplication of exclusive byte ownership. Every LISTED active content owner has a fixed
actual family and finite allocation/delegation issuance, independently of
current scalar availability. Parent loan annotations alone issue nothing. -/
structure CurrentDenotation (before : Before) (tracker : MachineHooks.BorrowState)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance)
    (call : CallLoans) (data : Identities) : Prop where
  worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup
  interpretationIds : (data.interpretation.precise.toList.map Prod.fst).Nodup
  length : call.length = len.toNat
  claims : Claims data.interpretation call
  listedCopies : StableChoices data
  contents : CandidateFreezeContentResources.Valid data.interpretation.content
  sourceBinding : CandidateCallBindings.SourceBinding before data.interpretation call argument len
  returnBinding : CandidateCallBindings.ReturnBinding before data.interpretation call place
  sourceStorage : len ≠ 0 → ∃ allocation, Present (ActualWorld before) call.sourceId allocation ∧
    OrdinaryPhysicalValidity.MutU8Slice allocation (UInt64.ofNat call.sourceOffset) len
  returnStorage : ∃ allocation, Present (ActualWorld before) call.returnId allocation ∧
    OrdinaryPhysicalValidity.BoolDestination allocation (UInt64.ofNat call.returnOffset)
  active : ∀ byte owner mode, data.interpretation.content byte owner = some ⟨mode,.active⟩ →
    ∃ loan pointer allocation precise,
      data.interpretation.loans[owner]? = some loan ∧ data.interpretation.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present (ActualWorld before) byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ data.interpretation.precise.toList ∧
      ParentInterpretation allocation.extra precise.completion ∧ PointerBinds allocation pointer ∧
      SpatialDelegation before tracker byte.1 allocation precise.completion pointer.grant ∧
      Embeds allocation tracker.global.protectedTags precise.completion pointer.grant byte.2 (demandOf mode)

/-- A single fixed family/current allocation/parent interpretation over a whole
nonempty demand window. Precise.states is unused encoding baggage, not a second
permission table or a source of current ownership. -/
structure UniformWindow (before : Before) (tracker : MachineHooks.BorrowState) (data : Identities)
    (owner : Nat) (id : AllocId) (offset length : Nat) (mode : CandidateFreezeContentResources.Mode) where
  loan : Loan
  pointer : PointerInstance
  allocation : Allocation Provenance BorrowTree
  precise : PreciseAllocation
  loanAt : data.interpretation.loans[owner]? = some loan
  pointerAt : data.interpretation.pointers[loan.pointer]? = some pointer
  pointerId : pointer.allocation = id
  present : Present (ActualWorld before) id allocation
  preciseAt : (id,precise) ∈ data.interpretation.precise.toList
  binding : PointerBinds allocation pointer
  issued : SpatialDelegation before tracker id allocation precise.completion pointer.grant
  parents : ParentInterpretation allocation.extra precise.completion
  window : ∀ byte, Window id offset length byte → byte.2 < allocation.len ∧
    Embeds allocation tracker.global.protectedTags precise.completion pointer.grant byte.2 (demandOf mode)

private theorem uniform_window {before tracker argument len place call data}
    (D : CurrentDenotation before tracker argument len place call data)
    (owner : Nat) (id : AllocId) (offset length : Nat) (mode : CandidateFreezeContentResources.Mode)
    (positive : 0 < length)
    (active : ∀ byte, Window id offset length byte → data.interpretation.content byte owner = some ⟨mode,.active⟩) :
    Nonempty (UniformWindow before tracker data owner id offset length mode) := by
  have first : Window id offset length (id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,pointerId,present,_,preciseAt,parents,binding,issued,embedding⟩ :=
    D.active (id,offset) owner mode (active _ first)
  refine ⟨⟨loan,pointer,allocation,precise,loanAt,pointerAt,pointerId,present,preciseAt,binding,issued,parents,?_⟩⟩
  intro byte inside
  obtain ⟨otherLoan,otherPointer,otherAllocation,otherPrecise,otherLoanAt,otherPointerAt,otherId,
      otherPresent,bound,otherPreciseAt,_,_,_,otherEmbedding⟩ := D.active byte owner mode (active byte inside)
  have loanEq := Option.some.inj (otherLoanAt.symm.trans loanAt)
  subst otherLoan
  have pointerEq := Option.some.inj (otherPointerAt.symm.trans pointerAt)
  subst otherPointer
  rw [inside.1] at otherPresent otherPreciseAt
  have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList D.worldIds
    id otherAllocation allocation otherPresent present
  have preciseEq := CandidateCurrentUniformOwnerWindow.same_id data.interpretation.precise.toList D.interpretationIds
    id otherPrecise precise otherPreciseAt preciseAt
  subst otherAllocation
  subst otherPrecise
  exact ⟨bound,otherEmbedding⟩

theorem UniformWindow.root_below {before tracker data owner id offset length mode}
    (window : UniformWindow before tracker data owner id offset length mode) :
    Below window.precise.completion allocationRoot window.pointer.grant :=
  window.issued.root_below window.parents

/-- Capability identity is extracted from the finite issuance, not supplied as
an extra root-support premise at normalization's call site. -/
theorem SpatialDelegation.capability {before tracker id allocation completion grant}
    (issued : SpatialDelegation before tracker id allocation completion grant) :
    AllocationCapability before tracker id allocation := by
  induction issued with
  | allocated capability => exact capability
  | concrete _ _ ih => exact ih
  | wildcard => assumption

private theorem same_root_ancestor {tree completion} (model : ParentInterpretation tree completion)
    {root query source : UniIndex} {rootNode queryNode : TreeNode}
    (rootAt : tree.nodes.get root = some rootNode) (parentless : rootNode.parent = none)
    (queryAt : tree.nodes.get query = some queryNode) (queryPath : Path tree root query)
    (sourcePath : Path tree root source) (below : Below completion query source) : Path tree query source := by
  rcases model.physical_or_attachment queryAt below with physical | attachment
  · exact physical
  · obtain ⟨origin,next,originNode,nextNode,path,originAt,_,nextAt,nextNone,edge,after⟩ := attachment
    have nextRoot : Below completion next root := by
      rcases model.physical_suffix sourcePath after with above | physicalNext
      · exact above
      · have same := CompletedBorrowAncestry.physical_roots_unique rootAt parentless nextAt nextNone
          physicalNext (.refl _ nextNode nextAt)
        subst next
        exact .refl root
    have rootOrigin := model.physical_below (CompletedBorrowAncestry.path_trans queryPath path)
    have before := UInt64.le_iff_toNat_le.mp (model.tag_le rootAt originAt rootOrigin)
    have afterTag := UInt64.le_iff_toNat_le.mp (model.tag_le nextAt rootAt nextRoot)
    obtain ⟨actual,actualAt,_,older⟩ := model.virtual_parent nextAt nextNone edge
    have same := Option.some.inj (originAt.symm.trans actualAt)
    subst actual
    have strict := UInt64.lt_iff_toNat_lt.mp older
    omega

private theorem local_support (state : LocationState) (held : Bool) (kind : AccessKind)
    (right : LocalWrite state held) : (state.permission.strongestAllowedLocalAccess held).allows kind = true := by
  cases permission : state.permission with
  | ReservedFrz c => cases c <;> cases held <;> cases kind <;>
      simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> cases kind <;>
      simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]

/-- Internal count algebra. Its exposed witnesses are DERIVED below from
issuance and current content tokens; this is not an admission/support field. -/
private theorem masked_shape (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (protections : ProtectedTags) (model : ParentInterpretation tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (rootPosition : Nat) (root source : UniIndex) (maximum : Option BorTag) (kind : AccessKind)
    (origin : ∀ query node,tree.nodes.get query = some node → Path tree root query → Below completion query source →
      ∃ witness witnessNode,tree.nodes.get witness = some witnessNode ∧
        DuplicatePrefixCallbackAuthorization.Supports location protections witness witnessNode maximum kind ∧
        Path tree query witness ∧ Below completion witness source)
    (rootNode : TreeNode) (rootAt : tree.nodes.get root = some rootNode)
    (grounded : rootPosition = 0 → Below completion root source)
    (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node)
    (queryPath : Path tree root query) (removed : List UniIndex)
    (legal : DuplicatePrefixResidualSupportAuthorization.Removal tree location protections maximum kind removed) :
    let relation := DuplicatePrefixResidualSupportAuthorization.residualRelation tree location protections root query node maximum kind rootPosition removed
    0 < DuplicatePrefixResidualSupportAuthorization.residualCount tree location protections kind removed root + (if rootPosition != 0 then 1 else 0) ∧
    (Below completion query source → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
    (¬Below completion query source → relation = some .ForeignAccess ∨ relation = some .EitherAccess) := by
  let count := DuplicatePrefixResidualSupportAuthorization.residualCount tree location protections kind removed
  have covered := GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query queryPath
  have primary : rootPosition = 0 → ∃ witness witnessNode,tree.nodes.get witness = some witnessNode ∧
      DuplicatePrefixCallbackAuthorization.Supports location protections witness witnessNode maximum kind ∧
      Path tree root witness ∧ Below completion witness source :=
    fun zero => origin root rootNode rootAt (.refl root rootNode rootAt) (grounded zero)
  have positive : 0 < count root + if rootPosition != 0 then 1 else 0 := by
    by_cases zero : rootPosition = 0
    · obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := primary zero
      have supported := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind removed legal
        root witness witnessNode lookup eligible path
      simpa [count,zero] using supported
    · simp only [show (rootPosition != 0) = true by simp [zero],ite_true]
      omega
  have nonzero : ((count root + if rootPosition != 0 then 1 else 0) == 0) = false := by
    exact Bool.eq_false_iff.mpr (fun equal => (Nat.ne_of_gt positive) (beq_iff_eq.mp equal))
  refine ⟨positive,?_,?_⟩
  · intro below
    change DuplicatePrefixCallbackAuthorization.classify (count root) (count query) (rootPosition != 0)
      (DuplicatePrefixCallbackAuthorization.aboveMaximum node maximum) = some .LocalAccess ∨
      DuplicatePrefixCallbackAuthorization.classify (count root) (count query) (rootPosition != 0)
      (DuplicatePrefixCallbackAuthorization.aboveMaximum node maximum) = some .EitherAccess
    obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := origin query node present queryPath below
    have localPositive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind removed legal
      query witness witnessNode lookup eligible path
    have localNonzero : (count query == 0) = false := by simp [count,Nat.ne_of_gt localPositive]
    have unclamped := GeneralBorrowWildcardParentTagOrder.path_not_above tree model.order location protections maximum kind
      query witness node witnessNode present lookup path eligible
    by_cases equal : count root + (if rootPosition != 0 then 1 else 0) = count query
    · have equalBool : ((count root + if rootPosition != 0 then 1 else 0) == count query) = true := beq_iff_eq.mpr equal
      simp only [unclamped,DuplicatePrefixCallbackAuthorization.classify,
        nonzero,equalBool,Bool.false_eq_true,ite_true]
      simp
    · have equalBool : ((count root + if rootPosition != 0 then 1 else 0) == count query) = false :=
        Bool.eq_false_iff.mpr (fun same => equal (beq_iff_eq.mp same))
      simp only [unclamped,DuplicatePrefixCallbackAuthorization.classify,
        nonzero,equalBool,localNonzero,Bool.false_eq_true,ite_false]
      simp
  · intro below
    change DuplicatePrefixCallbackAuthorization.classify (count root) (count query) (rootPosition != 0)
      (DuplicatePrefixCallbackAuthorization.aboveMaximum node maximum) = some .ForeignAccess ∨
      DuplicatePrefixCallbackAuthorization.classify (count root) (count query) (rootPosition != 0)
      (DuplicatePrefixCallbackAuthorization.aboveMaximum node maximum) = some .EitherAccess
    have unequal : count root + (if rootPosition != 0 then 1 else 0) ≠ count query := by
      intro equal
      by_cases zero : rootPosition = 0
      · obtain ⟨witness,witnessNode,lookup,eligible,path,witnessBelow⟩ := primary zero
        have outside : query ∉ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) witness := by
          intro walked
          have physical := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query witness witnessNode lookup _ walked
          exact below (CompletedBorrowAncestry.below_trans (model.physical_below physical) witnessBelow)
        have strict := S05CutoffOwnershipGeometry.residual_strict tree location protections depth root query witness witnessNode
          lookup maximum kind removed legal eligible path outside covered
        simp only [zero,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] at equal
        change count query < count root at strict
        omega
      · have bounded : count query ≤ count root := by
          change DuplicatePrefixResidualSupportAuthorization.residualCount tree location protections kind removed query ≤
            DuplicatePrefixResidualSupportAuthorization.residualCount tree location protections kind removed root
          rw [DuplicatePrefixResidualCountModel.count_as_cardinality,DuplicatePrefixResidualCountModel.count_as_cardinality]
          exact GeneralBorrowExposureCardinality.cardinality_dominates _ _ _ _ kind covered
        simp only [show (rootPosition != 0) = true by simp [zero],ite_true] at equal
        omega
    have unequalBool : ((count root + if rootPosition != 0 then 1 else 0) == count query) = false :=
      Bool.eq_false_iff.mpr (fun same => unequal (beq_iff_eq.mp same))
    simp only [DuplicatePrefixCallbackAuthorization.classify,
      nonzero,unequalBool,Bool.false_eq_true,ite_false]
    cases DuplicatePrefixCallbackAuthorization.aboveMaximum node maximum <;> cases localZero : (count query == 0) <;> simp

def cutoff (pointer : PointerInstance) (selectedNode : TreeNode) : Option BorTag :=
  match pointer.value.provenance with | .wildcard => none | .concrete _ _ => some selectedNode.tag

def Callback (pointer : PointerInstance) (selected root : UniIndex) : Prop :=
  pointer.value.provenance = .wildcard ∨ root ≠ selected

/-- Data geometry for the EXACT uniform grant, not Authorization or an
operation-result table. Primary exposed support is conditional on an actual
callback: concrete Normal access in root0 needs no exposed-root assumption.
Nat masked counts here are independent of execution counter/fuel headroom. -/
structure Geometry {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode) where
  sourceNode : TreeNode
  sourceAt : W.allocation.extra.nodes.get W.pointer.grant = some sourceNode
  selectedPosition : Nat
  selectedRoot : UniIndex
  selectedNode : TreeNode
  selectedSlot : W.allocation.extra.roots[selectedPosition]? = some selectedRoot
  selectedAt : W.allocation.extra.nodes.get selectedRoot = some selectedNode
  selectedNone : selectedNode.parent = none
  sourcePath : Path W.allocation.extra selectedRoot W.pointer.grant
  grounded : Below W.precise.completion allocationRoot W.pointer.grant
  normalAncestry : ∀ query node,W.allocation.extra.nodes.get query = some node →
    Path W.allocation.extra selectedRoot query →
    (Below W.precise.completion query W.pointer.grant ↔ Path W.allocation.extra query W.pointer.grant)
  primarySupport : ∀ byte,Window id offset length byte → ∀ segment ∈ W.allocation.extra.locations.entries.toList,
    segment.range.start.toNat ≤ byte.2 → byte.2 < segment.range.stop.toNat → ∀ kind,
    Callback W.pointer selectedRoot allocationRoot →
    ∃ witness node,W.allocation.extra.nodes.get witness = some node ∧
      DuplicatePrefixCallbackAuthorization.Supports segment.data tracker.global.protectedTags witness node (cutoff W.pointer selectedNode) kind ∧
      Path W.allocation.extra allocationRoot witness ∧ Below W.precise.completion witness W.pointer.grant
  masked : ∀ byte,Window id offset length byte → ∀ segment ∈ W.allocation.extra.locations.entries.toList,
    segment.range.start.toNat ≤ byte.2 → byte.2 < segment.range.stop.toNat → ∀ kind position root,
    W.allocation.extra.roots[position]? = some root → Callback W.pointer selectedRoot root →
    ∀ query node,W.allocation.extra.nodes.get query = some node → Path W.allocation.extra root query →
    ∀ removed,DuplicatePrefixResidualSupportAuthorization.Removal W.allocation.extra segment.data tracker.global.protectedTags
      (cutoff W.pointer selectedNode) kind removed →
    let relation := DuplicatePrefixResidualSupportAuthorization.residualRelation W.allocation.extra segment.data tracker.global.protectedTags
      root query node (cutoff W.pointer selectedNode) kind position removed
    0 < DuplicatePrefixResidualSupportAuthorization.residualCount W.allocation.extra segment.data tracker.global.protectedTags kind removed root +
      (if position != 0 then 1 else 0) ∧
    (Below W.precise.completion query W.pointer.grant → relation = some .LocalAccess ∨ relation = some .EitherAccess) ∧
    (¬Below W.precise.completion query W.pointer.grant → relation = some .ForeignAccess ∨ relation = some .EitherAccess)

theorem geometry_selected {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (actual : ∀ segment ∈ W.allocation.extra.locations.entries.toList, ∀ index node,
      W.allocation.extra.nodes.get index = some node →
      Realized (RawState segment.data index node) (tracker.global.protectedTags.contains node.tag))
    (exclusive : demandOf mode = .exclusive) : Nonempty (Geometry W) := by
  obtain ⟨sourceNode,sourceAt,_,sourceBinding⟩ := W.binding
  obtain ⟨position,root,rootNode,rootSlot,rootAt,sourcePath⟩ :=
    CandidateCurrentWindowAuthority.root_path W.allocation.extra W.parents.graph W.pointer.grant sourceNode sourceAt
  obtain ⟨sameNode,sameAt,parentless⟩ := W.parents.graph.rootNodes root
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  have same := Option.some.inj (rootAt.symm.trans sameAt)
  subst sameNode
  have cap := W.issued.capability
  obtain ⟨zeroNode,zeroAt,zeroNone,_,_⟩ := cap.rootNode
  obtain ⟨depth⟩ := W.parents.graph.depth
  have origins : ∀ byte,Window id offset length byte → ∀ segment ∈ W.allocation.extra.locations.entries.toList,
      segment.range.start.toNat ≤ byte.2 → byte.2 < segment.range.stop.toNat → ∀ kind callback callbackNode,
      W.allocation.extra.nodes.get callback = some callbackNode → callbackNode.parent = none → ∀ query node,
      W.allocation.extra.nodes.get query = some node → Path W.allocation.extra callback query →
      Callback W.pointer root callback → Below W.precise.completion query W.pointer.grant →
      ∃ witness witnessNode,W.allocation.extra.nodes.get witness = some witnessNode ∧
        DuplicatePrefixCallbackAuthorization.Supports segment.data tracker.global.protectedTags witness witnessNode (cutoff W.pointer rootNode) kind ∧
        Path W.allocation.extra query witness ∧ Below W.precise.completion witness W.pointer.grant := by
    intro byte inside segment member lower upper kind callback callbackNode callbackAt callbackNone query node present path allowed below
    have embedding := (W.window byte inside).2 segment member lower upper
    have localRights : ∀ index found,W.allocation.extra.nodes.get index = some found →
        Below W.precise.completion index W.pointer.grant →
        LocalWrite (RawState segment.data index found) (tracker.global.protectedTags.contains found.tag) := by
      intro index found nodeAt ancestor
      have token := (embedding index found nodeAt).1 ancestor
      rw [exclusive] at token
      exact local_write _ _ (actual segment member index found nodeAt) (token_local _ _ token)
    by_cases selected : callback = root
    · subst callback
      have wildcard : W.pointer.value.provenance = .wildcard := by
        rcases allowed with wildcard | different
        · exact wildcard
        · exact False.elim (different rfl)
      have exposed : sourceNode.isExposed = true := by rw [wildcard] at sourceBinding;exact sourceBinding
      have physical := same_root_ancestor W.parents rootAt parentless present path sourcePath below
      refine ⟨W.pointer.grant,sourceNode,sourceAt,⟨exposed,local_support _ _ kind (localRights _ sourceNode sourceAt (.refl _)),?_⟩,
        physical,.refl _⟩
      simp [cutoff,wildcard]
    · obtain ⟨origin,originNode,originAt,exposed,originPath,_,originBelow,older⟩ :=
        W.parents.cross_root_origin callbackAt callbackNone rootAt parentless present selected path sourcePath below
      refine ⟨origin,originNode,originAt,⟨exposed,local_support _ _ kind (localRights _ originNode originAt originBelow),?_⟩,originPath,originBelow⟩
      cases provenance : W.pointer.value.provenance with
      | wildcard => simp [cutoff,provenance]
      | concrete alloc tag => simpa [cutoff,provenance] using older
  refine ⟨⟨sourceNode,sourceAt,position,root,rootNode,rootSlot,rootAt,parentless,sourcePath,W.root_below,?_,?_,?_⟩⟩
  · intro query node present path
    exact ⟨same_root_ancestor W.parents rootAt parentless present path sourcePath,
      W.parents.physical_below⟩
  · intro byte inside segment member lower upper kind allowed
    exact origins byte inside segment member lower upper kind allocationRoot zeroNode zeroAt zeroNone allocationRoot zeroNode zeroAt
      (.refl _ zeroNode zeroAt) allowed W.root_below
  · intro byte inside segment member lower upper kind callbackPosition callbackRoot callbackSlot allowed query node present path removed legal
    obtain ⟨callbackNode,callbackAt,callbackNone⟩ := W.parents.graph.rootNodes callbackRoot
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? callbackSlot))
    have grounded : callbackPosition = 0 → Below W.precise.completion callbackRoot W.pointer.grant := by
      intro zero
      have firstSlot : W.allocation.extra.roots[0]? = some callbackRoot := by simpa only [zero] using callbackSlot
      have equal : callbackRoot = allocationRoot := Option.some.inj (firstSlot.symm.trans cap.rootSlot)
      rw [equal]
      exact W.root_below
    exact masked_shape W.allocation.extra W.precise.completion segment.data tracker.global.protectedTags W.parents depth
      callbackPosition callbackRoot W.pointer.grant (cutoff W.pointer rootNode) kind
      (fun query node present path below => origins byte inside segment member lower upper kind callbackRoot callbackNode callbackAt callbackNone query node present path allowed below)
      callbackNode callbackAt grounded query node present path removed legal

theorem geometry {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (actual : ActualRealized (ActualWorld before) tracker.global.protectedTags)
    (exclusive : demandOf mode = .exclusive) : Nonempty (Geometry W) := by
  exact geometry_selected W (fun segment member index node present =>
    actual id W.allocation W.present segment member index node present) exclusive

/-- ONE current normalization: fixed whole-window owner witnesses first, then
masked-query geometry for THOSE SAME grants/parent choices. This does not
return Proposed/Ordinary, assume any successful callback, or add a history.
Current denotation adequacy and constructor/copy/GC transport remain OPEN.
Actual address/cache WindowBinding is already supplied by the input binding
clauses; cache/address formation is not derived from pure ownership here.
Empty source has no nonempty issuance or source-support requirement. -/
theorem normalize_current {before tracker argument len place call data}
    (D : CurrentDenotation before tracker argument len place call data)
    (runtime : DuplicatePrefixRuntimeInput.OrderedState before tracker) :
    ∃ ret : UniformWindow before tracker data call.returnOwner call.returnId call.returnOffset 1 .ret,
      Nonempty (Geometry ret) ∧ place.layout = RootCompilerFacts.boolLayout ∧
      place.mplace.ptr = ret.pointer.value.withOptionalProvenance ∧
      CandidateCallBindings.WindowBinding before ret.pointer.value call.returnId call.returnOffset 1 ∧
      OrdinaryPhysicalValidity.BoolDestination ret.allocation (UInt64.ofNat call.returnOffset) ∧
      (len = 0 ∨ ∃ source : UniformWindow before tracker data call.sourceOwner call.sourceId call.sourceOffset call.length .mut,
        Nonempty (Geometry source) ∧ argument = .pointer source.pointer.value ∧
        CandidateCallBindings.WindowBinding before source.pointer.value call.sourceId call.sourceOffset call.length ∧
        OrdinaryPhysicalValidity.MutU8Slice source.allocation (UInt64.ofNat call.sourceOffset) len ∧
        (call.sourceId = call.returnId → source.precise = ret.precise)) ∧
      (∀ byte,Window call.sourceId call.sourceOffset call.length byte → Window call.returnId call.returnOffset 1 byte → False) := by
  have actual := CandidateCurrentGrantRuntime.actual_state before tracker runtime.toState
  obtain ⟨ret⟩ := uniform_window D call.returnOwner call.returnId call.returnOffset 1 .ret (by omega)
    (fun byte inside => (D.claims.2.2 byte).mpr inside)
  have retGeometry := geometry ret actual (by rfl)
  rcases D.returnBinding with ⟨layout,pointer,placeEq,boundLoan,boundPointer,loanAt,pointerAt,valueEq,_,window⟩
  have loanEq := Option.some.inj (loanAt.symm.trans ret.loanAt)
  subst boundLoan
  have pointerEq := Option.some.inj (pointerAt.symm.trans ret.pointerAt)
  subst boundPointer
  have placeExact : place.mplace.ptr = ret.pointer.value.withOptionalProvenance := by rw [valueEq];exact placeEq
  have retWindow : CandidateCallBindings.WindowBinding before ret.pointer.value call.returnId call.returnOffset 1 := by
    rw [valueEq];exact window
  obtain ⟨returnAllocation,returnAt,returnValue⟩ := D.returnStorage
  have returnEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList D.worldIds call.returnId
    returnAllocation ret.allocation returnAt ret.present
  subst returnAllocation
  refine ⟨ret,retGeometry,layout,placeExact,retWindow,returnValue,?_,?_⟩
  · by_cases empty : len = 0
    · exact .inl empty
    · have positive : 0 < call.length := by
        rw [D.length]
        exact Nat.pos_of_ne_zero (fun zero => empty (UInt64.toNat_inj.mp zero))
      obtain ⟨source⟩ := uniform_window D call.sourceOwner call.sourceId call.sourceOffset call.length .mut positive
        (fun byte inside => (D.claims.2.1 byte).mpr inside)
      have sourceGeometry := geometry source actual (by rfl)
      rcases D.sourceBinding with emptyBinding | ⟨_,bits,argumentEq,sourceLoan,sourcePointer,sourceLoanAt,sourcePointerAt,sourceValue,_,sourceWindow⟩
      · exact False.elim (empty emptyBinding.1)
      · have loanEq := Option.some.inj (sourceLoanAt.symm.trans source.loanAt)
        subst sourceLoan
        have pointerEq := Option.some.inj (sourcePointerAt.symm.trans source.pointerAt)
        subst sourcePointer
        have argumentExact : argument = .pointer source.pointer.value := by rw [sourceValue];exact argumentEq
        have normalized : CandidateCallBindings.WindowBinding before source.pointer.value call.sourceId call.sourceOffset call.length := by
          rw [sourceValue];exact sourceWindow
        obtain ⟨sourceAllocation,sourceAt,physical⟩ := D.sourceStorage empty
        have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList D.worldIds call.sourceId
          sourceAllocation source.allocation sourceAt source.present
        subst sourceAllocation
        refine .inr ⟨source,sourceGeometry,argumentExact,normalized,physical,?_⟩
        intro sameId
        apply CandidateCurrentUniformOwnerWindow.same_id data.interpretation.precise.toList D.interpretationIds call.returnId
        · simpa only [sameId] using source.preciseAt
        · exact ret.preciseAt
  · intro byte sourceWindow returnWindow
    exact CandidateCurrentJointCall.source_return_disjoint data.interpretation call D.contents D.claims byte sourceWindow returnWindow

end
end DuplicatePrefix.CurrentCallResourceNormalization

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceNormalization.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current normalization dependency {dependency}"
