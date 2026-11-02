import duplicate_prefix.CurrentCallResourceNormalization

/-! Candidate current support chains. These laws do not adopt an Ordinary
entitlement predicate or reconstruct pointer/copy families. -/
namespace DuplicatePrefix.CurrentCallSupportChain
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

structure Link (tree : BorrowTree) (origin grant : UniIndex) where
  originRoot : UniIndex
  root : UniIndex
  originNode : TreeNode
  rootNode : TreeNode
  earlier : Nat
  position : Nat
  originAt : tree.nodes.get origin=some originNode
  exposed : originNode.isExposed=true
  rootAt : tree.nodes.get root=some rootNode
  parentless : rootNode.parent=none
  older : originNode.tag.value<rootNode.tag.value
  before : earlier<position
  earlierSlot : tree.roots[earlier]?=some originRoot
  rootSlot : tree.roots[position]?=some root
  originPath : Path tree originRoot origin
  path : Path tree root grant

inductive Chain (tree : BorrowTree) : UniIndex → Type
  | root {grant} (path : Path tree allocationRoot grant) : Chain tree grant
  | link {origin grant} (prior : Chain tree origin) (edge : Link tree origin grant) : Chain tree grant

namespace Chain
variable {tree : BorrowTree} {grant : UniIndex}

def Member : {grant : UniIndex} → Chain tree grant → UniIndex → Prop
  | terminal,.root _,index => Path tree index terminal
  | terminal,.link prior _,index => Member prior index ∨ Path tree index terminal

def virtualParent : {grant : UniIndex} → Chain tree grant → UniIndex → Option UniIndex
  | _,.root _,_ => none
  | _,@Chain.link _ origin _ prior edge,index =>
      match virtualParent prior index with
      | some parent => some parent
      | none => if index=edge.root then some origin else none

theorem terminal (chain : Chain tree grant) : ∃ node,tree.nodes.get grant=some node := by
  cases chain with
  | root path => exact path.present
  | link prior edge => exact edge.path.present

theorem self_member (chain : Chain tree grant) : Member chain grant := by
  obtain ⟨node,present⟩:=terminal chain
  cases chain with
  | root => exact .refl _ node present
  | link => exact .inr (.refl _ node present)

theorem root_member (chain : Chain tree grant) : Member chain allocationRoot := by
  induction chain with
  | root path => exact path
  | link prior edge ih => exact .inl ih

private theorem path_start {first last : UniIndex} (path : Path tree first last) : ∃ node,tree.nodes.get first=some node := by
  induction path with
  | refl node found => exact ⟨node,found⟩
  | step earlier node found edge ih => exact ih

theorem member_live (chain : Chain tree grant) {index : UniIndex} (member : Member chain index) :
    ∃ node,tree.nodes.get index=some node := by
  induction chain with
  | root path => exact path_start member
  | link prior edge ih =>
    rcases member with old | path
    · exact ih old
    · exact path_start path

theorem member_tag_le (order : ParentTagOrder tree) (chain : Chain tree grant)
    {index : UniIndex} {node terminalNode : TreeNode} (present : tree.nodes.get index=some node)
    (terminalAt : tree.nodes.get grant=some terminalNode) (member : Member chain index) :
    node.tag.value≤terminalNode.tag.value := by
  induction chain generalizing index node terminalNode with
  | root path => exact path_tag_le tree order _ _ member _ _ present terminalAt
  | link prior edge ih =>
    rcases member with old | path
    · have first:=ih present edge.originAt old
      have last:=path_tag_le tree order _ _ edge.path _ _ edge.rootAt terminalAt
      exact Nat.le_trans first (Nat.le_trans (Nat.le_of_lt edge.older) last)
    · exact path_tag_le tree order _ _ path _ _ present terminalAt

theorem root_ne (order : ParentTagOrder tree) {origin : UniIndex} (prior : Chain tree origin)
    (edge : Link tree origin grant) : edge.root≠allocationRoot := by
  intro same
  obtain ⟨node,present⟩:=member_live prior (root_member prior)
  have edgeAtRoot : tree.nodes.get allocationRoot=some edge.rootNode := by rw [←same];exact edge.rootAt
  have equal : node=edge.rootNode := Option.some.inj (present.symm.trans edgeAtRoot)
  have bounded:=member_tag_le order prior present edge.originAt (root_member prior)
  rw [equal] at bounded
  exact Nat.not_lt_of_ge bounded edge.older

theorem virtual_domain (chain : Chain tree grant) {index parent : UniIndex}
    (found : virtualParent chain index=some parent) : Member chain index := by
  induction chain generalizing parent with
  | root path => cases found
  | link prior edge ih =>
    change (match virtualParent prior index with | some parent=>some parent | none=>if index=edge.root then some _ else none)=some parent at found
    cases old : virtualParent prior index with
    | some previous =>
      rw [old] at found
      cases found
      exact .inl (ih old)
    | none =>
      rw [old] at found
      by_cases same : index=edge.root
      · rw [ite_eq_left same] at found
        subst index
        exact .inr edge.path
      · rw [ite_eq_right same] at found
        cases found

theorem virtual_origin (chain : Chain tree grant) {index parent : UniIndex}
    (found : virtualParent chain index=some parent) : Member chain parent := by
  induction chain generalizing parent with
  | root path => cases found
  | link prior edge ih =>
    change (match virtualParent prior index with | some parent=>some parent | none=>if index=edge.root then some _ else none)=some parent at found
    cases old : virtualParent prior index with
    | some previous =>
      rw [old] at found
      cases found
      exact .inl (ih old)
    | none =>
      rw [old] at found
      by_cases same : index=edge.root
      · rw [ite_eq_left same] at found
        cases found
        exact .inl (self_member prior)
      · rw [ite_eq_right same] at found
        cases found

theorem virtual_sound (chain : Chain tree grant) {index parent : UniIndex}
    (found : virtualParent chain index=some parent) :
    ∃ (earlier position : Nat) (originRoot : UniIndex) (childNode originNode : TreeNode),
      earlier<position ∧ tree.roots[earlier]?=some originRoot ∧ tree.roots[position]?=some index ∧
      tree.nodes.get index=some childNode ∧ childNode.parent=none ∧
      tree.nodes.get parent=some originNode ∧ originNode.isExposed=true ∧ originNode.tag.value<childNode.tag.value ∧
      Path tree originRoot parent := by
  induction chain generalizing parent with
  | root path => cases found
  | link prior edge ih =>
    change (match virtualParent prior index with | some parent=>some parent | none=>if index=edge.root then some _ else none)=some parent at found
    cases old : virtualParent prior index with
    | some previous => rw [old] at found;cases found;exact ih old
    | none =>
      rw [old] at found
      by_cases same : index=edge.root
      · rw [ite_eq_left same] at found
        subst index
        cases found
        exact ⟨edge.earlier,edge.position,edge.originRoot,edge.rootNode,edge.originNode,edge.before,edge.earlierSlot,edge.rootSlot,
          edge.rootAt,edge.parentless,edge.originAt,edge.exposed,edge.older,edge.originPath⟩
      · rw [ite_eq_right same] at found
        cases found

theorem fresh_root (order : ParentTagOrder tree) {origin : UniIndex} (prior : Chain tree origin)
    (edge : Link tree origin grant) : virtualParent prior edge.root=none := by
  cases found : virtualParent prior edge.root with
  | none => rfl
  | some previous =>
    have bounded:=member_tag_le order prior edge.rootAt edge.originAt (virtual_domain prior found)
    exact False.elim (Nat.not_lt_of_ge bounded edge.older)

theorem virtual_root_none (order : ParentTagOrder tree) (chain : Chain tree grant) : virtualParent chain allocationRoot=none := by
  induction chain with
  | root => rfl
  | link prior edge ih => simp only [virtualParent,ih,ite_eq_right (Ne.symm (root_ne order prior edge))]

def completion (chain : Chain tree grant) : Completion where
  parents:=Array.ofFn (fun i : Fin tree.nodes.data.size =>
    (tree.nodes.get ⟨UInt32.ofNat i.val⟩).bind (fun node=>match node.parent with
      | some parent=>some parent
      | none=>virtualParent chain ⟨UInt32.ofNat i.val⟩))
  depths:=Array.replicate tree.nodes.data.size 0

theorem parents_at (chain : Chain tree grant) (index : UniIndex) (valid : index.toNat<tree.nodes.data.size) :
    (completion chain).parents[index.toNat]?=some ((tree.nodes.get index).bind (fun node=>match node.parent with
      | some parent=>some parent
      | none=>virtualParent chain index)) := by
  have equal : (⟨UInt32.ofNat index.toNat⟩ : UniIndex)=index := by
    cases index
    simp only [UniIndex.toNat,UInt32.ofNat_toNat]
  simp only [completion,Array.getElem?_ofFn,valid,↓reduceDIte,equal]

theorem virtual_at (chain : Chain tree grant) {index parent : UniIndex}
    (found : virtualParent chain index=some parent) :
    (completion chain).parents[index.toNat]?=some (some parent) := by
  obtain ⟨_,_,_,node,_,_,_,_,present,parentless,_,_,_,_⟩:=virtual_sound chain found
  rw [parents_at chain index (GeneralBorrowNodeUpdate.lookup_valid _ _ _ present)]
  simp only [present,Option.bind_some,parentless,found]

theorem physical_at (chain : Chain tree grant) {index parent : UniIndex} {node : TreeNode}
    (present : tree.nodes.get index=some node) (edge : node.parent=some parent) :
    (completion chain).parents[index.toNat]?=some (some parent) := by
  rw [parents_at chain index (GeneralBorrowNodeUpdate.lookup_valid _ _ _ present)]
  simp only [present,Option.bind_some,edge]

theorem parents (chain : Chain tree grant)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree) (order : ParentTagOrder tree)
    (distinct : tree.roots.toList.Nodup) (rootNode : TreeNode)
    (rootAt : tree.nodes.get allocationRoot=some rootNode) (rootNone : rootNode.parent=none) :
    ParentInterpretation tree (completion chain) := by
  refine ⟨graph,order,by simp only [completion,Array.size_ofFn],?_,?_,?_,?_⟩
  · intro index node present parent edge
    exact physical_at chain present edge
  · intro child parent edge
    have valid : child.toNat<tree.nodes.data.size := by
      have bound:=(Array.getElem?_eq_some_iff.mp edge).1
      simpa only [completion,Array.size_ofFn] using bound
    rw [parents_at chain child valid] at edge
    cases present : tree.nodes.get child with
    | none => simp only [present,Option.bind_none] at edge;cases edge
    | some node =>
      simp only [present,Option.bind_some] at edge
      cases physical : node.parent with
      | some actual =>
        simp only [physical,Option.some.injEq] at edge
        subst actual
        obtain ⟨depth⟩:=graph.depth
        obtain ⟨parentNode,parentAt,_⟩:=depth.parent child node present parent physical
        exact ⟨⟨node,rfl⟩,⟨parentNode,parentAt⟩⟩
      | none =>
        simp only [physical,Option.some.injEq] at edge
        obtain ⟨_,_,_,_,origin,_,_,_,_,_,originAt,_,_,_⟩:=virtual_sound chain edge
        exact ⟨⟨node,rfl⟩,⟨origin,originAt⟩⟩
  · rw [parents_at chain allocationRoot (GeneralBorrowNodeUpdate.lookup_valid _ _ _ rootAt)]
    simp only [rootAt,Option.bind_some,rootNone,virtual_root_none order chain]
  · intro position root slot origin edge
    obtain ⟨node,present,parentless⟩:=graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
    rw [parents_at chain root (GeneralBorrowNodeUpdate.lookup_valid _ _ _ present)] at edge
    simp only [present,Option.bind_some,parentless,Option.some.injEq] at edge
    obtain ⟨earlier,chosen,originRoot,rootNode,originNode,before,originSlot,rootSlot,rootHere,_,originHere,exposed,older,path⟩:=virtual_sound chain edge
    have chosenEq : chosen=position := distinct.eq_of_getElem?_eq
      (by simpa only [Array.length_toList] using (Array.getElem?_eq_some_iff.mp rootSlot).1)
      (by simpa only [Array.getElem?_toList] using rootSlot.trans slot.symm)
    subst chosen
    exact ⟨earlier,originRoot,rootNode,originNode,before,originSlot,rootHere,originHere,exposed,older,path⟩

theorem member_parent (chain : Chain tree grant) {child parent : UniIndex} {node : TreeNode}
    (present : tree.nodes.get child=some node) (edge : node.parent=some parent)
    (parentAt : ∃ parentNode,tree.nodes.get parent=some parentNode) (member : Member chain child) : Member chain parent := by
  obtain ⟨parentNode,parentAt⟩:=parentAt
  have path : Path tree parent child:=.step (.refl _ parentNode parentAt) node present edge
  induction chain with
  | root source => exact CompletedBorrowAncestry.path_trans path member
  | link prior edge ih =>
    rcases member with old | last
    · exact .inl (ih old)
    · exact .inr (CompletedBorrowAncestry.path_trans path last)

theorem member_closed (chain : Chain tree grant) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    {child parent : UniIndex} (edge : (completion chain).parents[child.toNat]?=some (some parent))
    (member : Member chain child) : Member chain parent := by
  have valid : child.toNat<tree.nodes.data.size := by
    have bound:=(Array.getElem?_eq_some_iff.mp edge).1
    simpa only [completion,Array.size_ofFn] using bound
  rw [parents_at chain child valid] at edge
  cases present : tree.nodes.get child with
  | none => simp only [present,Option.bind_none] at edge;cases edge
  | some node =>
    simp only [present,Option.bind_some] at edge
    cases physical : node.parent with
    | some actual =>
      simp only [physical,Option.some.injEq] at edge
      subst actual
      obtain ⟨depth⟩:=graph.depth
      obtain ⟨parentNode,parentAt,_⟩:=depth.parent child node present parent physical
      exact member_parent chain present physical ⟨parentNode,parentAt⟩ member
    | none =>
      simp only [physical,Option.some.injEq] at edge
      exact virtual_origin chain edge

theorem below_member (chain : Chain tree grant) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    {index : UniIndex} (below : Below (completion chain) index grant) : Member chain index := by
  have closed : ∀ {first last},Below (completion chain) first last → Member chain last → Member chain first := by
    intro first last path
    induction path with
    | refl => exact fun h=>h
    | step edge earlier ih => exact fun member=>ih (member_closed chain graph edge member)
  exact closed below (self_member chain)

/-- Any interpretation retaining the chain's physical and selected virtual
edges contains its complete support; no other virtual edge is required. -/
theorem member_below (chain : Chain tree grant) (order : ParentTagOrder tree) (C : Completion)
    (physical : ∀ index node,tree.nodes.get index=some node → ∀ parent,node.parent=some parent → C.parents[index.toNat]?=some (some parent))
    (virtual : ∀ index parent,virtualParent chain index=some parent → C.parents[index.toNat]?=some (some parent))
    {index : UniIndex} (member : Member chain index) : Below C index grant := by
  have physicalPath : ∀ {first last},Path tree first last → Below C first last := by
    intro first last path
    induction path with
    | refl => exact .refl _
    | step earlier node found edge ih => exact .step (physical _ node found _ edge) ih
  induction chain with
  | root path => exact physicalPath member
  | @link origin terminal prior edge ih =>
    have priorVirtual : ∀ index parent,virtualParent prior index=some parent → C.parents[index.toNat]?=some (some parent) := by
      intro index parent found
      apply virtual index parent
      simp only [virtualParent,found]
    have rootEdge : C.parents[edge.root.toNat]?=some (some origin) := by
      apply virtual edge.root origin
      simp only [virtualParent,fresh_root order prior edge,↓reduceIte]
    rcases member with previous | path
    · have before:=ih priorVirtual previous
      have toRoot : Below C origin edge.root:=.step rootEdge (.refl _)
      exact CompletedBorrowAncestry.below_trans before (CompletedBorrowAncestry.below_trans toRoot (physicalPath edge.path))
    · exact physicalPath path

theorem below_iff_member (chain : Chain tree grant) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (order : ParentTagOrder tree) {index : UniIndex} : Below (completion chain) index grant ↔ Member chain index :=
  ⟨below_member chain graph,member_below chain order (completion chain) (fun _ _ found _ edge=>physical_at chain found edge) (fun _ _ found=>virtual_at chain found)⟩

theorem issued {before tracker id allocation} (cap : AllocationCapability before tracker id allocation)
    (chain : Chain allocation.extra grant) (order : ParentTagOrder allocation.extra) :
    SpatialDelegation before tracker id allocation (completion chain) grant := by
  have general : ∀ {terminal} (prior : Chain allocation.extra terminal) (C : Completion),
      (∀ index parent,virtualParent prior index=some parent → C.parents[index.toNat]?=some (some parent)) →
      SpatialDelegation before tracker id allocation C terminal := by
    intro terminal prior
    induction prior with
    | root path => intro C virtual;exact .concrete (.allocated cap) path
    | @link origin terminal prior edge ih =>
      intro C virtual
      have inherited : ∀ index parent,virtualParent prior index=some parent → C.parents[index.toNat]?=some (some parent) := by
        intro index parent found;apply virtual index parent;simp only [virtualParent,found]
      have originIssued:=ih C inherited
      have rootEdge : C.parents[edge.root.toNat]?=some (some origin) := by
        apply virtual edge.root origin
        simp only [virtualParent,fresh_root order prior edge,↓reduceIte]
      exact .concrete (.wildcard edge.originNode edge.rootNode edge.earlier edge.position edge.originRoot originIssued edge.originAt edge.exposed edge.rootAt edge.parentless edge.older edge.before edge.earlierSlot edge.rootSlot edge.originPath rootEdge) edge.path
  exact general chain (completion chain) (fun _ _ found=>virtual_at chain found)


/-- Literal parent lookup: every nonphysical edge is one of the chain's
actual older-exposed-origin choices, and both endpoints lie on its support. -/
theorem edge_kind (chain : Chain tree grant) {child parent : UniIndex}
    (edge : (completion chain).parents[child.toNat]?=some (some parent)) :
    ∃ node,tree.nodes.get child=some node ∧
      (node.parent=some parent ∨ (node.parent=none ∧ virtualParent chain child=some parent ∧ Member chain child ∧ Member chain parent)) := by
  have valid : child.toNat<tree.nodes.data.size := by
    have bound:=(Array.getElem?_eq_some_iff.mp edge).1
    simpa only [completion,Array.size_ofFn] using bound
  rw [parents_at chain child valid] at edge
  cases present : tree.nodes.get child with
  | none => simp only [present,Option.bind_none] at edge;cases edge
  | some node =>
    simp only [present,Option.bind_some] at edge
    refine ⟨node,rfl,?_⟩
    cases physical : node.parent with
    | some actual =>
      simp only [physical,Option.some.injEq] at edge
      subst actual
      exact .inl rfl
    | none =>
      simp only [physical,Option.some.injEq] at edge
      exact .inr ⟨rfl,edge,virtual_domain chain edge,virtual_origin chain edge⟩

/-- Appending actual physical descendants changes no chosen virtual link. -/
def append {terminal : UniIndex} (chain : Chain tree grant) (path : Path tree grant terminal) : Chain tree terminal :=
  match chain with
  | .root previous=>.root (CompletedBorrowAncestry.path_trans previous path)
  | .link prior edge=>.link prior
      ⟨edge.originRoot,edge.root,edge.originNode,edge.rootNode,edge.earlier,edge.position,edge.originAt,edge.exposed,
        edge.rootAt,edge.parentless,edge.older,edge.before,edge.earlierSlot,edge.rootSlot,edge.originPath,
        CompletedBorrowAncestry.path_trans edge.path path⟩

/-- Structural reverse extraction only. This does not supply current token or
protector entitlements, or adopt an Ordinary input domain. -/
theorem of_issued {before tracker id allocation C}
    (issued : SpatialDelegation before tracker id allocation C grant) : Nonempty (Chain allocation.extra grant) := by
  induction issued with
  | allocated cap =>
    obtain ⟨node,present,_,_,_⟩:=cap.rootNode
    exact ⟨.root (.refl _ node present)⟩
  | concrete issued path ih =>
    obtain ⟨chain⟩:=ih
    exact ⟨append chain path⟩
  | @wildcard origin root originNode rootNode earlier position originRoot issued originAt exposed rootAt parentless older before originSlot rootSlot path edge ih =>
    obtain ⟨chain⟩:=ih
    exact ⟨.link chain ⟨originRoot,root,originNode,rootNode,earlier,position,originAt,exposed,rootAt,parentless,older,before,originSlot,rootSlot,path,.refl _ rootNode rootAt⟩⟩


end Chain
/-- Pointwise current token support and automatically decoded retained-guard
obligations, independent of any Completion. Copy/family identity stays outside
this per-byte chain; the actual pointer binding is supplied unchanged. -/
def Carries (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    {grant : UniIndex} (chain : Chain allocation.extra grant) (byte : Nat) (demand : Demand) : Prop :=
  ∀ segment∈allocation.extra.locations.entries.toList,
    segment.range.start.toNat≤byte → byte<segment.range.stop.toNat →
    ∀ index node,allocation.extra.nodes.get index=some node →
      (chain.Member index → demand∈tokens (denote (RawState segment.data index node) (held.contains node.tag))) ∧
      (Clash (guard (denote (RawState segment.data index node) (held.contains node.tag))) demand → chain.Member index)

theorem embeds {allocation : Allocation Provenance BorrowTree} {held : ProtectedTags} {grant : UniIndex}
    (chain : Chain allocation.extra grant) (graph : GeneralBorrowStructuralHistoryState.GraphState allocation.extra)
    (order : ParentTagOrder allocation.extra) {byte : Nat} {demand : Demand}
    (support : Carries allocation held chain byte demand) : Embeds allocation held chain.completion grant byte demand := by
  intro segment member lower upper index node present
  have current:=support segment member lower upper index node present
  exact ⟨fun below=>current.1 ((chain.below_iff_member graph order).mp below),
    fun clash=>(chain.below_iff_member graph order).mpr (current.2 clash)⟩

/-- Candidate support-chain adequacy at one byte. The ONE actual family value,
allocation and slot remain external to the byte's chosen chain/grant. This law
asserts neither Ordinary adoption nor coverage of runtime program copies. -/
theorem adequate {before tracker id allocation}
    (cap : AllocationCapability before tracker id allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global)
    (order : ParentTagOrder allocation.extra) (distinct : allocation.extra.roots.toList.Nodup)
    (pointer : PointerInstance) (_pointerId : pointer.allocation=id) (binding : PointerBinds allocation pointer)
    (chain : Chain allocation.extra pointer.grant) (byte : Nat) (demand : Demand)
    (support : Carries allocation tracker.global.protectedTags chain byte demand) :
    ∃ C,ParentInterpretation allocation.extra C ∧ PointerBinds allocation pointer ∧
      SpatialDelegation before tracker id allocation C pointer.grant ∧
      Embeds allocation tracker.global.protectedTags C pointer.grant byte demand := by
  obtain ⟨rootNode,rootAt,rootNone,_,_⟩:=cap.rootNode
  exact ⟨chain.completion,chain.parents runtime.formed.toGraphState order distinct rootNode rootAt rootNone,
    binding,chain.issued cap order,embeds chain runtime.formed.toGraphState order support⟩


end
end DuplicatePrefix.CurrentCallSupportChain
