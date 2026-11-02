import empty_function.Preservation
import empty_function.TreeRuntimeInput

/-! Observable old-node rights of the concrete zero-child constructor. -/
namespace EmptyFunction.ConcreteRights
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree.ZeroProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] UniValMap.insert UniValMap.get BorrowTree.newChild

private theorem fallback (left right : Option LocationState) (leftDefault rightDefault : LocationState)
    (same : left.map View.stateShape = right.map View.stateShape)
    (defaults : View.stateShape leftDefault = View.stateShape rightDefault) :
    View.stateShape (left.getD leftDefault) = View.stateShape (right.getD rightDefault) := by
  cases left <;> cases right <;> simp_all

 theorem of_shape (before after : BorrowTree) (same : View.treeShape after = View.treeShape before) :
    Preservation.OldNodeRights before after := by
  have mapping : after.tagMapping = before.tagMapping := congrArg Prod.fst same
  have roots : after.roots = before.roots := congrArg (fun value => value.2.2.2) same
  have nodes := congrArg (fun value => value.2.1) same
  have locations := congrArg (fun value => value.2.2.1) same
  change after.nodes.data.map (Option.map View.nodeShape) = before.nodes.data.map (Option.map View.nodeShape) at nodes
  change after.locations.entries.map (fun segment => (segment.range,View.locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,View.locationShape segment.data)) at locations
  refine ⟨?_,?_,?_⟩
  · intro tag index tagged
    rw [mapping]
    exact tagged
  · intro root member
    rw [roots]
    exact member
  · intro index old present
    have lookup := congrArg (fun data => (data[index.toNat]?).getD none) nodes
    rw [View.mapped_lookup,View.mapped_lookup,present] at lookup
    cases currentAt : after.nodes.get index with
    | none => simp [currentAt] at lookup
    | some current =>
      have shape : View.nodeShape current = View.nodeShape old := by simpa only [currentAt,Option.map_some,Option.some.injEq] using lookup
      have tag : current.tag = old.tag := congrArg Prod.fst shape
      have parent : current.parent = old.parent := congrArg (fun value => value.2.1) shape
      have children : current.children = old.children := congrArg (fun value => value.2.2.1) shape
      have permission : current.defaultInitialPermission = old.defaultInitialPermission :=
        congrArg (fun value => value.2.2.2.1) shape
      have exposed : current.isExposed = old.isExposed := congrArg (fun value => value.2.2.2.2) shape
      have defaults : View.stateShape current.defaultLocationState = View.stateShape old.defaultLocationState := by
        simp [View.stateShape,TreeNode.defaultLocationState,permission]
      refine ⟨current,rfl,tag,parent,exposed,?_,?_,?_,?_⟩
      · exact congrArg Prod.fst defaults
      · exact congrArg Prod.snd defaults
      · intro child member
        rw [children]
        exact member
      · intro byte segment member contains
        obtain ⟨position,beforeValid,equal⟩ := Array.mem_iff_getElem.mp member
        subst segment
        have sizes := congrArg Array.size locations
        simp only [Array.size_map] at sizes
        have afterValid : position < after.locations.entries.size := by omega
        have pair := congrArg (fun entries => entries[position]?) locations
        simp only [Array.getElem?_map,Array.getElem?_eq_getElem afterValid,
          Array.getElem?_eq_getElem beforeValid,Option.map_some] at pair
        have pairEq := Option.some.inj pair
        have range : (after.locations.entries[position]'afterValid).range =
            (before.locations.entries[position]'beforeValid).range := congrArg Prod.fst pairEq
        have perms : View.locationShape (after.locations.entries[position]'afterValid).data =
            View.locationShape (before.locations.entries[position]'beforeValid).data := congrArg Prod.snd pairEq
        simp only [View.locationShape] at perms
        refine ⟨after.locations.entries[position],Array.getElem_mem afterValid,?_,?_,?_⟩
        · simpa only [Preservation.ContainsByte,range] using contains
        · have state := congrArg (fun data => (data[index.toNat]?).getD none) perms
          rw [View.mapped_lookup,View.mapped_lookup] at state
          exact congrArg Prod.fst (fallback _ _ _ _ state defaults)
        · have state := congrArg (fun data => (data[index.toNat]?).getD none) perms
          rw [View.mapped_lookup,View.mapped_lookup] at state
          exact congrArg Prod.snd (fallback _ _ _ _ state defaults)

private theorem trans (first middle last : BorrowTree)
    (left : Preservation.OldNodeRights first middle) (right : Preservation.OldNodeRights middle last) :
    Preservation.OldNodeRights first last := by
  refine ⟨fun tag index found => right.1 tag index (left.1 tag index found),
    fun root member => right.2.1 root (left.2.1 root member),?_⟩
  intro index old present
  obtain ⟨mid,midAt,tag1,parent1,exposed1,permission1,accessed1,children1,locations1⟩ := left.2.2 index old present
  obtain ⟨final,finalAt,tag2,parent2,exposed2,permission2,accessed2,children2,locations2⟩ := right.2.2 index mid midAt
  refine ⟨final,finalAt,tag2.trans tag1,parent2.trans parent1,exposed2.trans exposed1,
    permission2.trans permission1,accessed2.trans accessed1,
    fun child member => children2 child (children1 child member),?_⟩
  intro byte segment member contains
  obtain ⟨next,nextAt,nextContains,permission1,accessed1⟩ := locations1 byte segment member contains
  obtain ⟨finalSegment,finalAt,finalContains,permission2,accessed2⟩ := locations2 byte next nextAt nextContains
  exact ⟨finalSegment,finalAt,finalContains,permission2.trans permission1,accessed2.trans accessed1⟩

private theorem inserted_mapping (tree : BorrowTree) (tag : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index) :
    mapping.mapping = (tree.tagMapping.mapping.filter (fun row => row.1 != tag)).push (tag,index) := by
  cases available : tree.tagMapping.deassigned.back? with
  | some free =>
    simp [UniKeyMap.insert,available,fresh] at inserted
    rcases inserted with ⟨rfl,rfl⟩
    rfl
  | none =>
    cases generated : UniIndex.ofNat? tree.tagMapping.mapping.size with
    | none => simp [UniKeyMap.insert,available,generated] at inserted
    | some free =>
      simp [UniKeyMap.insert,available,generated,fresh] at inserted
      rcases inserted with ⟨rfl,rfl⟩
      rfl

private theorem mapping_old (tree : BorrowTree) (tag : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (oldTag : BorTag) (oldIndex : UniIndex) (old : tree.tagMapping.get oldTag = some oldIndex) :
    mapping.get oldTag = some oldIndex := by
  have different : tag ≠ oldTag := by intro same; subst oldTag; rw [fresh] at old; contradiction
  have filter : tree.tagMapping.mapping.filter (fun row => row.1 != tag) = tree.tagMapping.mapping := by
    apply Array.filter_eq_self.mpr
    intro row member
    have noFind : tree.tagMapping.mapping.find? (fun row => row.1 == tag) = none := by
      unfold UniKeyMap.get at fresh
      cases found : tree.tagMapping.mapping.find? (fun row => row.1 == tag) with
      | none => rfl
      | some foundRow => simp [found] at fresh
    have noMatch := Array.find?_eq_none.mp noFind row member
    simpa only [Bool.not_eq_true,beq_iff_eq,bne_iff_ne] using noMatch
  have data := inserted_mapping tree tag mapping index fresh inserted
  unfold UniKeyMap.get
  rw [data,filter]
  simpa [UniKeyMap.get,Array.find?_push,different] using old

private theorem staged (tree : BorrowTree) (tag : BorTag) (index parent : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (present : tree.nodes.get parent = some parentNode) (vacant : tree.nodes.get index = none) :
    let node : TreeNode := {
      tag := tag
      parent := some parent
      children := #[]
      defaultInitialPermission := .ReservedFrz false
      defaultInitialSifa := .None
      isExposed := false}
    let after : BorrowTree := {tree with
      tagMapping := mapping
      nodes := Append.attachedNodes tree.nodes index parent parentNode node}
    Preservation.OldNodeRights tree after := by
  dsimp only
  refine ⟨fun oldTag oldIndex old => mapping_old tree tag mapping index fresh inserted oldTag oldIndex old,
    fun root member => member,?_⟩
  intro query old oldAt
  have notFresh : query ≠ index := by intro same; subst query; rw [vacant] at oldAt; contradiction
  by_cases same : query = parent
  · subst query
    have oldEq : old = parentNode := by rw [present] at oldAt; exact (Option.some.inj oldAt).symm
    subst old
    refine ⟨{parentNode with children := parentNode.children.push index},?_,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · unfold Append.attachedNodes
      exact Sparse.get_same _ parent {parentNode with children := parentNode.children.push index}
    · intro child member
      exact Array.mem_push_of_mem index member
    · intro byte segment member contains
      exact ⟨segment,member,contains,rfl,rfl⟩
  · have oldStill : (Append.attachedNodes tree.nodes index parent parentNode
        ({tag := tag,parent := some parent,children := #[],defaultInitialPermission := .ReservedFrz false,
          defaultInitialSifa := .None,isExposed := false} : TreeNode)).get query = some old := by
      unfold Append.attachedNodes
      rw [Sparse.get_other _ parent query _ same,Sparse.get_other _ index query _ notFresh]
      exact oldAt
    refine ⟨old,oldStill,rfl,rfl,rfl,rfl,rfl,fun child member => member,?_⟩
    intro byte segment member contains
    exact ⟨segment,member,contains,rfl,rfl⟩

 theorem constructor (tree : BorrowTree) (tag : BorTag) (formed : TreeRuntimeInput.TreeFormed tree tag)
    (parentTag : BorTag) (parent : UniIndex) (tagged : tree.tagMapping.get parentTag = some parent)
    (room : tree.tagMapping.mapping.size ≤ 4294967295) (offset : Size) (initial : LocationState) :
    Preservation.OldNodeRights tree
      (tree.newChild offset (.concrete parentTag) tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
        (.ReservedFrz false) true).tree := by
  obtain ⟨parentNode,present⟩ := formed.parentPresent parentTag parent tagged
  obtain ⟨mapping,index,inserted,_,vacant⟩ := formed.allocate room
  have ctor := Release.concrete_zero_eq tree parentTag tag index parent parentNode mapping
    inserted tagged present vacant offset initial
  rw [ctor]
  dsimp only
  apply trans
  · exact staged tree tag index parent parentNode mapping formed.nextFresh inserted present vacant
  · apply of_shape
    exact View.preserves _ parent .None

end EmptyFunction.ConcreteRights

namespace EmptyFunction.ConcreteRights
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree.ZeroProtection
set_option autoImplicit false
/-- Successful allocator metadata, rather than an initial size reserve,
suffices for old-node rights of the actual concrete zero child. -/
theorem constructor_of_insert (tree : BorrowTree) (tag parentTag : BorTag)
    (parent : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag) (index : UniIndex)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (present : tree.nodes.get parent = some parentNode) (vacant : tree.nodes.get index = none)
    (offset : Size) (initial : LocationState) :
    Preservation.OldNodeRights tree
      (tree.newChild offset (.concrete parentTag) tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
        (.ReservedFrz false) true).tree := by
  rw [Release.concrete_zero_eq tree parentTag tag index parent parentNode mapping
    inserted tagged present vacant offset initial]
  dsimp only
  apply trans
  · exact staged tree tag index parent parentNode mapping fresh inserted present vacant
  · apply of_shape
    exact View.preserves _ parent .None
end EmptyFunction.ConcreteRights
