import duplicate_prefix.GeneralBorrowWildcardRootInstalled
import duplicate_prefix.GeneralBorrowExposedConcreteLast
namespace DuplicatePrefix.GeneralBorrowWildcardConstructorNextRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPositiveWildcardConstructor DuplicatePrefix.GeneralBorrowWildcardLeaf
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Profile (protections : ProtectedTags) (head : UniIndex) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (location : LocationTree) : Prop :=
  location.perms.get head = some unique ∧
  ∀ root ∈ extras, supports (effective location protections root (nodes root)) .Read = true

/-- A genuine positive protected wildcard-root constructor supplies the new
concrete root's next local Read. The old exposed references are processed by
Local/Either classification rather than a ForeignOwned hypothesis. Cache
coherence, new-row materialization, all root identities and tag cutoffs are
formed from initial graph, permission and allocator resources. -/
theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (protections : ProtectedTags) (head : UniIndex) (headNode : TreeNode) (extras : List UniIndex)
    (nodes : UniIndex → TreeNode) (tag : BorTag) (offset len : UInt64)
    (roots : tree.roots = (head::extras).toArray)
    (headPresent : tree.nodes.get head = some headNode) (headLeaf : headNode.children = #[])
    (headExposed : headNode.isExposed = true) (headBound : headNode.tag.value ≤ tag.value)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧ (nodes root).children = #[] ∧
      (nodes root).isExposed = true ∧ (nodes root).tag.value ≤ tag.value)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (short : tree.nodes.size+1 < 65536)
    (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (coherent : Every (fun location => LocationCoherent tree location protections) tree.locations)
    (profile : Every (Profile protections head extras nodes) tree.locations) :
    let inserted := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) ⟨.ReservedFrz false,true,.None⟩) (.ReservedFrz false) true
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    inserted.outcome = .ok () ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => ∀ range : ByteRange,
          source_access_status (source_tree_access_at inserted.tree location (some index) .Read protections .VisitChildrenOfAccessed range) = none ∧
          LocationCoherent inserted.tree (source_access_location
            (source_tree_access_at inserted.tree location (some index) .Read protections .VisitChildrenOfAccessed range)) protections)
        offset (offset+len) inserted.tree.locations := by
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let state : LocationState := ⟨.ReservedFrz false,true,.None⟩
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
  let after := result tree mapping index tag (.ReservedFrz false) .None state offset len
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    rw [aligned]
    change tree.nodes.data.size+1 < 65536 at short
    omega
  have atEnd : index.toNat = tree.nodes.data.size := by
    dsimp only [index,UniIndex.toNat]
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega),aligned]
  have vacant : tree.nodes.get index = none := by simp [UniValMap.get,atEnd]
  have size : (tree.nodes.insert index node).size = tree.nodes.size+1 :=
    GeneralBorrowFreshNode.append_size tree.nodes index node atEnd
  have ctor := GeneralBorrowPositiveWildcardConstructor.append tree tag fresh noFree fits
    (.ReservedFrz false) .None state true rfl rfl rfl rfl rfl offset len nonzero well bounds
  change tree.newChild _ _ _ _ _ _ = ⟨after,.ok ()⟩ at ctor
  dsimp only
  rw [ctor]
  refine ⟨rfl,?_⟩
  have nextCoherent := GeneralBorrowWildcardRootCache.constructor tree depth mapping index tag (.ReservedFrz false) .None state
    offset len vacant (by rw [size];omega) well bounds protections coherent
  have newStored := GeneralBorrowWildcardRootInstalled.installed tree.locations index state (Size.ofBytes offset) (Size.ofBytes len) well bounds
  have headDifferent : head ≠ index := by intro same;rw [same,vacant] at headPresent;cases headPresent
  have extrasDifferent : ∀ root ∈ extras, root ≠ index := by
    intro root member same
    have present := (data root member).1
    rw [same,vacant] at present
    cases present
  have nextProfile : Every (Profile protections head extras nodes) after.locations := by
    apply GeneralBorrowExposureChildAttach.modify_every (Profile protections head extras nodes) tree.locations
      (Size.ofBytes offset) (Size.ofBytes len) (fun _ location => {location with perms := location.perms.insert index state}) well bounds profile
    intro range location good
    refine ⟨?_,?_⟩
    · simpa only [GeneralBorrowFreshLocation.get_other location.perms index head state headDifferent] using good.1
    · intro root member
      simpa only [effective,GeneralBorrowFreshLocation.get_other location.perms index root state (extrasDifferent root member)] using good.2 root member
  have afterRoots : after.roots = (head::(extras++[index])).toArray := by
    change tree.roots.push index = _
    apply Array.toList_inj.mp
    simp [roots,List.cons_append,List.append_assoc]
  have oldHead : after.nodes.get head = some headNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index head node headDifferent).trans headPresent
  have newPresent : after.nodes.get index = some node := GeneralBorrowFreshLocation.get_same tree.nodes index node
  intro position valid positive start stop range
  have stored := newStored position valid positive start stop
  have localProfile := nextProfile position valid
  have oldData : ∀ root ∈ extras, after.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      supports (effective after.locations.entries[position].data protections root (nodes root)) .Read = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some node.tag) = false := by
    intro root member
    obtain ⟨present,leaf,exposed,bound⟩ := data root member
    refine ⟨(GeneralBorrowFreshLocation.get_other tree.nodes index root node (extrasDifferent root member)).trans present,
      leaf,exposed,localProfile.2 root member,?_⟩
    simp only [GeneralBorrowWildcardVirtualLeaf.onlyForeign,node,WildcardHitZeroConstructor.rootNode]
    have notLt : ¬ tag.value < (nodes root).tag.value := by
      have := UInt64.le_iff_toNat_le.mp bound
      simp only [UInt64.lt_iff_toNat_lt]
      omega
    exact decide_eq_false notLt
  obtain ⟨final,actual,status,finalCoherent,cache⟩ := GeneralBorrowExposedConcreteLast.access after _ protections head index headNode node extras nodes range
    afterRoots (Ne.symm headDifferent) extrasDifferent oldHead headLeaf headExposed localProfile.1 headBound newPresent rfl rfl rfl state stored
    (by intro held;cases held <;> simp [state,GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.LocalReadable,LocationState.possible])
    (nextCoherent position valid) (by change (tree.nodes.insert index node).size < 65536;rw [size];exact short) oldData
  exact ⟨status,by rw [actual];exact finalCoherent⟩
end DuplicatePrefix.GeneralBorrowWildcardConstructorNextRead
