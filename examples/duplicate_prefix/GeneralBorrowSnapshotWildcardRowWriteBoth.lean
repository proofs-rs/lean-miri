import duplicate_prefix.GeneralBorrowSnapshotWriteBothFold
import duplicate_prefix.DuplicatePrefixPrimaryWriteRuntimeBoth
import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowVirtualRootsAdapter
namespace DuplicatePrefix.GeneralBorrowSnapshotWildcardRowWriteBoth
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection DuplicatePrefixCallbackAuthorization
open DuplicatePrefixResidualSupportAuthorization GeneralBorrowSnapshotWriteBothFold
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem reposition (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (before after : Nat) (kind : AccessKind) (support : UniIndex → Prop)
    (sameVirtual : (before != 0) = (after != 0))
    (auth : Authorization tree location protections root before none kind support) :
    Authorization tree location protections root after none kind support := by
  refine ⟨auth.rooted,auth.present,auth.children,auth.covers,auth.possible,?_,?_⟩
  · intro first last firstLegal lastLegal included index node supported present missing
    simpa only [residualRelation,sameVirtual] using auth.queries first last firstLegal lastLegal included index node supported present missing
  · intro physical
    have beforeZero : before = 0 := by
      have zero : (before != 0) = false := by simpa [physical] using sameVirtual
      simpa using zero
    exact auth.witness beforeZero

private def scan (tree : BorrowTree) (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (root : UniIndex) (state : GeneralBorrowVirtualRootsAdapter.State) : Id (ForInStep GeneralBorrowVirtualRootsAdapter.State) :=
  if state.2.1 = none ∧ state.2.2 = false then
    let first := tree.performWildcardAccessAt state.1 root none kind protections true
    if first.status = .Completed then .yield (first.location,state.2.1,state.2.2)
    else .yield (first.location,some (.WildcardFailure range first.status),state.2.2)
  else .yield state

private theorem successful (tree : BorrowTree) (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (roots : List UniIndex) (before after : LocationTree)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree roots before none kind protections = ⟨after,.Completed⟩) :
    forIn roots (before,none,false) (scan tree kind protections range) = (after,none,false) := by
  induction roots generalizing before with
  | nil => cases completed;rfl
  | cons root rest ih =>
    have good : (tree.performWildcardAccessAt before root none kind protections true).status = .Completed := by
      simp only [GeneralBorrowWildcardVirtualLeafFold.run] at completed
      split at completed
      · exact of_decide_eq_true ‹_ = true›
      · have status := congrArg BorrowTree.WildcardLocationAccessResult.status completed
        simp_all
    have tail : GeneralBorrowWildcardVirtualLeafFold.run tree rest
        (tree.performWildcardAccessAt before root none kind protections true).location none kind protections = ⟨after,.Completed⟩ := by
      simpa only [GeneralBorrowWildcardVirtualLeafFold.run,good,beq_self_eq_true,ite_true] using completed
    rw [List.forIn_cons]
    simp only [scan,good,bind,pure,↓reduceIte]
    exact ih _ tail

private def scanAt (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (position : Nat) (state : GeneralBorrowVirtualRootsAdapter.State) : Id (ForInStep GeneralBorrowVirtualRootsAdapter.State) :=
  if state.2.1 = none ∧ state.2.2 = false then
    match (primary::extras)[position]? with
    | none => .yield state
    | some root =>
      let first := tree.performWildcardAccessAt state.1 root none kind protections (position != 0)
      if first.status = .Completed then .yield (first.location,state.2.1,state.2.2)
      else .yield (first.location,some (.WildcardFailure range first.status),state.2.2)
  else .yield state

private theorem indexed (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange) (initial : GeneralBorrowVirtualRootsAdapter.State) :
    forIn (List.range' 1 extras.length) initial (scanAt tree primary extras kind protections range) =
      forIn extras initial (scan tree kind protections range) := by
  calc
    _ = forIn (List.range' 1 extras.length) initial
        (fun pos state => scan tree kind protections range (primary::extras)[pos]! state) := by
      apply GeneralBorrowVirtualRootsAdapter.forIn_congr
      intro pos member state
      obtain ⟨index,bound,position⟩ := List.mem_range'.mp member
      have positionEq : pos = index+1 := by omega
      subst pos
      have selected : (primary::extras)[index+1]? = some extras[index] := by
        simp only [List.getElem?_cons_succ,List.getElem?_eq_getElem bound]
      simp only [scanAt,Nat.one_mul,Nat.add_comm 1 index,selected,show (index+1 != 0) = true from by simp,
        scan,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]
    _ = forIn ((List.range' 1 extras.length).map (fun pos => (primary::extras)[pos]!)) initial
        (scan tree kind protections range) := List.forIn_map.symm
    _ = _ := by rw [GeneralBorrowVirtualRootsAdapter.index_map]

private theorem iterator (tree : BorrowTree) (before middle after : LocationTree) (primary : UniIndex)
    (extras : List UniIndex) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (primary::extras).toArray)
    (first : tree.performWildcardAccessAt before primary none kind protections false = ⟨middle,.Completed⟩)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none kind protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree before none kind protections mode range) = after ∧
    source_access_status (source_tree_access_at tree before none kind protections mode range) = none := by
  simp_tree_helpers
  simp only [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    List.size_toArray,List.length_cons]
  simp [List.size_toArray,List.range'_succ,bind,pure,first]
  change (forIn (List.range' 1 extras.length) (middle,none,false)
    (scanAt tree primary extras kind protections range)).1 = after ∧
    (forIn (List.range' 1 extras.length) (middle,none,false)
    (scanAt tree primary extras kind protections range)).2.1 = none
  rw [indexed,successful tree kind protections range extras middle after completed]
  exact ⟨rfl,rfl⟩


/-- Actual wildcard-provenance full row Write preserves BOTH raw S01 callback
authorizations on the resulting row. No operation, counter frame, removal
mask, scalar-transfer table, or successor-family certificate is assumed. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections none none none)
    (distinct : tree.roots.toList.Nodup) (nonempty : 0 < tree.roots.size)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location none .Write protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    (∀ query, tree.nodes.get query = none → (source_access_location result).perms.get query = location.perms.get query) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree (source_access_location result) protections none none none) := by
  cases rootList : tree.roots.toList with
  | nil =>
    have zero : tree.roots.size = 0 := by
      have length := congrArg List.length rootList
      simpa only [Array.length_toList,List.length_nil] using length
    omega
  | cons primary extras =>
    have roots : tree.roots = (primary::extras).toArray := by rw [←rootList]
    have listDistinct : (primary::extras).Nodup := by simpa only [rootList] using distinct
    obtain ⟨primarySupport,primaryRead,primaryWrite⟩ := row.callbacks 0 nonempty (by simp)
    have primaryRead : Authorization tree location protections primary 0 none .Read primarySupport := by
      simpa only [roots,List.getElem_toArray,List.getElem_cons_zero] using primaryRead
    have primaryWrite : Authorization tree location protections primary 0 none .Write primarySupport := by
      simpa only [roots,List.getElem_toArray,List.getElem_cons_zero] using primaryWrite
    have package : ∀ root ∈ extras, ∃ support, Authorization tree location protections root 1 none .Read support ∧
        Authorization tree location protections root 1 none .Write support := by
      intro root member
      obtain ⟨position,bounded,selected⟩ := List.getElem_of_mem member
      have valid : position+1 < tree.roots.size := by simp only [roots,List.size_toArray,List.length_cons];omega
      have selectedArray : tree.roots[position+1]'valid = root := by
        simpa only [roots,List.getElem_toArray,List.getElem_cons_succ] using selected
      obtain ⟨support,read,write⟩ := row.callbacks (position+1) valid (by simp)
      rw [selectedArray] at read write
      exact ⟨support,reposition tree location protections root (position+1) 1 .Read support (by simp) read,
        reposition tree location protections root (position+1) 1 .Write support (by simp) write⟩
    let supports : UniIndex → UniIndex → Prop := fun root =>
      if root = primary then primarySupport else
        if member : root ∈ extras then Classical.choose (package root member) else fun _ => False
    let positions : UniIndex → Nat := fun root => if root = primary then 0 else 1
    have family : BothFamily tree location protections (primary::extras) positions supports := by
      intro root member
      rcases List.mem_cons.mp member with same | later
      · subst root
        simpa only [supports,positions,ite_true] using And.intro primaryRead primaryWrite
      · have different : root ≠ primary := by intro same;subst root;exact (List.nodup_cons.mp listDistinct).1 later
        simpa only [supports,positions,if_neg different,dif_pos later] using Classical.choose_spec (package root later)
    have members : ∀ root ∈ (primary::extras), root ∈ tree.roots.toList := by intro root member;simpa only [rootList] using member
    obtain ⟨complete,afterCoherent,afterProfile,afterPossible,absent,matching,writeSnapshot,readSnapshot,writeAfter,readAfter,outside⟩ :=
      DuplicatePrefixPrimaryWriteRuntimeBoth.access tree location protections formed primary primarySupport primaryWrite coherent short profile possible
    let middle := (tree.performWildcardAccessAt location primary none .Write protections false).location
    have nextFamily : BothFamily tree middle protections (primary::extras) positions supports := by
      intro other member
      by_cases same : other = primary
      · subst other
        simpa only [supports,positions,ite_true] using And.intro readAfter writeAfter
      · have auth := family other member
        have transport (kind : AccessKind) (authorization : Authorization tree location protections other (positions other) none kind (supports other)) :
            Authorization tree middle protections other (positions other) none kind (supports other) :=
          GeneralBorrowRootLocalCounterFrame.authorization_other_no_maximum tree location middle protections formed primary other
            (members primary (by simp)) (members other member) (Ne.symm same) primarySupport (supports other) primaryWrite.covers
            (positions other) kind authorization coherent afterCoherent short outside
        exact ⟨transport .Read auth.1,transport .Write auth.2⟩
    have virtual : ∀ root ∈ extras, positions root ≠ 0 := by
      intro root member
      have different : root ≠ primary := by intro same;subst root;exact (List.nodup_cons.mp listDistinct).1 member
      simp only [positions,if_neg different];decide
    have tail := GeneralBorrowSnapshotWriteBothFold.run tree middle protections formed extras (primary::extras) positions supports
      (by intro root member;simp [member]) members virtual nextFamily afterCoherent short afterProfile afterPossible
    obtain ⟨tailDone,tailCoherent,tailProfile,tailPossible,tailVacant,tailOutside,finalFamily⟩ := tail
    let final := (GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Write protections).location
    have firstEq : tree.performWildcardAccessAt location primary none .Write protections false = ⟨middle,.Completed⟩ := by
      have reconstruct : tree.performWildcardAccessAt location primary none .Write protections false =
        ⟨middle,(tree.performWildcardAccessAt location primary none .Write protections false).status⟩ := rfl
      rw [complete] at reconstruct
      exact reconstruct
    have tailEq : GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Write protections = ⟨final,.Completed⟩ := by
      have reconstruct : GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Write protections =
        ⟨final,(GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Write protections).status⟩ := rfl
      rw [tailDone] at reconstruct
      exact reconstruct
    have actual := iterator tree location middle final primary extras .Write protections mode range roots firstEq tailEq
    have restored : Nonempty (DuplicatePrefixBorrowAuthorization.Row tree final protections none none none) := by
      refine ⟨{wildcard := fun _ => rfl,rootPath := ?_,rootPresent := ?_,cutoff := rfl,normal := ?_,callbacks := ?_}⟩
      · intro anchor impossible;cases impossible
      · intro root impossible;cases impossible
      · intro anchor impossible;cases impossible
      · intro position valid different
        have member : tree.roots[position]'valid ∈ (primary::extras) := by
          rw [←rootList]
          exact Array.mem_toList_iff.mpr (Array.getElem_mem valid)
        have auth := finalFamily tree.roots[position] member
        have sameVirtual : (positions tree.roots[position] != 0) = (position != 0) := by
          by_cases zero : position = 0
          · subst position
            simp only [roots,List.getElem_toArray,List.getElem_cons_zero,positions,ite_true]
          · have afterZero : tree.roots[position]'valid ≠ primary := by
              intro same
              have posBound : position < (primary::extras).length := by simpa only [roots,List.size_toArray] using valid
              have eq : (primary::extras)[position]'posBound = (primary::extras)[0]'(by simp) := by
                simpa only [roots,List.getElem_toArray,List.getElem_cons_zero] using same
              exact zero (listDistinct.getElem_inj.mp eq)
            simp [positions,afterZero,zero]
        exact ⟨supports tree.roots[position],
          reposition tree final protections tree.roots[position] (positions tree.roots[position]) position .Read _ sameVirtual auth.1,
          reposition tree final protections tree.roots[position] (positions tree.roots[position]) position .Write _ sameVirtual auth.2⟩
    refine ⟨actual.2,?_,?_,?_,?_,?_⟩
    · rw [actual.1];exact tailCoherent
    · rw [actual.1];exact tailProfile
    · rw [actual.1];exact tailPossible
    · rw [actual.1];intro query missing;exact (tailVacant query missing).trans (absent query missing)
    · rw [actual.1];exact restored

end DuplicatePrefix.GeneralBorrowSnapshotWildcardRowWriteBoth
