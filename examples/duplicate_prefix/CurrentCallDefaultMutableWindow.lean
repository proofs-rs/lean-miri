import duplicate_prefix.CurrentCallResourceDefaultMutable
import duplicate_prefix.CurrentCallSharedConstructorWindow
namespace DuplicatePrefix.CurrentCallDefaultMutableWindow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership OrdinaryBorrowAuthority GeneralBorrowView GeneralBorrowProjection GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable CurrentCallResourceNormalization
open GeneralBorrowFreshGraph

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
open Lean Elab Term in
elab "default_window_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked shared window helper {suffix.getString}"
noncomputable section
private theorem modify_owned (map : DedupRangeMap LocationTree) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (modify : LocationTree → LocationTree) (idempotent : ∀ location, modify (modify location) = modify location)
    (P Q : LocationTree → Prop) (step : ∀ location, P location → Q (modify location))
    (lower upper : UInt64) (insideLower : offset.bytes.toNat≤lower.toNat)
    (insideUpper : upper.toNat≤offset.bytes.toNat+len.bytes.toNat)
    (owned : OwnedOn P lower upper map) :
    OwnedOn Q lower upper
      (map.modifyRange offset len (fun _ location => modify location)).state := by
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len (fun _ location => modify location)
  have preparedGood := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := GeneralRangeMapOrigins.refines_owned_on map prepared.state P lower upper
    preparedGood.1.wellFormed preparedGood.2.1 owned
  have fits : offset.bytes.toNat+len.bytes.toNat<2^64:=Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt map.size.bytes)
  have endEq : (offset.bytes+len.bytes).toNat=offset.bytes.toNat+len.bytes.toNat:=by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by
    change position < changed.state.entries.size at valid
    omega
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len (fun _ location => modify location)
    (fun _ location => idempotent location) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    split at known <;> exact known
  rw [rangeEq] at start stop
  have actualPositive : offset.bytes.toNat<(offset.bytes+len.bytes).toNat:=by omega
  have overlapLower : (map.iterMut offset len).state.entries[position].range.start.toNat<(offset.bytes+len.bytes).toNat:=by
    change prepared.state.entries[position].range.start.toNat<_
    omega
  have overlapUpper : offset.bytes.toNat<(map.iterMut offset len).state.entries[position].range.stop.toNat:=by
    change _<prepared.state.entries[position].range.stop.toNat
    omega
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected map offset len well bounds actualPositive position oldValid overlapLower overlapUpper
  have member : position ∈ prepared.positions.toList := by
    rw [←same]
    exact Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,bounded,rfl⟩)
  simp only [show position ∈ (map.iterMut offset len).positions.toList from member,↓reduceIte] at entryEq
  rw [entryEq]
  apply step
  exact preparedOwned position oldValid positive start stop

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : CurrentCallResourceNormalization.ParentInterpretation tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (unheld : held.contains tag = false) (mapping : UniKeyMap BorTag)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (lower upper : UInt64) (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤offset.toNat+len.toNat)
    (owned : OwnedOn (Authority tree completion held parent) lower upper tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held child) lower upper locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations
  refine modify_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshDefaultChild.inside)
    (Authority tree completion held parent) (Authority stage (extend completion child parent) held child) ?_ lower upper insideLower insideUpper owned
  intro location authority
  exact (default_window_rule ".CurrentCallResourceDefaultMutable.stage_location") tree completion held complete child parent parentNode tag vacant parentAt mapping locations location authority

theorem raw (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : CurrentCallResourceNormalization.ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (lower upper : UInt64) (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤offset.toNat+len.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags child)
          lower upper actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth⟩ := GeneralBorrowDefaultConstructorRuntime.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound unheld offset len nonzero bounds
  obtain ⟨child,lookup,_,_,_⟩ := GeneralBorrowDefaultChildMetadata.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,?_⟩
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefault.append input
    have same : GeneralBorrowFreshMetadataChildDefault.index input = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size :=
      GeneralBorrowFreshMetadataChildDefault.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := stage_owned tree completion global.protectedTags complete _ parent parentNode newTag vacant present unheld
      (GeneralBorrowFreshMetadataChildDefault.mapping input) offset len runtime.formed.well bounds lower upper insideLower insideUpper owned
    have result := (default_window_rule ".CurrentCallResourceDefaultMutable.shape_owned") (GeneralBorrowFreshMetadataChildDefault.stage input)
      (GeneralBorrowFreshMetadataChildDefault.result input) _ global.protectedTags (GeneralBorrowFreshMetadataChildDefault.index input) lower upper
      (GeneralBorrowFreshMetadataChildDefault.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefault.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have staged := stage_owned tree completion global.protectedTags complete index parent parentNode newTag vacant present unheld
      (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) offset len runtime.formed.well bounds lower upper insideLower insideUpper owned
    have result := (default_window_rule ".CurrentCallResourceDefaultMutable.shape_owned") (GeneralBorrowFreshMetadataChildDefaultReuse.stage input)
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input) _ global.protectedTags index lower upper
      (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.result,input] using result

/-- One actual Default mutable constructor, with parent interpretation and
new-child authority restricted to the supplied contained subwindow. Root
liveness and parent order are lower structural facts, independent of contents. -/
theorem construct_window (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (tagBound : newTag.value.toNat<global.nextPointerTag.value.toNat) (unheld : global.protectedTags.contains newTag=false)
    (actualOffset actualLen : UInt64) (nonzero : actualLen≠0)
    (bounds : actualOffset.toNat+actualLen.toNat≤tree.locations.size.bytes.toNat)
    (lower upper : UInt64) (insideLower : actualOffset.toNat≤lower.toNat)
    (insideUpper : upper.toNat≤actualOffset.toNat+actualLen.toNat)
    (primaryLive : ∃node,tree.nodes.get allocationRoot=some node)
    (parentOrder : parentNode.tag.value≤newTag.value)
    (owned : OwnedOn (Authority tree C global.protectedTags parent) lower upper tree.locations) :
    let actual:=tree.newChild (Size.ofBytes actualOffset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes actualLen) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome=.ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size=tree.locations.size ∧actual.tree.nodes.size≤tree.nodes.size+1 ∧
    ∃child,actual.tree.indexOfTag newTag=some child ∧ParentInterpretation actual.tree (extend C child parent) ∧
      OwnedOn (Authority actual.tree (extend C child parent) global.protectedTags child) lower upper actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,leaf,completed,ancestry,defaults⟩:=
    (default_window_rule ".CurrentCallResourceDefaultMutable.completion_construct") tree global C runtime parents
      parentTag newTag parent parentNode tagged present fresh room tagBound unheld actualOffset actualLen nonzero bounds primaryLive parentOrder
  obtain ⟨_,_,_,_,framedChild,framedLookup,framed⟩:=raw tree global C runtime parents parentTag newTag parent parentNode tagged present fresh room
    tagBound unheld actualOffset actualLen nonzero bounds lower upper insideLower insideUpper owned
  have same : framedChild=child:=Option.some.inj (framedLookup.symm.trans lookup)
  subst framedChild
  exact ⟨done,afterRuntime,capacity,growth,child,lookup,completed,framed⟩

end
end DuplicatePrefix.CurrentCallDefaultMutableWindow
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallDefaultMutableWindow" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved default mutable subwindow dependency {dependency}"
