import duplicate_prefix.CurrentCallResourceChild
import duplicate_prefix.GeneralBorrowConcreteRangeEntry
import duplicate_prefix.CurrentCallSpatialEntryRead
import duplicate_prefix.CurrentCallResourceSourceKeyOrigin
import duplicate_prefix.CurrentCallSpatialEntryReadSubwindow
namespace DuplicatePrefix.CurrentCallSpatialEntryConstructor
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CurrentCallResourceNormalization GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

/-- Pure full-request materialization retains resource transport on any
contained proof subwindow. It does not split the operation at proof cells. -/
private theorem modify_subwindow (map : DedupRangeMap LocationTree) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat≤map.size.bytes.toNat)
    (modify : LocationTree→LocationTree) (idempotent : ∀ location,modify (modify location)=modify location)
    (P Q : LocationTree→Prop) (step : ∀ location,P location→Q (modify location))
    (lower upper : UInt64) (insideLower : offset.bytes.toNat≤lower.toNat) (insideUpper : upper.toNat≤(offset.bytes+len.bytes).toNat)
    (owned : OwnedOn P lower upper map) :
    OwnedOn Q lower upper (map.modifyRange offset len (fun _ location=>modify location)).state := by
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len (fun _ location=>modify location)
  have preparedGood := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := GeneralRangeMapOrigins.refines_owned_on map prepared.state P lower upper preparedGood.1.wellFormed preparedGood.2.1 owned
  have sizes : changed.state.entries.size=prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position<prepared.state.entries.size := by change position<changed.state.entries.size at valid;omega
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len (fun _ location=>modify location)
    (fun _ location=>idempotent location) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range=(prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    split at known <;> exact known
  rw [rangeEq] at start stop
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected map offset len well bounds (by omega)
    position oldValid (by dsimp only [prepared] at start;omega) (by dsimp only [prepared] at stop;omega)
  have member : position∈prepared.positions.toList := by
    rw [←same]
    exact Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,bounded,rfl⟩)
  simp only [show position∈(map.iterMut offset len).positions.toList from member,↓reduceIte] at entryEq
  rw [entryEq]
  exact step _ (preparedOwned position oldValid positive start stop)

open Lean Elab Term in
elab "spatial_constructor_rule " suffix:str : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := names | throwError "expected one checked constructor resource rule"
  Lean.Meta.mkConstWithFreshMVarLevels name

private theorem stage_owned_subwindow (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child=none) (parentAt : tree.nodes.get parent=some parentNode)
    (mapping : UniKeyMap BorTag) (offset len lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤(offset+len).toNat)
    (owned : OwnedOn (Authority tree completion held parent) lower upper tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location=>GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode (GeneralBorrowFreshChild.child tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held child) lower upper locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location=>GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)).state
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode (GeneralBorrowFreshChild.child tag parent) mapping locations
  refine modify_subwindow tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location=>GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)
    (fun location=>GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshChild.inside)
    (Authority tree completion held parent) (Authority stage (extend completion child parent) held child) ?_ lower upper insideLower insideUpper owned
  intro location authority
  exact (spatial_constructor_rule ".CurrentCallResourceChild.stage_location") tree completion held complete child parent parentNode tag vacant parentAt mapping locations location authority

/-- Concrete construction executes the full range once; only the chosen
subwindow's old-parent authority is consumed by this resource certificate. -/
theorem concrete_subwindow (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (tagBound : newTag.value.toNat<global.nextPointerTag.value.toNat) (held : global.protectedTags.contains newTag=true)
    (offset len lower upper : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤(offset+len).toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child,actual.tree.indexOfTag newTag=some child ∧
      OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags child) lower upper actual.tree.locations := by
  obtain ⟨_,_,_,_,child,lookup,_,_⟩ := CurrentCallParentInsertion.concrete_frame tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held offset len nonzero bounds
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  refine ⟨child,lookup,?_⟩
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutable.append input
    have same : GeneralBorrowFreshMetadataChildMutable.index input=child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat=tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input)=none := by simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := stage_owned_subwindow tree completion global.protectedTags complete (GeneralBorrowFreshMetadataChildMutable.index input) parent parentNode newTag vacant present
      (GeneralBorrowFreshMetadataChildMutable.mapping input) offset len lower upper runtime.formed.well bounds insideLower insideUpper owned
    have result := (spatial_constructor_rule ".CurrentCallResourceChild.shape_owned") (GeneralBorrowFreshMetadataChildMutable.stage input)
      (GeneralBorrowFreshMetadataChildMutable.result input) _ global.protectedTags (GeneralBorrowFreshMetadataChildMutable.index input) lower upper
      (GeneralBorrowFreshMetadataChildMutable.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildMutable.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    have same : index=child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have staged := stage_owned_subwindow tree completion global.protectedTags complete index parent parentNode newTag vacant present
      (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) offset len lower upper runtime.formed.well bounds insideLower insideUpper owned
    have result := (spatial_constructor_rule ".CurrentCallResourceChild.shape_owned") (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
      (GeneralBorrowFreshMetadataChildMutableReuse.result input) _ global.protectedTags index lower upper
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildMutableReuse.result,input] using result

/-- A full wildcard-root constructor may choose a different SAME old origin
in each proof cell; this certificate consumes only a contained subwindow. -/
theorem wildcard_subwindow (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (newTag : BorTag) (origin : UniIndex) (originNode : TreeNode) (present : tree.nodes.get origin=some originNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (tagBound : newTag.value.toNat<global.nextPointerTag.value.toNat) (held : global.protectedTags.contains newTag=true)
    (offset len lower upper : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤(offset+len).toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags origin) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child,actual.tree.indexOfTag newTag=some child ∧
      OwnedOn (Authority actual.tree (extend completion child origin) global.protectedTags child) lower upper actual.tree.locations := by
  obtain ⟨_,afterRuntime,_,_,child,lookup,_,_,_⟩ := GeneralBorrowWildcardConstructorRuntime.protected_mutable tree global runtime newTag fresh room tagBound held offset len nonzero bounds
  obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime newTag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState newTag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  rw [actual] at afterRuntime lookup ⊢
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping index newTag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside offset len
  have ownLookup : model.indexOfTag newTag=some index := afterRuntime.formed.allocator.nodeTags index _ (GeneralBorrowFreshLocation.get_same tree.nodes index _)
  have same : index=child := Option.some.inj (ownLookup.symm.trans lookup)
  refine ⟨child,lookup,?_⟩
  subst child
  apply modify_subwindow tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well bounds
    (fun location=>{location with perms:=location.perms.insert index GeneralBorrowFreshChild.inside})
    (fun location=>by simp only [GeneralBorrowFreshInstallation.insert_idempotent])
    (Authority tree completion global.protectedTags origin) (Authority model (extend completion index origin) global.protectedTags index)
    _ lower upper insideLower insideUpper owned
  intro location authority
  exact (spatial_constructor_rule ".CurrentCallResourceChild.Wildcard.model_location") tree completion global.protectedTags complete mapping index origin newTag vacant
    ⟨originNode,present⟩ offset len location authority

def constructorProvenance (value : Provenance) : ProvenanceExtra :=
  match value with | .concrete _ tag=>.concrete tag | .wildcard=>.wildcard

/-- One actual constructor admits a separate old semantic parent per proof
cell. Only the proof subwindow is owned under that cell's SAME map. -/
theorem parent_subwindow (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (value : Provenance) (origin : UniIndex) (originNode : TreeNode) (present : tree.nodes.get origin=some originNode)
    (binding : match value with | .concrete _ tag=>tag=originNode.tag | .wildcard=>originNode.isExposed=true)
    (newTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : newTag.value.toNat<global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains newTag=true) (older : originNode.tag.value<newTag.value)
    (primaryLive : ∃node,tree.nodes.get allocationRoot=some node)
    (offset len lower upper : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤(offset+len).toNat)
    (owned : OwnedOn (Authority tree C global.protectedTags origin) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (constructorProvenance value) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child,actual.tree.indexOfTag newTag=some child ∧ ParentInterpretation actual.tree (extend C child origin) ∧
      OwnedOn (Authority actual.tree (extend C child origin) global.protectedTags child) lower upper actual.tree.locations := by
  have tagged := runtime.formed.allocator.nodeTags origin originNode present
  cases value with
  | concrete id tag =>
    change tag=originNode.tag at binding
    subst tag
    obtain ⟨child,lookup,childOwned⟩ := concrete_subwindow tree global C runtime parents originNode.tag newTag origin originNode tagged present fresh room tagBound held offset len lower upper nonzero bounds insideLower insideUpper owned
    obtain ⟨_,afterRuntime,_,_,frameChild,frameLookup,leaf,_⟩ := CurrentCallParentInsertion.concrete_frame tree global runtime originNode.tag newTag origin originNode tagged present fresh room tagBound held offset len nonzero bounds
    have same : frameChild=child := Option.some.inj (frameLookup.symm.trans lookup)
    subst frameChild
    have order := GeneralBorrowProtectedChildOrder.construct tree global runtime parents.order originNode.tag newTag origin originNode tagged present fresh room
      (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older))) offset len nonzero bounds
    exact ⟨child,lookup,CurrentCallParentInsertion.of_leaf tree _ C parents child origin leaf primaryLive afterRuntime.formed.toGraphState order,childOwned⟩
  | wildcard =>
    obtain ⟨child,lookup,childOwned⟩ := wildcard_subwindow tree global C runtime parents newTag origin originNode present fresh room tagBound held offset len lower upper nonzero bounds insideLower insideUpper owned
    obtain ⟨_,afterRuntime,_,_,frameChild,frameLookup,_,rootFrame,_⟩ := CurrentCallParentInsertion.wildcard_frame tree global runtime newTag fresh room tagBound held origin originNode present offset len nonzero bounds
    have same : frameChild=child := Option.some.inj (frameLookup.symm.trans lookup)
    subst frameChild
    obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime newTag fresh room (.ReservedFrz false) .None
    obtain ⟨depth⟩ := runtime.formed.depth
    have order := GeneralBorrowWildcardChildCausalOrder.inserted_order tree depth parents.order newTag mapping index inserted vacant
      (Size.ofBytes offset) (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree parents.graph origin originNode present
    exact ⟨child,lookup,CurrentCallParentInsertion.of_root tree _ C parents child origin newTag rootFrame primaryLive afterRuntime.formed.toGraphState order originNode present binding older position root slot path,childOwned⟩

/-- Actual constructor keys originate in the old mapping or the ONE new tag.
This statement is independent of any parent completion or resource window. -/
theorem constructor_keys (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (value : Provenance) (parent : UniIndex) (node : TreeNode) (present : tree.nodes.get parent=some node)
    (binding : match value with | .concrete _ tag=>tag=node.tag | .wildcard=>True)
    (newTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (room : tree.nodes.size+1≤4294967295) (offset len : UInt64) (nonzero : len≠0)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (constructorProvenance value) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∀ key index,(key,index)∈actual.tree.tagMapping.mapping → key=newTag ∨∃oldIndex,(key,oldIndex)∈tree.tagMapping.mapping := by
  cases value with
  | concrete id tag =>
    change tag=node.tag at binding
    subst tag
    have tagged := runtime.formed.allocator.nodeTags parent node present
    let depth := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
    let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent node present room
    have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build tree depth runtime.formed.children runtime.formed.covered
      node.tag newTag parent node tagged present fresh slot offset len nonzero runtime.formed.well runtime.formed.fits bounds
    exact (spatial_constructor_rule ".CurrentCallResourceSourceKeyOrigin.old_lookup_origin") tree.tagMapping _ newTag metadata.oldLookup
  | wildcard =>
    obtain ⟨mapping,index,inserted,_,_⟩ := GeneralBorrowStructuralHistoryWildcardAllocator.select tree runtime.formed.toGraphState newTag fresh room (.ReservedFrz false) .None
    have mapped := GeneralBorrowForestTagHighWaterCtorFrame.mapping tree newTag mapping index inserted (.ReservedFrz false) .None true rfl rfl rfl
      (Size.ofBytes offset) (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside)
    have origins := (spatial_constructor_rule ".CurrentCallResourceSourceKeyOrigin.insert_origin") tree.tagMapping mapping newTag index fresh (by
      intro noFree
      have aligned := GeneralBorrowFreshStagePool.empty_aligned tree runtime.formed.allocator.accounting noFree
      change tree.nodes.data.size+1≤4294967295 at room
      omega) inserted
    simpa only [constructorProvenance,mapped] using origins

open CurrentCallSpatialCover CurrentCallSpatialRows GeneralBorrowFnEntryRegistration CandidateCurrentJointCall CandidateCurrentGrantResources

/-- The registered whole-span Read is followed by ONE actual protected child
constructor. Its execution and metadata do not depend on any cell completion. -/
theorem invoke {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    let output := CurrentCallSpatialEntryRead.output role frame room start amount
    CandidateCurrentFnEntryRaw.operation role.backing.allocation.extra tracker.global frame role.backing.id
      role.family.value.provenance start amount=.ok output ∧
    output.access.status=.Completed ∧ output.child.outcome=.ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
    output.child.tree.locations.size=role.backing.allocation.extra.locations.size ∧
    output.child.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 ∧
    ∃ child,output.child.tree.indexOfTag output.tag=some child ∧
      (∀ (position : Nat) (root : UniIndex),role.backing.allocation.extra.roots[position]?=some root → output.child.tree.roots[position]?=some root) ∧
      (∀ index node,role.backing.allocation.extra.nodes.get index=some node →
        ∃ next,output.child.tree.nodes.get index=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧
          next.isExposed=node.isExposed ∧next.defaultInitialPermission=node.defaultInitialPermission) ∧
      (∃node,output.child.tree.nodes.get child=some node ∧node.tag=output.tag) := by
  let accessed := CurrentCallSpatialEntryRead.read role frame room start amount
  let registration := registered tracker.global frame role.backing.id room
  obtain ⟨contract,afterRuntime,parents⟩ := CurrentCallSpatialEntryRead.invoke role exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  obtain ⟨allocated,held,frameEq,registeredRuntime,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global frame role.backing.id room runtime
  have positive : 0<length := by
    have pos : 0<amount.toNat := Nat.pos_of_ne_zero (fun zero=>nonzero (UInt64.toNat_inj.mp zero))
    omega
  have request : Window role.backing.id offset length (role.backing.id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  have overlap : ∃ byte,Window role.backing.id offset length byte ∧ Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte := ⟨(role.backing.id,offset),request,cell⟩
  obtain ⟨parentNode,parentAt,mapping,binding⟩ := (role.roles i overlap).binding
  have parentAfter : accessed.tree.nodes.get (role.roles i overlap).grant=some parentNode := by rw [contract.nodes];exact parentAt
  have tagged : accessed.tree.indexOfTag parentNode.tag=some (role.roles i overlap).grant := afterRuntime.formed.allocator.nodeTags _ _ parentAfter
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have childRoom : accessed.tree.nodes.size+1≤4294967295 := by change accessed.tree.nodes.data.size+1≤_;rw [contract.nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have literal := CurrentCallSpatialEntryRead.literal_operation role frame room start amount
  cases value : role.family.value.provenance with
  | concrete id tag =>
    change (match role.family.value.provenance with | .concrete id tag=>id=role.family.allocation ∧tag=parentNode.tag | .wildcard=>parentNode.isExposed=true) at binding
    rw [value] at binding
    obtain ⟨done,postRuntime,capacity,growth,child,lookup,leaf,old⟩ := CurrentCallParentInsertion.concrete_frame accessed.tree registration.1 afterRuntime
      parentNode.tag tracker.global.nextPointerTag (role.roles i overlap).grant parentNode tagged parentAfter freshAfter childRoom tagBound tagHeld start amount nonzero childBounds
    obtain ⟨metadataChild,metadataLookup,metadataNode,_,_⟩ := GeneralBorrowProtectedChildMetadata.construct accessed.tree registration.1 afterRuntime
      parentNode.tag tracker.global.nextPointerTag (role.roles i overlap).grant parentNode tagged parentAfter freshAfter childRoom start amount nonzero childBounds
    have metadataSame : metadataChild=child := Option.some.inj (metadataLookup.symm.trans lookup)
    subst metadataChild
    obtain ⟨newNode,newAt,newTag,_⟩ := metadataNode
    dsimp only [accessed] at newAt
    dsimp only [accessed] at done postRuntime capacity growth lookup leaf old
    have provenance : provenance role=.concrete parentNode.tag := by simp only [CurrentCallSpatialRows.provenance,value,binding.2]
    refine ⟨(by simpa only [value] using literal),contract.completed,?_,?_,?_,?_,child,?_,?_,?_,?_⟩
    · simpa only [CurrentCallSpatialEntryRead.output,provenance] using done
    · simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialEntryRead.registeredTracker,provenance] using postRuntime
    · simpa only [CurrentCallSpatialEntryRead.output,provenance] using capacity.trans contract.capacity
    · simpa only [CurrentCallSpatialEntryRead.output,provenance,contract.nodes] using growth
    · simpa only [CurrentCallSpatialEntryRead.output,provenance] using lookup
    · intro position root slot
      change _=some root
      simpa only [CurrentCallSpatialEntryRead.output,provenance,leaf.roots,contract.roots] using slot
    · intro index node present
      simpa only [CurrentCallSpatialEntryRead.output,provenance,BorrowTree.nodeAt] using old index node (by change (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.get index=some node;rw [contract.nodes];exact present)
    · exact ⟨newNode,by simpa only [CurrentCallSpatialEntryRead.output,provenance,BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildMutableSlot.result] using newAt,newTag⟩
  | wildcard =>
    have provenance : provenance role=.wildcard := by simp only [CurrentCallSpatialRows.provenance,value]
    obtain ⟨done,postRuntime,capacity,growth,child,lookup,rootEq,rootFrame,old⟩ := CurrentCallParentInsertion.wildcard_frame accessed.tree registration.1 afterRuntime
      tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld (role.roles i overlap).grant parentNode parentAfter start amount nonzero childBounds
    dsimp only [accessed] at done postRuntime capacity growth lookup rootEq rootFrame old
    obtain ⟨newNode,newAt,newTag,_⟩ := rootFrame.childLive
    refine ⟨(by simpa only [value] using literal),contract.completed,?_,?_,?_,?_,child,?_,?_,?_,?_⟩
    · simpa only [CurrentCallSpatialEntryRead.output,provenance] using done
    · simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialEntryRead.registeredTracker,provenance] using postRuntime
    · simpa only [CurrentCallSpatialEntryRead.output,provenance] using capacity.trans contract.capacity
    · simpa only [CurrentCallSpatialEntryRead.output,provenance,contract.nodes] using growth
    · simpa only [CurrentCallSpatialEntryRead.output,provenance] using lookup
    · intro position root slot
      have bound := (Array.getElem?_eq_some_iff.mp slot).1
      simp only [CurrentCallSpatialEntryRead.output,provenance,rootEq,contract.roots,Array.getElem?_push,show position≠role.backing.allocation.extra.roots.size by omega,↓reduceIte]
      exact slot
    · intro index node present
      simpa only [CurrentCallSpatialEntryRead.output,provenance,BorrowTree.nodeAt] using old index node (by change (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.get index=some node;rw [contract.nodes];exact present)
    · exact ⟨newNode,by simpa only [CurrentCallSpatialEntryRead.output,provenance] using newAt,newTag⟩

/-- Every intersecting proof cell shares ONE actual fresh child. Its SAME
parent map owns only the contained proof subwindow, never the whole request. -/
theorem cells {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    let output := CurrentCallSpatialEntryRead.output role frame room start amount
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      ∀ (i : Fin role.backing.cells.size)
        (overlap : ∃byte,Window role.backing.id offset length byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
        (lower upper : UInt64), offset≤lower.toNat →upper.toNat≤offset+length →
        role.backing.cells[i].offset≤lower.toNat →upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length →
        ParentInterpretation output.child.tree (extend role.backing.cells[i].completion child (role.roles i overlap).grant) ∧
        OwnedOn (Authority output.child.tree (extend role.backing.cells[i].completion child (role.roles i overlap).grant)
          output.global.protectedTags child) lower upper output.child.tree.locations := by
  obtain ⟨_,_,_,_,_,_,child,lookup,_,_,_⟩ := invoke role exclusive runtime distinct short nodeRoom frame room start amount startEq amountEq nonzero bounds
  refine ⟨child,lookup,?_⟩
  intro i overlap lower upper requestLower requestUpper cellLower cellUpper
  let accessed := CurrentCallSpatialEntryRead.read role frame room start amount
  let registration := registered tracker.global frame role.backing.id room
  obtain ⟨contract,afterRuntime,parents⟩ := CurrentCallSpatialEntryRead.invoke role exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  obtain ⟨allocated,held,frameEq,registeredRuntime,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global frame role.backing.id room runtime
  obtain ⟨parentNode,parentAt,mapping,binding⟩ := (role.roles i overlap).binding
  have parentAfter : accessed.tree.nodes.get (role.roles i overlap).grant=some parentNode := by rw [contract.nodes];exact parentAt
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have childRoom : accessed.tree.nodes.size+1≤4294967295 := by change accessed.tree.nodes.data.size+1≤_;rw [contract.nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh role.backing.allocation.extra tracker.global runtime (role.roles i overlap).grant parentNode parentAt
  obtain ⟨primaryNode,primaryAt,_,_,_⟩ := (role.roles i overlap).issued.capability.rootNode
  have primaryLive : ∃node,accessed.tree.nodes.get allocationRoot=some node := ⟨primaryNode,by rw [contract.nodes];exact primaryAt⟩
  have owned := CurrentCallSpatialEntryReadSubwindow.owned_subwindow role exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds i overlap lower upper requestLower requestUpper cellLower cellUpper
  have bindingOnly : match role.family.value.provenance with | .concrete _ tag=>tag=parentNode.tag | .wildcard=>parentNode.isExposed=true := by
    cases value : role.family.value.provenance with
    | concrete id tag => exact (show id=role.family.allocation ∧tag=parentNode.tag from by simpa only [value,Family.at] using binding).2
    | wildcard => simpa only [value,Family.at] using binding
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt role.backing.allocation.extra.locations.size.bytes)
  have endEq : (start+amount).toNat=offset+length := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap,startEq,amountEq]
  obtain ⟨ownChild,ownLookup,ownParents,ownOwned⟩ := parent_subwindow accessed.tree registration.1 role.backing.cells[i].completion afterRuntime (parents i)
    role.family.value.provenance (role.roles i overlap).grant parentNode parentAfter bindingOnly tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld older primaryLive
    start amount lower upper nonzero childBounds (by omega) (by omega) owned
  have same : ownChild=child := Option.some.inj (ownLookup.symm.trans lookup)
  subst ownChild
  exact ⟨ownParents,ownOwned⟩

/-- Registration and the actual whole-span Read preserve old mapping keys;
the ONE actual constructor adds only the allocated fresh tag. -/
theorem key_origin {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    let output := CurrentCallSpatialEntryRead.output role frame room start amount
    ∀ key index,(key,index)∈output.child.tree.tagMapping.mapping → key=output.tag ∨
      ∃oldIndex,(key,oldIndex)∈role.backing.allocation.extra.tagMapping.mapping := by
  obtain ⟨contract,afterRuntime,_⟩ := CurrentCallSpatialEntryRead.invoke role exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  have positive : 0<length := by
    have pos : 0<amount.toNat := Nat.pos_of_ne_zero (fun zero=>nonzero (UInt64.toNat_inj.mp zero))
    omega
  have request : Window role.backing.id offset length (role.backing.id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  have overlap : ∃byte,Window role.backing.id offset length byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte := ⟨_,request,cell⟩
  obtain ⟨node,present,_,binding⟩ := (role.roles i overlap).binding
  have afterAt : (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.get (role.roles i overlap).grant=some node := by rw [contract.nodes];exact present
  have bindingOnly : match role.family.value.provenance with | .concrete _ tag=>tag=node.tag | .wildcard=>True := by
    cases value : role.family.value.provenance with
    | concrete id tag => exact (show id=role.family.allocation ∧tag=node.tag from by simpa only [value,Family.at] using binding).2
    | wildcard => trivial
  have fresh := (GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global frame role.backing.id room runtime).2.2.2.2.2
  have origins := constructor_keys (CurrentCallSpatialEntryRead.read role frame room start amount).tree _ afterRuntime role.family.value.provenance (role.roles i overlap).grant node afterAt bindingOnly tracker.global.nextPointerTag
    (by rw [contract.tags];exact fresh) (by change (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.data.size+1≤_;rw [contract.nodes];exact nodeRoom)
    start amount nonzero (by rw [contract.capacity];exact bounds)
  rw [contract.tags] at origins
  exact origins

end
end DuplicatePrefix.CurrentCallSpatialEntryConstructor

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialEntryConstructor.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial entry constructor dependency {dependency}"
