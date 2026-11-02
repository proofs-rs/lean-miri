import duplicate_prefix.CurrentCallResourceEntry
import duplicate_prefix.CurrentCallExclusiveWindowFrame
import duplicate_prefix.CurrentCallAllocationLicense

namespace DuplicatePrefix.CurrentCallResourceSourceAfterBool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration
open CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]


variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

def sourceC : Completion := S05ConcreteProtectedChildCompletion.extend W.precise.completion out.sourceChild W.pointer.grant
def pointer : PointerInstance := CurrentCallResourceFnEntry.child_pointer W out.sourceOutput.tag out.sourceChild
private def qPrecise : PreciseAllocation := {W.precise with completion := sourceC out}
private def bPrecise : PreciseAllocation := {C.V.precise with completion := out.R.completion}

/-- Backend dictionaries only: no content-fragment freshness or post denotation
is asserted by these appended technical indices. -/
private def dataView : Identities :=
  { data with interpretation := {data.interpretation with
    pointers := data.interpretation.pointers.push (pointer out)
    loans := data.interpretation.loans.push ⟨data.interpretation.pointers.size,some owner,W.loan.depth+1⟩
    precise := (data.interpretation.precise.push (id,qPrecise out)).push (id,bPrecise out) } }

include out in
private theorem original_runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global ∧
    W.allocation.extra.roots.toList.Nodup := by
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some out.sourceLive)
  have eq := congrArg Allocation.extra out.sourceAllocation
  exact ⟨⟨by simpa only [eq] using C.state.formed (id,out.sourceEntry) member,
    by simpa only [eq] using C.state.coherent (id,out.sourceEntry) member,
    by simpa only [eq] using C.state.possible (id,out.sourceEntry) member,
    by simpa only [eq] using C.highwater (id,out.sourceEntry) member⟩,
    by simpa only [eq] using C.state.roots (id,out.sourceEntry) member⟩

theorem source_live : out.sourceMachine.memory.live.find? (fun row => row.1 == id) =
    some (id,{out.sourceEntry with allocation := out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree}) := by
  rw [out.sourceMachineEq]
  exact MemoryCopyBridge.live_lookup_replaced before.memory id _

theorem same_entry (same : out.physical.id = id) :
    out.physical.entry = {out.sourceEntry with allocation := out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree} := by
  have live : out.sourceMachine.memory.live.find? (fun row => row.1 == id) = some (id,out.physical.entry) := by
    simpa only [same] using out.physical.live
  exact (Prod.mk.inj (Option.some.inj (live.symm.trans (source_live out)))).2

theorem source_present : Present (ActualWorld out.sourceMachine) id (W.allocation.setExtra out.sourceOutput.child.tree) := by
  have live : out.sourceMachine.memory.live.find? (fun row => row.1 == id) =
      some (id,{out.sourceEntry with allocation := out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree}) := by
    rw [out.sourceMachineEq]
    exact MemoryCopyBridge.live_lookup_replaced before.memory id _
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,{out.sourceEntry with allocation := out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree}),
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),by simp only [out.sourceAllocation]⟩

theorem source_issued : SpatialDelegation out.sourceMachine ⟨out.sourceOutput.global,tracker.retagMode⟩ id
    (W.allocation.setExtra out.sourceOutput.child.tree) (sourceC out) out.sourceChild := by
  apply (CurrentCallBorrowIssuance.post W (original_runtime out).1 out.sourceOutput out.sourceChild (UInt64.ofNat offset) len
    out.sourceWitness out.sourceTag out.sourceMachine ⟨out.sourceOutput.global,tracker.retagMode⟩ (source_present out) _).2
  rw [out.sourceGlobal]
  rfl

private def sourceView : UniformWindow out.sourceMachine ⟨out.sourceOutput.global,tracker.retagMode⟩
    (dataView out) data.interpretation.loans.size id offset len.toNat .mut where
  loan := ⟨data.interpretation.pointers.size,some owner,W.loan.depth+1⟩
  pointer := pointer out
  allocation := W.allocation.setExtra out.sourceOutput.child.tree
  precise := qPrecise out
  loanAt := by simp [dataView]
  pointerAt := by simp [dataView]
  pointerId := rfl
  present := source_present out
  preciseAt := Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inl (Array.mem_push.mpr (.inr rfl))))
  binding := out.sourceWitness.binding
  issued := source_issued out
  parents := out.sourceWitness.parents
  window := by
    intro byte inside
    exact out.sourceWitness.window byte inside

private def boolView (same : out.physical.id = id) : UniformWindow out.sourceMachine ⟨out.sourceOutput.global,tracker.retagMode⟩
    (dataView out) C.returnOwner id out.physical.offset.toNat 1 .ret where
  loan := C.V.loan
  pointer := C.V.pointer
  allocation := C.V.allocation.setExtra out.R.tree
  precise := bPrecise out
  loanAt := by
    have bound := (Array.getElem?_eq_some_iff.mp C.V.loanAt).1
    simpa [dataView,Array.getElem?_push,Nat.ne_of_lt bound] using C.V.loanAt
  pointerAt := by
    have bound := (Array.getElem?_eq_some_iff.mp C.V.pointerAt).1
    simpa [dataView,Array.getElem?_push,Nat.ne_of_lt bound] using C.V.pointerAt
  pointerId := C.V.pointerId.trans (out.physicalId.symm.trans same)
  present := by
    have originalSame := out.physicalId.symm.trans same
    simpa only [originalSame] using out.R.present
  preciseAt := Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
  binding := out.R.binding
  issued := by
    have originalSame := out.physicalId.symm.trans same
    simpa only [originalSame,bPrecise] using out.R.issued
  parents := out.R.parents
  window := by
    intro byte inside
    apply out.R.window byte
    have originalSame := out.physicalId.symm.trans same
    simpa only [originalSame,out.physicalOffset] using inside

include out in
private theorem source_bounds :
    offset < 2^64 ∧ (UInt64.ofNat offset).toNat = offset ∧
    (UInt64.ofNat offset).toNat+len.toNat ≤ W.allocation.extra.locations.size.bytes.toNat := by
  have last := (out.sourceWitness.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have positive := C.positive
  have extent := W.issued.capability.extent
  have treeExtent := W.issued.capability.treeExtent
  have bounded := UInt64.toNat_lt W.allocation.byteSize.bytes
  have fits : offset < 2^64 := by omega
  have start : (UInt64.ofNat offset).toNat = offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  exact ⟨fits,start,by rw [start,treeExtent,←extent];omega⟩

/-- Exact actual-node frame needed by spatial allocation licensing. It says
nothing about stored bytes, initialization, or the provenance-map contents. -/
structure SameFrame where
  capacity : out.updated.extra.locations.size = out.sourceOutput.child.tree.locations.size
  roots : ∀ (position : Nat) (root : UniIndex),out.sourceOutput.child.tree.roots[position]? = some root → out.updated.extra.roots[position]? = some root
  nodes : ∀ index node,out.sourceOutput.child.tree.nodes.get index = some node →
    ∃ next,out.updated.extra.nodes.get index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
      next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission
  edges : ∀ (first second : UniIndex),(sourceC out).parents[first.toNat]? = some (some second) →
    (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant).parents[first.toNat]? = some (some second)

/-- The current source child, not its caller parent, retains full raw source
window authority through SAME-allocation Bool Read, constructor, and Write. -/
private theorem same_framed (same : out.physical.id = id) :
    GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority out.updated.extra
      (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
      out.boolOutput.global.protectedTags out.sourceChild)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) out.updated.extra.locations ∧
    PointerBinds out.updated (pointer out) ∧ SameFrame out := by
  let Q := sourceView out
  let B := boolView out same
  have originalSame : C.physical.id = id := out.physicalId.symm.trans same
  have trees := out.sameTree originalSame
  have allocationEq : Q.allocation = B.allocation := by
    change W.allocation.setExtra out.sourceOutput.child.tree = C.V.allocation.setExtra out.R.tree
    rw [C.sameAllocation originalSame,trees.1]
  have completionEq : Q.precise.completion = B.precise.completion := trees.2.symm
  have separate : ∀ byte,Window id out.physical.offset.toNat 1 byte → Window id offset len.toNat byte → False := by
    intro byte boolInside sourceInside
    apply C.separate originalSame byte sourceInside
    simpa only [originalSame,out.physicalOffset] using boolInside
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra out.sourceOutput.global := by
    change DuplicatePrefixBorrowContract.RuntimeFacts out.R.tree out.sourceOutput.global
    rw [trees.1]
    exact out.sourceWitness.runtime
  have nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295 := by have h:=C.sourceShort;omega
  have nonzero : len ≠ 0 := by intro zero;have p:=C.positive;rw [zero] at p;cases p
  have growth := CurrentCallResourceBorrowGrowth.operation W (original_runtime out).1 C.state C.highwater C.borrowFrame C.fresh (by rfl)
    (original_runtime out).2 C.sourceShort nodeRoom (UInt64.ofNat offset) len (source_bounds out).2.1 rfl nonzero (source_bounds out).2.2
    out.sourceOutput out.sourceActual
  have boolRoom := C.boolRoom
  have sameAlloc := C.sameAllocation originalSame
  have short : B.allocation.extra.nodes.size < 65536 := by
    change out.R.tree.nodes.size < 65536
    rw [trees.1]
    rw [sameAlloc] at boolRoom
    omega
  have distinct : B.allocation.extra.roots.toList.Nodup := by
    change out.R.tree.roots.toList.Nodup
    rw [trees.1]
    exact CurrentCallResourceSourceKeyOrigin.roots W (original_runtime out).1 C.state C.highwater C.borrowFrame C.fresh (by rfl)
      (original_runtime out).2 C.sourceShort nodeRoom (UInt64.ofNat offset) len (source_bounds out).2.1 rfl nonzero (source_bounds out).2.2
      out.sourceOutput out.sourceActual
  have boolBounds : out.physical.offset.toNat+1 ≤ B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (id,out.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent]
    omega
  obtain ⟨other,otherChild,actual,⟨witness⟩,owned,binding,embedding⟩ := CurrentCallExclusiveWindowFrame.invoke B Q C.positive (by rfl)
    allocationEq completionEq separate runtime out.sourceOutput.frame out.returnRoom (by rfl) distinct short (by omega)
    out.physical.offset 1 rfl rfl (by decide) boolBounds
  have actualBool : CandidateCurrentFnEntryRaw.operation B.allocation.extra out.sourceOutput.global out.sourceOutput.frame id C.V.pointer.value.provenance out.physical.offset 1 = .ok out.boolOutput := by
    change CandidateCurrentFnEntryRaw.operation out.R.tree out.sourceOutput.global out.sourceOutput.frame id C.V.pointer.value.provenance out.physical.offset 1 = _
    simpa only [same] using out.boolActual
  have outputEq : other = out.boolOutput := Except.ok.inj (actual.symm.trans actualBool)
  subst other
  have firstLookup := witness.runtime.formed.allocator.nodeTags otherChild witness.node witness.nodeAt
  have secondLookup := witness.runtime.formed.allocator.nodeTags out.boolChild out.boolNode out.boolNodeAt
  rw [witness.tag] at firstLookup
  rw [out.boolNodeTag] at secondLookup
  have childEq : otherChild = out.boolChild := Option.some.inj (firstLookup.symm.trans secondLookup)
  subst otherChild
  have currentOwned : GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority out.boolOutput.child.tree
      (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
      out.boolOutput.global.protectedTags out.sourceChild) (UInt64.ofNat offset) (UInt64.ofNat offset+len) out.boolOutput.child.tree.locations := by
    simpa only [Q,B,sourceView,boolView,pointer,bPrecise,CurrentCallResourceFnEntry.child_pointer,UInt64.ofNat_toNat] using owned
  have startEq := (source_bounds out).2.1
  have sourceNoWrap : offset+len.toNat < 2^64 := Nat.lt_of_le_of_lt (by simpa only [startEq] using (source_bounds out).2.2) (UInt64.toNat_lt W.allocation.extra.locations.size.bytes)
  have endEq : (UInt64.ofNat offset+len).toNat = offset+len.toNat := by simp only [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt sourceNoWrap]
  have boolNoWrap : out.physical.offset.toNat+1 < 2^64 := Nat.lt_of_le_of_lt boolBounds (UInt64.toNat_lt B.allocation.extra.locations.size.bytes)
  have boolEnd : (out.physical.offset+1).toNat = out.physical.offset.toNat+1 := by simp only [UInt64.toNat_add,show (1:UInt64).toNat=1 from rfl,Nat.mod_eq_of_lt boolNoWrap]
  have apart : ∀ point : UInt64,(UInt64.ofNat offset).toNat ≤ point.toNat → point.toNat < (UInt64.ofNat offset+len).toNat →
      point.toNat < out.physical.offset.toNat ∨ (out.physical.offset+1).toNat ≤ point.toNat := by
    intro point lower upper
    by_cases early : point.toNat < out.physical.offset.toNat
    · exact .inl early
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro overlap
      exact separate (id,point.toNat) ⟨rfl,by omega,by omega⟩ ⟨rfl,by omega,by omega⟩
  have afterBounds : out.physical.offset.toNat+1 ≤ out.boolOutput.child.tree.locations.size.bytes.toNat := by
    rw [witness.capacity]
    exact boolBounds
  have retained := (CurrentCallExclusiveWindowFrame.write_outside out.boolOutput.child.tree
    (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
    out.boolOutput.global.protectedTags out.sourceChild (.concrete out.sourceOutput.global.nextPointerTag)
    (Size.ofBytes out.physical.offset) (Size.ofBytes 1) .VisitChildrenOfAccessed
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) witness.runtime.formed.well afterBounds apart currentOwned).2
  have updatedBinding : PointerBinds out.updated (pointer out) := by
    obtain ⟨node,nodeAt,mapped,provenance⟩ := binding
    refine ⟨node,?_,?_,provenance⟩
    · change out.updated.extra.nodes.get _ = _
      rw [out.updatedNodes]
      exact nodeAt
    · change out.updated.extra.tagMapping.get node.tag = _
      rw [out.updatedTags]
      exact mapped
  have vacant : out.R.tree.nodes.get out.boolChild = none := by
    cases oldAt : out.R.tree.nodes.get out.boolChild with
    | none => rfl
    | some old =>
      obtain ⟨next,nextAt,tagEq,_,_,_⟩ := witness.oldNodes out.boolChild old oldAt
      have equal : next = out.boolNode := Option.some.inj (nextAt.symm.trans out.boolNodeAt)
      have oldTag : old.tag = out.sourceOutput.global.nextPointerTag :=
        tagEq.symm.trans ((congrArg TreeNode.tag equal).trans (out.boolNodeTag.trans out.boolTag))
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh out.R.tree out.sourceOutput.global runtime out.boolChild old oldAt
      rw [oldTag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have frame : SameFrame out := by
    constructor
    · rw [out.updatedCapacity]
      have capacity := witness.capacity
      change out.boolOutput.child.tree.locations.size = out.R.tree.locations.size at capacity
      exact capacity.trans (congrArg (fun tree : BorrowTree => tree.locations.size) trees.1)
    · intro position root rootAt
      rw [out.updatedRoots]
      apply witness.oldRoots position root
      change out.R.tree.roots[position]? = some root
      rw [trees.1]
      exact rootAt
    · intro index node oldAt
      have beforeAt : out.R.tree.nodes.get index = some node := by rw [trees.1];exact oldAt
      obtain ⟨next,nextAt,tag,parent,exposed,permission⟩ := witness.oldNodes index node beforeAt
      exact ⟨next,by rw [out.updatedNodes];exact nextAt,tag,parent,exposed,permission⟩
    · intro first second edge
      have oldEdge : out.R.completion.parents[first.toNat]? = some (some second) := by
        rw [trees.2]
        exact edge
      have different : first ≠ out.boolChild := by
        intro same
        obtain ⟨node,present⟩ := (out.R.parents.edgeLive first second oldEdge).1
        rw [same,vacant] at present
        cases present
      have bound := (Array.getElem?_eq_some_iff.mp oldEdge).1
      exact (S05ConcreteProtectedChildCompletion.old_parent out.R.completion out.boolChild C.V.pointer.grant first different bound).trans oldEdge
  refine ⟨?_,updatedBinding,frame⟩
  rw [out.updatedExtra]
  exact retained



theorem same_raw (same : out.physical.id = id) :
    GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority out.updated.extra
      (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
      out.boolOutput.global.protectedTags out.sourceChild)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) out.updated.extra.locations :=
  (same_framed out same).1

theorem same_binding (same : out.physical.id = id) : PointerBinds out.updated (pointer out) :=
  (same_framed out same).2.1

/-- SAME actual Bool Read/constructor/write metadata and chosen-edge frame. -/
theorem same_frame (same : out.physical.id = id) : SameFrame out :=
  (same_framed out same).2.2

/-- Actual fresh Bool registration changes no old source-node protector flag;
the source tree is retained when Bool occupies another allocation. -/
theorem registered_source_window (byte : CandidateFreezeContentResources.Byte)
    (inside : Window id offset len.toNat byte) : byte.2 < W.allocation.len ∧
    Embeds (W.allocation.setExtra out.sourceOutput.child.tree) out.boolOutput.global.protectedTags
      (sourceC out) out.sourceChild byte.2 .exclusive := by
  let Q := sourceView out
  let registeredQ := CurrentCallResourceFnEntry.registered_window Q out.sourceWitness.runtime out.sourceOutput.frame out.returnRoom
  have globalEq : (registered out.sourceOutput.global out.sourceOutput.frame id out.returnRoom).1 = out.boolOutput.global := by
    rw [out.boolGlobal]
    rfl
  have window := registeredQ.window byte inside
  change byte.2 < W.allocation.len ∧ Embeds (W.allocation.setExtra out.sourceOutput.child.tree)
    (registered out.sourceOutput.global out.sourceOutput.frame id out.returnRoom).1.protectedTags
    (sourceC out) out.sourceChild byte.2 .exclusive at window
  rw [globalEq] at window
  exact window


/-- SAME-allocation raw rights yield the current q byte embeddings against the
actual written allocation, whose mask/provenance fields may have changed. -/
theorem same_window (same : out.physical.id = id) (byte : CandidateFreezeContentResources.Byte)
    (inside : Window id offset len.toNat byte) : byte.2 < out.updated.len ∧
    Embeds out.updated out.boolOutput.global.protectedTags
      (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
      out.sourceChild byte.2 .exclusive := by
  have length : out.updated.len = W.allocation.len := by
    rw [out.updatedLength,same_entry out same]
    simp only [out.sourceAllocation,Allocation.setExtra,Allocation.mapExtra,Allocation.len]
  refine ⟨by rw [length];exact (out.sourceWitness.window byte inside).1,?_⟩
  have startEq := (source_bounds out).2.1
  have noWrap : offset+len.toNat < 2^64 := Nat.lt_of_le_of_lt
    (by simpa only [startEq] using (source_bounds out).2.2) (UInt64.toNat_lt W.allocation.extra.locations.size.bytes)
  have endEq : (UInt64.ofNat offset+len).toNat = offset+len.toNat := by simp only [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt noWrap]
  have positive := C.positive
  have interval := inside.2
  intro segment member lower upper index node present
  obtain ⟨position,valid,sameSegment⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have rights := same_raw out same position valid (by omega) (by omega) (by omega) index node present
  have realized := CandidateCurrentGrantRuntime.realized _ _ (out.afterRuntime.possible position valid index node present)
    ((out.afterRuntime.formed.profile position valid).present index node present)
  constructor
  · intro below
    exact local_token _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact foreign_no_clash _ _ realized (rights.2 outside) clash

end
end DuplicatePrefix.CurrentCallResourceSourceAfterBool
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceSourceAfterBool.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current source-after-Bool dependency {dependency}"
