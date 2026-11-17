import duplicate_prefix.CurrentCallSpatialCover
import duplicate_prefix.CurrentCallSupportChainExtraction

/-! Finite singleton proof covers from pointwise current resource witnesses.
Families are fixed outside byte choices. These are not new runtime partitions,
Ordinary admission, or reconstructed program-copy identities. -/
namespace DuplicatePrefix.CurrentCallPointwiseSpatialCover
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CandidateFreezeContentResources
open CurrentCallResourceNormalization CurrentCallSpatialCover
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def Pointwise (before : Before) (tracker : MachineHooks.BorrowState)
    (family : Family) (allocation : Allocation Provenance BorrowTree) (mode : Mode) (offset length : Nat) : Prop :=
  ∀ byte,Window family.allocation offset length byte →
    ∃ C grant,ParentInterpretation allocation.extra C ∧ PointerBinds allocation (family.at grant) ∧
      SpatialDelegation before tracker family.allocation allocation C grant ∧
      Embeds allocation tracker.global.protectedTags C grant byte.2 (demandOf mode)

def Rows (allocation : Allocation Provenance BorrowTree) (id : AllocId) (offset length : Nat) : Prop :=
  ∀ byte,Window id offset length byte → ∃ segment,segment∈allocation.extra.locations.entries.toList ∧
    segment.range.start.toNat≤byte.2 ∧ byte.2<segment.range.stop.toNat

def ExactCharge (fragment : Fragment) (owner : Nat) (mode : Mode) (id : AllocId) (offset length : Nat) : Prop :=
  ∀ byte,fragment byte owner=some ⟨mode,.active⟩ ↔ Window id offset length byte

theorem exclusive_separate {Fs Fr : Fragment} {sourceOwner returnOwner : Nat} {sourceId returnId : AllocId}
    {sourceOffset sourceLength returnOffset : Nat}
    (composable : Composable Fs Fr)
    (source : ExactCharge Fs sourceOwner .mut sourceId sourceOffset sourceLength)
    (ret : ExactCharge Fr returnOwner .ret returnId returnOffset 1) :
    ∀ byte,Window sourceId sourceOffset sourceLength byte → Window returnId returnOffset 1 byte → False := by
  intro byte sourceHit returnHit
  have incompatible:=composable.2.2.2 byte sourceOwner returnOwner _ _ ((source byte).mpr sourceHit) ((ret byte).mpr returnHit)
  simp [Compatible] at incompatible

private structure Witness (before : Before) (tracker : MachineHooks.BorrowState)
    (family : Family) (allocation : Allocation Provenance BorrowTree) (mode : Mode) (byte : Nat) where
  C : Completion
  grant : UniIndex
  parents : ParentInterpretation allocation.extra C
  binding : PointerBinds allocation (family.at grant)
  issued : SpatialDelegation before tracker family.allocation allocation C grant
  embeds : Embeds allocation tracker.global.protectedTags C grant byte (demandOf mode)

private def choose {before tracker family allocation mode offset length}
    (points : Pointwise before tracker family allocation mode offset length) (i : Fin length) :
    Witness before tracker family allocation mode (offset+i.val) := by
  exact Classical.choice (by
    obtain ⟨C,grant,parents,binding,issued,embeds⟩:=points (family.allocation,offset+i.val) ⟨rfl,by omega,by have h:=i.isLt;omega⟩
    exact ⟨⟨C,grant,parents,binding,issued,embeds⟩⟩)

private def cells {before tracker family allocation mode offset length}
    (points : Pointwise before tracker family allocation mode offset length) : Array (Cell allocation.extra) :=
  Array.ofFn (fun i : Fin length=>⟨offset+i.val,1,(choose points i).C,(choose points i).parents⟩)

private theorem cell_at {before tracker family allocation mode offset length}
    (points : Pointwise before tracker family allocation mode offset length) (i : Nat) (valid : i<(cells points).size) :
    (cells points)[i]=⟨offset+i,1,(choose points ⟨i,by simpa only [cells,Array.size_ofFn] using valid⟩).C,
      (choose points ⟨i,by simpa only [cells,Array.size_ofFn] using valid⟩).parents⟩ := by
  change (Array.ofFn (fun i : Fin length=>(⟨offset+i.val,1,(choose points i).C,(choose points i).parents⟩ : Cell allocation.extra)))[i]'valid=_
  exact Array.getElem_ofFn _

private theorem cell_offset {before tracker family allocation mode offset length}
    (points : Pointwise before tracker family allocation mode offset length) (i : Nat) (valid : i<(cells points).size) :
    ((cells points)[i]'valid).offset=offset+i ∧ ((cells points)[i]'valid).length=1 := by
  rw [cell_at points i valid]
  exact ⟨rfl,rfl⟩

private def backing {before tracker family allocation mode offset length}
    (live : Present (ActualWorld before) family.allocation allocation)
    (points : Pointwise before tracker family allocation mode offset length) : AllocationCover before where
  id:=family.allocation
  allocation:=allocation
  live:=live
  cells:=cells points
  disjoint:=by
    intro i j different byte first second
    change Window family.allocation ((cells points)[i.val]'i.isLt).offset ((cells points)[i.val]'i.isLt).length byte at first
    change Window family.allocation ((cells points)[j.val]'j.isLt).offset ((cells points)[j.val]'j.isLt).length byte at second
    have firstShape:=cell_offset points i.val i.isLt
    have secondShape:=cell_offset points j.val j.isLt
    rw [firstShape.1,firstShape.2] at first
    rw [secondShape.1,secondShape.2] at second
    have a:=first.2
    have b:=second.2
    apply different
    apply Fin.ext
    omega

private theorem cell_inside {before tracker family allocation mode offset length}
    (points : Pointwise before tracker family allocation mode offset length)
    (i : Fin (cells points).size) (byte : Byte)
    (inside : Window family.allocation (cells points)[i].offset (cells points)[i].length byte) :
    Window family.allocation offset length byte := by
  change Window family.allocation ((cells points)[i.val]'i.isLt).offset ((cells points)[i.val]'i.isLt).length byte at inside
  have shape:=cell_offset points i.val i.isLt
  rw [shape.1,shape.2] at inside
  have bound : i.val<length := by simpa only [cells,Array.size_ofFn] using i.isLt
  exact ⟨inside.1,by have h:=inside.2;omega,by have h:=inside.2;omega⟩

private def role {before tracker family allocation mode offset length}
    (live : Present (ActualWorld before) family.allocation allocation)
    (points : Pointwise before tracker family allocation mode offset length)
    (bound : offset+length≤allocation.len)
    (ctx : Context before) (member : backing live points∈ctx.allocations.toList) :
    RoleCover before tracker ctx mode offset length where
  family:=family
  backing:=backing live points
  backingAt:=member
  id:=rfl
  covered:=by
    intro byte hit
    have indexBound : byte.2-offset<length := by have h:=hit.2;omega
    let index : Fin (cells points).size:=⟨byte.2-offset,by simpa only [cells,Array.size_ofFn] using indexBound⟩
    refine ⟨index,?_⟩
    change Window family.allocation ((cells points)[index.val]'index.isLt).offset ((cells points)[index.val]'index.isLt).length byte
    have shape:=cell_offset points index.val index.isLt
    rw [shape.1,shape.2]
    change Window family.allocation (offset+(byte.2-offset)) 1 byte
    exact ⟨hit.1,by have h:=hit.2;omega,by have h:=hit.2;omega⟩
  roles:=by
    intro i overlap
    let index : Fin length:=⟨i.val,by simpa only [backing,cells,Array.size_ofFn] using i.isLt⟩
    let chosen:=choose points index
    refine ⟨chosen.grant,?_,?_,?_⟩
    · exact chosen.binding
    · have valid : i.val<(cells points).size := i.isLt
      change SpatialDelegation before tracker family.allocation allocation ((cells points)[i.val]'valid).completion chosen.grant
      rw [cell_at points i.val]
      exact chosen.issued
    · intro byte request inside
      have valid : i.val<(cells points).size := i.isLt
      change Window family.allocation ((cells points)[i.val]'valid).offset ((cells points)[i.val]'valid).length byte at inside
      have shape:=cell_offset points i.val valid
      rw [shape.1,shape.2] at inside
      have equal : byte.2=offset+i.val := by have h:=inside.2;omega
      refine ⟨by have h:=request.2;change byte.2<allocation.len;omega,?_⟩
      change Embeds allocation tracker.global.protectedTags ((cells points)[i.val]'valid).completion chosen.grant byte.2 (demandOf mode)
      rw [cell_at points i.val valid,equal]
      exact chosen.embeds

private def jointCells {before tracker S R allocation sourceOffset sourceLength returnOffset}
    (source : Pointwise before tracker S allocation .mut sourceOffset sourceLength)
    (ret : Pointwise before tracker R allocation .ret returnOffset 1) : Array (Cell allocation.extra) :=
  Array.ofFn (fun i : Fin (sourceLength+1)=>if h : i.val<sourceLength then
    ⟨sourceOffset+i.val,1,(choose source ⟨i.val,h⟩).C,(choose source ⟨i.val,h⟩).parents⟩
    else ⟨returnOffset,1,(choose ret ⟨0,by decide⟩).C,(choose ret ⟨0,by decide⟩).parents⟩)

private theorem joint_at {before tracker S R allocation sourceOffset sourceLength returnOffset}
    (source : Pointwise before tracker S allocation .mut sourceOffset sourceLength)
    (ret : Pointwise before tracker R allocation .ret returnOffset 1) (i : Nat) (valid : i<(jointCells source ret).size) :
    (jointCells source ret)[i]=(if h : i<sourceLength then
      (⟨sourceOffset+i,1,(choose source ⟨i,h⟩).C,(choose source ⟨i,h⟩).parents⟩ : Cell allocation.extra)
      else ⟨returnOffset,1,(choose ret ⟨0,by decide⟩).C,(choose ret ⟨0,by decide⟩).parents⟩) := by
  change (Array.ofFn (fun i : Fin (sourceLength+1)=>if h : i.val<sourceLength then
    (⟨sourceOffset+i.val,1,(choose source ⟨i.val,h⟩).C,(choose source ⟨i.val,h⟩).parents⟩ : Cell allocation.extra)
    else ⟨returnOffset,1,(choose ret ⟨0,by decide⟩).C,(choose ret ⟨0,by decide⟩).parents⟩))[i]'valid=_
  exact Array.getElem_ofFn _

private theorem joint_offset {before tracker S R allocation sourceOffset sourceLength returnOffset}
    (source : Pointwise before tracker S allocation .mut sourceOffset sourceLength)
    (ret : Pointwise before tracker R allocation .ret returnOffset 1) (i : Nat) (valid : i<(jointCells source ret).size) :
    ((jointCells source ret)[i]'valid).offset=(if i<sourceLength then sourceOffset+i else returnOffset) ∧
    ((jointCells source ret)[i]'valid).length=1 := by
  rw [joint_at source ret i valid]
  by_cases h : i<sourceLength <;> simp [h]

private def joined {before tracker S R allocation sourceOffset sourceLength returnOffset}
    (live : Present (ActualWorld before) S.allocation allocation)
    (source : Pointwise before tracker S allocation .mut sourceOffset sourceLength)
    (ret : Pointwise before tracker R allocation .ret returnOffset 1)
    (separate : ∀ byte,Window S.allocation sourceOffset sourceLength byte → Window S.allocation returnOffset 1 byte → False) :
    AllocationCover before where
  id:=S.allocation
  allocation:=allocation
  live:=live
  cells:=jointCells source ret
  disjoint:=by
    intro i j different byte first second
    change Window S.allocation ((jointCells source ret)[i.val]'i.isLt).offset ((jointCells source ret)[i.val]'i.isLt).length byte at first
    change Window S.allocation ((jointCells source ret)[j.val]'j.isLt).offset ((jointCells source ret)[j.val]'j.isLt).length byte at second
    have ai:=joint_offset source ret i.val i.isLt
    have aj:=joint_offset source ret j.val j.isLt
    rw [ai.1,ai.2] at first
    rw [aj.1,aj.2] at second
    have ib : i.val<sourceLength+1 := by simpa only [jointCells,Array.size_ofFn] using i.isLt
    have jb : j.val<sourceLength+1 := by simpa only [jointCells,Array.size_ofFn] using j.isLt
    by_cases a : i.val<sourceLength
    · simp only [ite_eq_left a] at first
      by_cases b : j.val<sourceLength
      · simp only [ite_eq_left b] at second
        apply different
        apply Fin.ext
        have h:=first.2
        have k:=second.2
        omega
      · simp only [ite_eq_right b] at second
        exact separate byte ⟨first.1,by have h:=first.2;omega,by have h:=first.2;omega⟩ second
    · simp only [ite_eq_right a] at first
      by_cases b : j.val<sourceLength
      · simp only [ite_eq_left b] at second
        exact separate byte ⟨second.1,by have h:=second.2;omega,by have h:=second.2;omega⟩ first
      · apply different
        apply Fin.ext
        omega

private def joinedSource {before tracker S R allocation sourceOffset sourceLength returnOffset}
    (live : Present (ActualWorld before) S.allocation allocation)
    (source : Pointwise before tracker S allocation .mut sourceOffset sourceLength)
    (ret : Pointwise before tracker R allocation .ret returnOffset 1)
    (separate : ∀ byte,Window S.allocation sourceOffset sourceLength byte → Window S.allocation returnOffset 1 byte → False)
    (bound : sourceOffset+sourceLength≤allocation.len)
    (ctx : Context before) (member : joined live source ret separate∈ctx.allocations.toList) :
    RoleCover before tracker ctx .mut sourceOffset sourceLength where
  family:=S
  backing:=joined live source ret separate
  backingAt:=member
  id:=rfl
  covered:=by
    intro byte hit
    have small : byte.2-sourceOffset<sourceLength := by have h:=hit.2;omega
    let index : Fin (jointCells source ret).size:=⟨byte.2-sourceOffset,by simp only [jointCells,Array.size_ofFn];omega⟩
    refine ⟨index,?_⟩
    change Window S.allocation ((jointCells source ret)[index.val]'index.isLt).offset ((jointCells source ret)[index.val]'index.isLt).length byte
    rw [joint_at source ret index.val index.isLt]
    simp only [show index.val<sourceLength from small,↓reduceDIte]
    change Window S.allocation (sourceOffset+(byte.2-sourceOffset)) 1 byte
    exact ⟨hit.1,by have h:=hit.2;omega,by have h:=hit.2;omega⟩
  roles:=by
    intro i overlap
    have valid : i.val<(jointCells source ret).size := i.isLt
    by_cases small : i.val<sourceLength
    · let index : Fin sourceLength:=⟨i.val,small⟩
      let chosen:=choose source index
      refine ⟨chosen.grant,chosen.binding,?_,?_⟩
      · change SpatialDelegation before tracker S.allocation allocation ((jointCells source ret)[i.val]'valid).completion chosen.grant
        rw [joint_at source ret i.val valid]
        simp only [small,↓reduceDIte]
        exact chosen.issued
      · intro byte request inside
        change Window S.allocation ((jointCells source ret)[i.val]'valid).offset ((jointCells source ret)[i.val]'valid).length byte at inside
        rw [joint_at source ret i.val valid] at inside
        simp only [small,↓reduceDIte] at inside
        have equal : byte.2=sourceOffset+i.val := by have h:=inside.2;omega
        refine ⟨by have h:=request.2;change byte.2<allocation.len;omega,?_⟩
        change Embeds allocation tracker.global.protectedTags ((jointCells source ret)[i.val]'valid).completion chosen.grant byte.2 .exclusive
        rw [joint_at source ret i.val valid]
        simp only [small,↓reduceDIte]
        rw [equal]
        exact chosen.embeds
    · apply False.elim
      obtain ⟨byte,request,inside⟩:=overlap
      change Window S.allocation ((jointCells source ret)[i.val]'valid).offset ((jointCells source ret)[i.val]'valid).length byte at inside
      rw [joint_at source ret i.val valid] at inside
      simp only [small,↓reduceDIte] at inside
      exact separate byte request inside

private def joinedReturn {before tracker S R allocation sourceOffset sourceLength returnOffset}
    (live : Present (ActualWorld before) S.allocation allocation)
    (source : Pointwise before tracker S allocation .mut sourceOffset sourceLength)
    (ret : Pointwise before tracker R allocation .ret returnOffset 1)
    (same : R.allocation=S.allocation)
    (separate : ∀ byte,Window S.allocation sourceOffset sourceLength byte → Window S.allocation returnOffset 1 byte → False)
    (bound : returnOffset+1≤allocation.len)
    (ctx : Context before) (member : joined live source ret separate∈ctx.allocations.toList) :
    RoleCover before tracker ctx .ret returnOffset 1 where
  family:=R
  backing:=joined live source ret separate
  backingAt:=member
  id:=same
  covered:=by
    intro byte hit
    let index : Fin (jointCells source ret).size:=⟨sourceLength,by simp only [jointCells,Array.size_ofFn];omega⟩
    refine ⟨index,?_⟩
    change Window S.allocation ((jointCells source ret)[index.val]'index.isLt).offset ((jointCells source ret)[index.val]'index.isLt).length byte
    rw [joint_at source ret index.val index.isLt]
    simp only [show ¬index.val<sourceLength from Nat.lt_irrefl _,↓reduceDIte]
    exact hit
  roles:=by
    intro i overlap
    have valid : i.val<(jointCells source ret).size := i.isLt
    by_cases small : i.val<sourceLength
    · apply False.elim
      obtain ⟨byte,request,inside⟩:=overlap
      change Window S.allocation ((jointCells source ret)[i.val]'valid).offset ((jointCells source ret)[i.val]'valid).length byte at inside
      rw [joint_at source ret i.val valid] at inside
      simp only [small,↓reduceDIte] at inside
      exact separate byte ⟨inside.1,by have h:=inside.2;omega,by have h:=inside.2;omega⟩ request
    · let chosen:=choose ret ⟨0,by decide⟩
      refine ⟨chosen.grant,chosen.binding,?_,?_⟩
      · change SpatialDelegation before tracker S.allocation allocation ((jointCells source ret)[i.val]'valid).completion chosen.grant
        rw [joint_at source ret i.val valid]
        simp only [small,↓reduceDIte]
        simpa only [same] using chosen.issued
      · intro byte request inside
        change Window S.allocation ((jointCells source ret)[i.val]'valid).offset ((jointCells source ret)[i.val]'valid).length byte at inside
        rw [joint_at source ret i.val valid] at inside
        simp only [small,↓reduceDIte] at inside
        have equal : byte.2=returnOffset := by have h:=inside.2;omega
        refine ⟨by have h:=request.2;change byte.2<allocation.len;omega,?_⟩
        change Embeds allocation tracker.global.protectedTags ((jointCells source ret)[i.val]'valid).completion chosen.grant byte.2 .exclusive
        rw [joint_at source ret i.val valid]
        simp only [small,↓reduceDIte]
        rw [equal]
        exact chosen.embeds


private theorem actual_present {before : Before} {id : AllocId} {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    Present (ActualWorld before) id entry.allocation := by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩

/-- Positive live source/return assembly. The finite cover contains exactly
singleton request cells; unused bytes are omitted. Proof-cell counts impose no
runtime BorrowTree node-budget condition. Source and return families are fixed
outside every per-byte completion/grant choice. -/
theorem assemble {before tracker}
    (S R : Family) (sourceOffset sourceLength returnOffset : Nat) (_positive : 0<sourceLength)
    (sourceEntry returnEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==S.allocation)=some (S.allocation,sourceEntry))
    (returnLive : before.memory.live.find? (fun row=>row.1==R.allocation)=some (R.allocation,returnEntry))
    (sourceBound : sourceOffset+sourceLength≤sourceEntry.allocation.len)
    (returnBound : returnOffset+1≤returnEntry.allocation.len)
    (sourceRows : Rows sourceEntry.allocation S.allocation sourceOffset sourceLength)
    (returnRows : Rows returnEntry.allocation R.allocation returnOffset 1)
    (Fs Fr : Fragment) (sourceOwner returnOwner : Nat)
    (composable : Composable Fs Fr)
    (sourceCharge : ExactCharge Fs sourceOwner .mut S.allocation sourceOffset sourceLength)
    (returnCharge : ExactCharge Fr returnOwner .ret R.allocation returnOffset 1)
    (source : Pointwise before tracker S sourceEntry.allocation .mut sourceOffset sourceLength)
    (ret : Pointwise before tracker R returnEntry.allocation .ret returnOffset 1) :
    ∃ ctx : Context before,
      ∃ sourceRole : RoleCover before tracker ctx .mut sourceOffset sourceLength,
      ∃ returnRole : RoleCover before tracker ctx .ret returnOffset 1,
        sourceRole.family=S ∧ returnRole.family=R ∧
        sourceRole.backing.allocation=sourceEntry.allocation ∧ returnRole.backing.allocation=returnEntry.allocation ∧
        Rows sourceRole.backing.allocation S.allocation sourceOffset sourceLength ∧
        Rows returnRole.backing.allocation R.allocation returnOffset 1 := by
  have sourcePresent:=actual_present sourceLive
  have returnPresent:=actual_present returnLive
  have separate:=exclusive_separate composable sourceCharge returnCharge
  by_cases same : R.allocation=S.allocation
  · have returnLive' : before.memory.live.find? (fun row=>row.1==S.allocation)=some (S.allocation,returnEntry) := by simpa only [same] using returnLive
    have entryEq : returnEntry=sourceEntry := (Prod.mk.inj (Option.some.inj (returnLive'.symm.trans sourceLive))).2
    subst returnEntry
    have apart : ∀ byte,Window S.allocation sourceOffset sourceLength byte → Window S.allocation returnOffset 1 byte → False := by
      intro byte a b
      exact separate byte a (by simpa only [same] using b)
    let common:=joined sourcePresent source ret apart
    let ctx : Context before:=⟨#[common],by simp⟩
    have member : common∈ctx.allocations.toList := by simp [ctx]
    let sourceRole:=joinedSource sourcePresent source ret apart sourceBound ctx member
    let returnRole:=joinedReturn sourcePresent source ret same apart returnBound ctx member
    exact ⟨ctx,sourceRole,returnRole,rfl,rfl,rfl,rfl,sourceRows,returnRows⟩
  · let sourceBacking:=backing sourcePresent source
    let returnBacking:=backing returnPresent ret
    let ctx : Context before:=⟨#[sourceBacking,returnBacking],by simp [sourceBacking,returnBacking,backing,Ne.symm same]⟩
    have sourceMember : sourceBacking∈ctx.allocations.toList := by simp [ctx]
    have returnMember : returnBacking∈ctx.allocations.toList := by simp [ctx]
    let sourceRole:=role sourcePresent source sourceBound ctx sourceMember
    let returnRole:=role returnPresent ret returnBound ctx returnMember
    exact ⟨ctx,sourceRole,returnRole,rfl,rfl,rfl,rfl,sourceRows,returnRows⟩

/-- Actual map coverage follows from physical extent and map well-formedness,
never from a scalar embedding that could be vacuous outside represented rows. -/
theorem rows_of_bound {before tracker id allocation offset length}
    (cap : AllocationCapability before tracker id allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global)
    (bound : offset+length≤allocation.len) : Rows allocation id offset length := by
  intro byte hit
  have inside : byte.2<allocation.extra.locations.size.bytes.toNat := by
    rw [cap.treeExtent,←cap.extent]
    have h:=hit.2
    omega
  have fits : byte.2<2^64 := Nat.lt_trans inside (UInt64.toNat_lt _)
  have valueEq : (UInt64.ofNat byte.2).toNat=byte.2 := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  obtain ⟨index,valid,lower,upper⟩:=GeneralRangeMapGeometry.covered allocation.extra.locations runtime.formed.well
    (UInt64.ofNat byte.2) (by rw [valueEq];exact inside)
  exact ⟨allocation.extra.locations.entries[index],Array.mem_toList_iff.mpr (Array.getElem_mem valid),by rwa [valueEq] at lower,by rwa [valueEq] at upper⟩

def Chained (tracker : MachineHooks.BorrowState)
    (family : Family) (allocation : Allocation Provenance BorrowTree) (mode : Mode) (offset length : Nat) : Prop :=
  ∀ byte,Window family.allocation offset length byte → ∃ grant,
    ∃ chain : CurrentCallSupportChain.Chain allocation.extra grant,
      PointerBinds allocation (family.at grant) ∧
      CurrentCallSupportChain.Carries allocation tracker.global.protectedTags chain byte.2 (demandOf mode)

theorem pointwise_of_chains {before tracker family allocation mode offset length}
    (cap : AllocationCapability before tracker family.allocation allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder allocation.extra)
    (distinct : allocation.extra.roots.toList.Nodup)
    (raw : Chained tracker family allocation mode offset length) :
    Pointwise before tracker family allocation mode offset length := by
  intro byte hit
  obtain ⟨grant,chain,binding,support⟩:=raw byte hit
  obtain ⟨C,parents,binding,issued,embeds⟩:=CurrentCallSupportChain.adequate cap runtime order distinct
    (family.at grant) rfl binding chain byte.2 (demandOf mode) support
  exact ⟨C,grant,parents,binding,issued,embeds⟩

/-- The raw-chain presentation adds no restriction to the existing sufficient
pointwise resource witnesses. This direction derives no physical bounds. -/
theorem chains_of_pointwise {before tracker family allocation mode offset length}
    (points : Pointwise before tracker family allocation mode offset length) :
    Chained tracker family allocation mode offset length := by
  intro byte hit
  obtain ⟨C,grant,parents,binding,issued,embeds⟩:=points byte hit
  obtain ⟨chain,_,support⟩:=CurrentCallSupportChainExtraction.extract_support parents issued embeds
  exact ⟨grant,chain,binding,support⟩

theorem pointwise_of_role {before tracker ctx mode offset length}
    (existing : RoleCover before tracker ctx mode offset length) :
    Pointwise before tracker existing.family existing.backing.allocation mode offset length := by
  intro byte hit
  have request : Window existing.backing.id offset length byte := by simpa only [existing.id] using hit
  obtain ⟨i,inside⟩:=existing.covered byte request
  let cellRole:=existing.roles i ⟨byte,request,inside⟩
  exact ⟨existing.backing.cells[i].completion,cellRole.grant,existing.backing.cells[i].parents,cellRole.binding,
    by simpa only [existing.id] using cellRole.issued,(cellRole.available byte request inside).2⟩

/-- Raw-chain corollary with current scalar realization and root licensing.
Physical bounds supply byte availability and ACTUAL row coverage separately. -/
theorem assemble_chains {before tracker}
    (S R : Family) (sourceOffset sourceLength returnOffset : Nat) (positive : 0<sourceLength)
    (sourceEntry returnEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==S.allocation)=some (S.allocation,sourceEntry))
    (returnLive : before.memory.live.find? (fun row=>row.1==R.allocation)=some (R.allocation,returnEntry))
    (sourceBound : sourceOffset+sourceLength≤sourceEntry.allocation.len)
    (returnBound : returnOffset+1≤returnEntry.allocation.len)
    (Fs Fr : Fragment) (sourceOwner returnOwner : Nat)
    (composable : Composable Fs Fr)
    (sourceCharge : ExactCharge Fs sourceOwner .mut S.allocation sourceOffset sourceLength)
    (returnCharge : ExactCharge Fr returnOwner .ret R.allocation returnOffset 1)
    (sourceCap : AllocationCapability before tracker S.allocation sourceEntry.allocation)
    (returnCap : AllocationCapability before tracker R.allocation returnEntry.allocation)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global)
    (returnRuntime : DuplicatePrefixBorrowContract.RuntimeFacts returnEntry.allocation.extra tracker.global)
    (sourceOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra)
    (returnOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder returnEntry.allocation.extra)
    (sourceDistinct : sourceEntry.allocation.extra.roots.toList.Nodup)
    (returnDistinct : returnEntry.allocation.extra.roots.toList.Nodup)
    (source : Chained tracker S sourceEntry.allocation .mut sourceOffset sourceLength)
    (ret : Chained tracker R returnEntry.allocation .ret returnOffset 1) :
    ∃ ctx : Context before,
      ∃ sourceRole : RoleCover before tracker ctx .mut sourceOffset sourceLength,
      ∃ returnRole : RoleCover before tracker ctx .ret returnOffset 1,
        sourceRole.family=S ∧ returnRole.family=R ∧
        sourceRole.backing.allocation=sourceEntry.allocation ∧ returnRole.backing.allocation=returnEntry.allocation ∧
        Rows sourceRole.backing.allocation S.allocation sourceOffset sourceLength ∧
        Rows returnRole.backing.allocation R.allocation returnOffset 1 := by
  exact assemble S R sourceOffset sourceLength returnOffset positive sourceEntry returnEntry sourceLive returnLive
    sourceBound returnBound (rows_of_bound sourceCap sourceRuntime sourceBound) (rows_of_bound returnCap returnRuntime returnBound)
    Fs Fr sourceOwner returnOwner composable sourceCharge returnCharge
    (pointwise_of_chains sourceCap sourceRuntime sourceOrder sourceDistinct source)
    (pointwise_of_chains returnCap returnRuntime returnOrder returnDistinct ret)


end
end DuplicatePrefix.CurrentCallPointwiseSpatialCover
