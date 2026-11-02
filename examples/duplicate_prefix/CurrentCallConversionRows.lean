import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.GlobalRelocationFiniteConversion
namespace DuplicatePrefix.CurrentCallConversionRows
open Miri Miri.ABI Miri.Memory
open GlobalRelocationFiniteLoop
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Only input position/provenance and source bytes matter here. The base/root
fields are unused format placeholders, not claims about runtime roots/caches. -/
def row (source : Allocation CtfeProvenance Unit) (input : Size × CtfeProvenance) : Row :=
  ⟨input.1,input.2,0,BorTag.one,fun i=>((AllocationCopy.snapshot source)[input.1.bytes.toNat+i.val]?).getD 0⟩

def rows (source : Allocation CtfeProvenance Unit) : List Row := source.provenanceMap.ptrs.toList.map (row source)

private theorem snapshot_size (source : Allocation CtfeProvenance Unit) : (AllocationCopy.snapshot source).size=source.len := by
  cases source
  simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,pure,Pure.pure,Except.pure,Except.toOption]

private theorem window (raw : Array UInt8) (start : Nat) (bounds : start+8≤raw.size) :
    raw.extract start (start+8)=GlobalRelocationWordDecode.bytes (fun i=>raw[start+i.val]?.getD 0) := by
  apply Array.ext
  · simp only [Array.size_extract,Nat.min_eq_left bounds,Nat.add_sub_cancel_left,GlobalRelocationWordDecode.bytes,List.size_toArray,List.length_cons,List.length_nil]
  · intro i left right
    have inside : i<8:=by simpa only [Array.size_extract,Nat.min_eq_left bounds,Nat.add_sub_cancel_left] using left
    have fit : start+i<raw.size:=by omega
    have value : raw[start+i]=raw[start+i]?.getD 0:=by rw [Array.getElem?_eq_getElem fit,Option.getD_some]
    have f0 : (0 : Fin 8).val=0:=rfl
    have f1 : (1 : Fin 8).val=1:=rfl
    have f2 : (2 : Fin 8).val=2:=rfl
    have f3 : (3 : Fin 8).val=3:=rfl
    have f4 : (4 : Fin 8).val=4:=rfl
    have f5 : (5 : Fin 8).val=5:=rfl
    have f6 : (6 : Fin 8).val=6:=rfl
    have f7 : (7 : Fin 8).val=7:=rfl
    have cases : i=0 ∨i=1 ∨i=2 ∨i=3 ∨i=4 ∨i=5 ∨i=6 ∨i=7:=by omega
    rcases cases with rfl |rfl |rfl |rfl |rfl |rfl |rfl |rfl
    all_goals simpa [Array.getElem_extract,GlobalRelocationWordDecode.bytes,f0,f1,f2,f3,f4,f5,f6,f7] using value

/-- Deterministic extraction from the actual finite source map. The map's
existing fixed-width well-formedness supplies all eight-byte bounds/order;
no cached relocation target, callback status, or execution premise is used. -/
theorem extract (source : Allocation CtfeProvenance Unit)
    (valid : ProvenanceCopy.WellFormed source.provenanceMap source.len) :
    (rows source).map input=source.provenanceMap.ptrs.toList ∧
    (rows source).Pairwise Separate ∧
    (∀r∈rows source,r.position.bytes.toNat+8≤(AllocationCopy.snapshot source).size) ∧
    ∀r∈rows source,(AllocationCopy.snapshot source).extract r.position.bytes.toNat (r.position.bytes.toNat+8)=GlobalRelocationWordDecode.bytes r.word := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [rows,List.map_map,input,row,Function.comp_def,Prod.eta]
    exact List.map_id _
  · simpa only [rows,List.pairwise_map,Separate,row] using (ProvenanceCopy.WellFormed.pointerOrder (self:=source.provenanceMap) (capacity:=source.len) valid)
  · intro r member
    change r∈source.provenanceMap.ptrs.toList.map (row source) at member
    obtain ⟨item,itemMember,same⟩:=List.mem_map.mp member
    subst r
    rw [snapshot_size]
    exact ProvenanceCopy.WellFormed.pointerBounds (self:=source.provenanceMap) (capacity:=source.len) valid item (Array.mem_toList_iff.mp itemMember)
  · intro r member
    change r∈source.provenanceMap.ptrs.toList.map (row source) at member
    obtain ⟨item,itemMember,same⟩:=List.mem_map.mp member
    subst r
    exact window (AllocationCopy.snapshot source) item.1.bytes.toNat
      (by rw [snapshot_size];exact ProvenanceCopy.WellFormed.pointerBounds (self:=source.provenanceMap) (capacity:=source.len) valid item (Array.mem_toList_iff.mp itemMember))

theorem of_storage (source : Allocation CtfeProvenance Unit) (storage : CurrentCallOrdinaryInput.Storage source) :
    (rows source).map input=source.provenanceMap.ptrs.toList ∧
    (rows source).Pairwise Separate ∧
    (∀r∈rows source,r.position.bytes.toNat+8≤(AllocationCopy.snapshot source).size) ∧
    ∀r∈rows source,(AllocationCopy.snapshot source).extract r.position.bytes.toNat (r.position.bytes.toNat+8)=GlobalRelocationWordDecode.bytes r.word :=
  extract source storage.2.2.2
end DuplicatePrefix.CurrentCallConversionRows
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionRows" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual conversion row dependency {dependency}"
