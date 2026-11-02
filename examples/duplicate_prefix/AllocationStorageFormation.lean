import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.InitMaskCopy
import duplicate_prefix.ProvenanceCopy
namespace DuplicatePrefix.AllocationStorageFormation
open Miri.ABI Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

open Lean Elab Command in
run_cmd do
  for (suffix, aliasName) in [
    (".Miri.Memory.firstNonZero", `DuplicatePrefix.AllocationStorageFormation.firstNonZero),
    (".Miri.Memory.checkedAlign", `DuplicatePrefix.AllocationStorageFormation.checkedAlign)] do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix && name.toString.startsWith "_private.Miri.Memory.Allocation." then some name else none
    let [name] := found | throwError "expected one source definition {suffix}"
    let info ← getConstInfo name
    liftCoreM <| addAndCompile <| .defnDecl {
      name := aliasName
      levelParams := info.levelParams
      type := info.type
      value := mkConst name (info.levelParams.map Level.param)
      hints := .regular 0
      safety := .safe }

def scan (bytes : Array UInt8) (index : Nat) (_ : Option (Option (Nat × UInt8)) × Unit) :
    Id (ForInStep (Option (Option (Nat × UInt8)) × Unit)) :=
  match bytes[index]? with
  | some byte => if byte != 0 then pure (.done (some (some (index,byte)),())) else pure (.yield (none,()))
  | none => pure (.done (some (some (index,0)),()))

theorem scan_zero (bytes : Array UInt8) (indices : List Nat)
    (valid : ∀ i∈indices,i<bytes.size) (zero : ∀ i (h : i<bytes.size),bytes[i]=0) :
    forIn indices (none,()) (scan bytes)= (none,()) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have bounded := valid i (by simp)
    have get : bytes[i]?=some 0 := by simp [bounded,zero i bounded]
    simp only [List.forIn_cons,scan,get,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    exact ih (fun j member=>valid j (by simp [member]))

theorem zero_scan (bytes : Array UInt8) (zero : ∀ i (h : i<bytes.size),bytes[i]=0) :
    firstNonZero bytes=none := by
  unfold firstNonZero
  unfold_internal ".Memory.firstNonZero"
  simp only [Id.run,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (do
    let result ← forIn (List.range' 0 bytes.size) (none,()) (scan bytes)
    pure (result.1.getD none) : Id (Option (Nat × UInt8)))=none
  rw [scan_zero bytes _ (by intro i member;have := List.mem_range'.mp member;omega) zero]
  rfl

/-- Actual allocation backing creation for byte-aligned slices. The host
resource supplies the requested zeroed byte array; alignment, length and zero
checks are executed by the unchanged source. No allocation-success premise is
required. This covers backing creation, not ID reservation or machine hooks. -/
theorem create (size : Size) (init : AllocInit) (bytes : Array UInt8)
    (storage : Size→Align→Option (Array UInt8))
    (provided : storage size Align.ONE=some bytes)
    (length : bytes.size=size.bytes.toNat)
    (zero : ∀ i (h : i<bytes.size),bytes[i]=0) :
    ∃ allocation : Allocation Prov Unit,
      Allocation.tryNew size Align.ONE init storage=.ok allocation ∧
      allocation.len=size.bytes.toNat ∧ allocation.byteSize=size ∧
      allocation.provenanceMap=ProvenanceMap.new ∧
      allocation.initializationMask=InitMask.new size (init==.Zero) ∧
      allocation.mutability=.Mut ∧ allocation.align=Align.ONE ∧
      allocation.nativeBuffer=none := by
  have checked : checkedAlign Align.ONE=.ok Align.ONE := by decide
  unfold checkedAlign at checked
  have scanned := zero_scan bytes zero
  unfold firstNonZero at scanned
  simp only [Allocation.tryNew,checked,bind,pure,Except.bind,provided,length,bne_self_eq_false,
    Bool.false_eq_true,↓reduceIte,scanned,Except.pure]
  cases init <;> exact ⟨_,rfl,length,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- An actual initialized backing supplies the mask/provenance/storage part of
whole-call input contracts, independently of borrow-history formation. -/
theorem initialized (size : Size) (bytes : Array UInt8)
    (storage : Size→Align→Option (Array UInt8))
    (provided : storage size Align.ONE=some bytes)
    (length : bytes.size=size.bytes.toNat)
    (zero : ∀ i (h : i<bytes.size),bytes[i]=0) :
    ∃ allocation : Allocation Prov Unit,
      Allocation.tryNew size Align.ONE .Zero storage=.ok allocation ∧
      allocation.len=allocation.byteSize.bytes.toNat ∧ allocation.byteSize=size ∧
      InitMaskCopy.WellFormed allocation.initializationMask ∧
      allocation.initializationMask.len=allocation.byteSize ∧
      (∀ start finish,InitMaskCopy.InitializedOn allocation.initializationMask start finish) ∧
      ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len ∧
      allocation.mutability=.Mut := by
  obtain ⟨allocation,created,len,sizeEq,provenance,mask,mutable,_,_⟩ :=
    create (Prov:=Prov) size .Zero bytes storage provided length zero
  have maskEq : allocation.initializationMask=InitMask.new size true := mask
  refine ⟨allocation,created,by rw [sizeEq];exact len,sizeEq,?_,?_,?_,?_,mutable⟩
  · rw [maskEq];exact True.intro
  · rw [maskEq,sizeEq];rfl
  · intro start finish;rw [maskEq];rfl
  · rw [provenance]
    constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
end DuplicatePrefix.AllocationStorageFormation
