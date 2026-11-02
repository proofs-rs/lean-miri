import duplicate_prefix.S05ZeroCellContractQuery
import duplicate_prefix.DuplicatePrefixReferenceInput
import duplicate_prefix.S05ConsistentCallSpecification

/-! The accepted closed finite caller lies outside the existing conservative
contract. Only its reference field is inspected; no resource/frame/metadata
constructor, actual-call outcome or NoUB claim is involved. -/
namespace DuplicatePrefix.S05ZeroCellContractExclusion
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter Miri.Input
open S05ZeroCellTypedGeneratedPrefix
open S05ZeroCellJointPacket
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-- Every existential choice in this concrete positive-reference interface is
forced by the supplied pointer, live row, base row and actual ancestor path. -/
theorem no_positive_reference
    (input : DuplicatePrefixReferenceInput.Positive before sourcePointer 2) : False := by
  rcases input with ⟨tracker,enabled,id,entry,base,offset,capacity,live,cached,
    address,nonnull,fits,size,bytes,mutable,storage,provenance,borrowSize,
    source,selectedRoot,maximum,binding,borrow⟩
  change sourceId = id ∧ ∃ anchor, source = some anchor ∧
    entry.allocation.extra.indexOfTag (tag 6) = some anchor at binding
  obtain ⟨idEq,anchor,sourceEq,anchorEq⟩ := binding
  subst id
  have entryEq : entry = sourceEntry :=
    (Prod.mk.inj (Option.some.inj (live.symm.trans source_present))).2
  subst entry
  have baseEq : base = 4096 := by
    have same := Option.some.inj (cached.symm.trans source_cached)
    exact congrArg (fun row => row.address) same
  subst base
  have offsetEq : offset = 0 := by
    change (4096 : UInt64) = 4096 + offset at address
    have same : (4096 : UInt64) + 0 = 4096 + offset := by simpa using address
    exact (UInt64.add_right_inj 4096).mp same.symm
  subst offset
  have trackerEq : tracker = ⟨{nextPointerTag := tag 8, rootPointerTags := #[(sourceId,tag 1),(destinationId,tag 7)]},.Default⟩ :=
    Option.some.inj enabled.symm
  subst tracker
  have actualAnchor : sourceEntry.allocation.extra.indexOfTag (tag 6) = some (ix 5) := by cbv
  have anchorSame : anchor = ix 5 := Option.some.inj (anchorEq.symm.trans actualAnchor)
  subst anchor
  subst source
  have valid : 0 < sourceEntry.allocation.extra.locations.entries.size := by cbv
  have start : (sourceEntry.allocation.extra.locations.entries[0]'valid).range.start.toNat < (2 : UInt64).toNat := by cbv
  have stop : (0 : UInt64).toNat < (sourceEntry.allocation.extra.locations.entries[0]'valid).range.stop.toNat := by cbv
  obtain ⟨row⟩ := borrow.rows 0 valid (by decide) start stop
  have path := row.rootPath (ix 5) rfl
  have actualPath : ((source_normal_projection
      sourceEntry.allocation.extra S05ZeroCellContractQuery.location {}).topology.ancestorPath (ix 5).toNat).getLast? = some 3 := by cbv
  have rootNat : selectedRoot.map UniIndex.toNat = some 3 := path.symm.trans actualPath
  have rootEq : selectedRoot = some (ix 3) := by
    cases selectedRoot with
    | none => cases rootNat
    | some index =>
      have numeric : index.toNat = 3 := Option.some.inj rootNat
      have indexEq : index = ix 3 := by
        cases index with
        | mk value =>
          congr 1
          exact UInt32.toNat_inj.mp numeric
      exact congrArg some indexEq
  subst selectedRoot
  have maxEq : maximum = some (tag 4) := by
    exact row.cutoff.trans (by cbv)
  subst maximum
  exact S05ZeroCellContractQuery.no_row row

/-- The existing Contract excludes this caller solely through its conservative
positive borrow interface. This does not reverse its joint-authority admission. -/
theorem no_contract (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (input : DuplicatePrefixCallSpecification.Contract options limits remaining span before argument 2 place) : False := by
  cases input.reference with
  | empty zero _ => cases zero
  | positive pointer encoding positive =>
    have same : pointer = sourcePointer := (DuplicatePrefixSliceArgument.Argument.pointer.inj encoding).symm
    subst pointer
    exact no_positive_reference positive

/-- A wrapper cannot restore a Contract whose reference field is impossible. -/
theorem no_consistent_contract (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    ¬ Nonempty (S05ConsistentCallSpecification.ConsistentContract options limits remaining span before argument 2 place) := by
  rintro ⟨input⟩
  exact no_contract options limits remaining span input.contract

end DuplicatePrefix.S05ZeroCellContractExclusion
