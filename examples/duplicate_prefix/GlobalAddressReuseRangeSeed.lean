import duplicate_prefix.GlobalAddressReuseCompleteRanges
import duplicate_prefix.GlobalAddressGcRangeResources
namespace DuplicatePrefix.GlobalAddressReuseRangeSeed
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressRangeResources GlobalAddressBumpRangeFormation GlobalAddressReuseContents GlobalAddressReuseHoleGeometry
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual source address/reuse-pool initialization jointly forms the recurring
range/size resources, cursor frontier and stored-hole separation certificate.
No final geometry or pool-availability field is an input premise. -/
theorem new {K} (memory : MemoryState Provenance BorrowTree K) (sizes : AllocId → Size)
    (mode : ProvenanceMode) (start stop : UInt64) (config : AddressReuseConfig)
    (reuse : (Float.le 0.0 config.addressReuseRate && Float.le config.addressReuseRate 1.0)=true)
    (cross : (Float.le 0.0 config.addressReuseCrossThreadRate && Float.le config.addressReuseCrossThreadRate 1.0)=true) :
    ∃ addresses generation, GlobalAddressState.new mode .managed start stop config = .ok addresses ∧
      addresses.generation=some generation ∧ State memory addresses sizes ∧
      Frontier addresses.intToPtrMap sizes generation.generator ∧
      Contents generation.reusePool (Hole addresses.intToPtrMap sizes) := by
  let generation : AddressGenerationState := ⟨AddressGenerator.new start stop,⟨config.addressReuseRate,config.addressReuseCrossThreadRate,#[]⟩⟩
  let addresses : GlobalAddressState := ⟨#[],#[],#[],mode,.managed,some generation,#[]⟩
  have source : GlobalAddressState.new mode .managed start stop config = .ok addresses := by
    unfold GlobalAddressState.new ReusePool.new
    unfold_internal ".ReusePool.validRate"
    simp only [reuse,cross,Bool.not_true,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,Except.mapError,bind,Except.bind,pure,Except.pure]
    rfl
  obtain ⟨other,actual,resources,frontier⟩:=GlobalAddressRangeResources.seed memory sizes mode start stop config reuse cross
  have same : other=addresses:=Except.ok.inj (actual.symm.trans source)
  subst other
  refine ⟨addresses,generation,source,rfl,resources,frontier,?_⟩
  intro bucket member
  change bucket∈(#[] : Array (Array ReusableAddress)) at member
  simp only [Array.not_mem_empty] at member
end DuplicatePrefix.GlobalAddressReuseRangeSeed
