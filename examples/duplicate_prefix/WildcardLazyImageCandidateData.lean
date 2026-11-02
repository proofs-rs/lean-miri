import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.WildcardLazyGlobalResolve
import duplicate_prefix.StaticGlobalAllocInfo

namespace DuplicatePrefix.WildcardLazyImageCandidateData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- Source witnesses are extracted from the actual-context candidate unchanged.
No successful materialization or later state is an input. -/
structure Data (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) where
  source : Allocation CtfeProvenance Unit
  root : BorTag
  absent : before.memory.live.find? (fun row => row.1 == id) = none
  noFunction : before.memory.hasFunctionPointer id = false
  noVaList : before.memory.hasVaListId id = false
  descriptor : before.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩ ∨
    ∃ definition, PreparedReflection.actual.image.initializers.find? (·.1 == definition) = some (definition,source) ∧
      before.memory.findGlobal? id = some
        ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩
  rootCached : tracker.global.rootTag? id = some root
  noExtras : (before.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false
  supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
    before.memory tracker.global.rootPointerTags before.user.addresses.baseAddr

theorem extract (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : Option BorTag)
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before tracker)
      before.memory before.user.addresses id tag) : Nonempty (Data options before tracker id) := by
  rcases candidate with ⟨source,root,absent,noFunction,noVaList,descriptor,rootCached,tagEq,noExtras,native,supported⟩
  refine ⟨⟨source,root,absent,noFunction,noVaList,descriptor,rootCached,?_,supported⟩⟩
  change ((before.user.payload.payload.user.runtime.extras.allocations.map Prod.fst).contains id) = false at noExtras
  have symmetry {A : Type} (rows : Array (AllocId × A)) :
      rows.any (fun row => id == row.1) = rows.any (fun row => row.1 == id) := by
    congr 1
    funext row
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact eq_comm
  rw [←symmetry]
  simpa only [Array.contains_eq_any_beq,Array.any_map,Function.comp_def] using noExtras

theorem alloc_info (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (data : Data options before tracker id) :
    before.memory.getAllocInfo id = .ok ⟨data.source.byteSize,data.source.align,.liveData,data.source.mutability⟩ := by
  rcases data.descriptor with memory | ⟨definition,initializer,static⟩
  · exact GlobalDataOnlyMaterialize.alloc_info before id data.source data.absent data.noFunction data.noVaList memory
  · exact StaticGlobalAllocInfo.alloc_info before id data.source definition data.absent data.noFunction data.noVaList static

theorem geometry (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (data : Data options before tracker id)
    (info : AllocationInfo) (known : before.memory.getAllocInfo id = .ok info)
    (address base : UInt64)
    (hit : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap address base id info.size) :
    WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap address base id data.source.byteSize := by
  have eq := Except.ok.inj (known.symm.trans (alloc_info options before tracker id data))
  cases eq
  exact hit

theorem exposed_live (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState)
    (wildcard : DuplicatePrefixEmptyReferenceInput.Wildcard (imageContext options before tracker)
      before.memory before.user.addresses) (id : AllocId)
    (exposed : before.user.addresses.exposed.contains id = true) : before.memory.isAllocLive id = true := by
  exact wildcard.coherent.live.2 id (by simpa using exposed)

theorem root_below (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (resources : Resources options limits remaining before tracker len)
    (id : AllocId) (data : Data options before tracker id) :
    data.root.value.toNat < tracker.global.nextPointerTag.value.toNat := by
  have cached := data.rootCached
  unfold GlobalState.rootTag? at cached
  cases found : tracker.global.rootPointerTags.find? (fun row => row.1 == id) with
  | none => simp only [found,Option.map_none] at cached; contradiction
  | some row =>
    have rootEq : row.2 = data.root := by simpa only [found,Option.map_some,Option.some.injEq] using cached
    have member : row ∈ tracker.global.rootPointerTags.toList := by
      exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found)
    simpa only [rootEq] using resources.cachedRootsBelow row member

theorem root_distinct (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (resources : Resources options limits remaining before tracker len)
    (id : AllocId) (data : Data options before tracker id) :
    data.root ≠ tracker.global.nextPointerTag := by
  intro equal
  have below := root_below options limits remaining before tracker len resources id data
  rw [equal] at below
  exact Nat.lt_irrefl _ below

theorem cached_hit (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState)
    (wildcard : DuplicatePrefixEmptyReferenceInput.Wildcard (imageContext options before tracker)
      before.memory before.user.addresses) (id : AllocId) (address base : UInt64) (size : Size)
    (hit : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap address base id size)
    (exposed : before.user.addresses.exposed.contains id = true) :
    before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
  have member : (⟨base,id⟩ : Miri.Memory.AllocAddresses.InverseAddressEntry) ∈ before.user.addresses.intToPtrMap := by
    rcases hit with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
    · exact Array.mem_of_getElem? row
    · exact Array.mem_of_getElem? row
  exact wildcard.cached ⟨base,id⟩ member exposed

theorem tag_fresh (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (resources : Resources options limits remaining before tracker len) :
    tracker.global.nextPointerTag.value < 18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  have room := resources.tagRoom
  change tracker.global.nextPointerTag.value.toNat < 18446744073709551615
  omega

end DuplicatePrefix.WildcardLazyImageCandidateData
