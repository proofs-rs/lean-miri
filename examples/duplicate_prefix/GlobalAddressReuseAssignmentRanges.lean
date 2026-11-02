import duplicate_prefix.GlobalAddressReuseFreeHoles
namespace DuplicatePrefix.GlobalAddressReuseAssignmentRanges
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressRangeFormation GlobalAddressAlignedBumpFormation GlobalAddressReuseContents GlobalAddressReuseHoleGeometry WildcardEmptyFamilyFormation
open GlobalAddressBumpRangeFormation (Frontier)
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.split false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem returned (staged : GlobalAddressState) (id : AllocId) (address : UInt64) (sizes : AllocId → Size)
    (good : Apart (staged.cacheAddress id address).state.intToPtrMap sizes) :
    Apart (match (staged.cacheAddress id address).outcome with
      | .ok _ => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id address).state,.ok (.ready address)⟩)
      | .error error => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id address).state,.error error⟩)).state.intToPtrMap sizes := by
  cases (staged.cacheAddress id address).outcome <;> exact good

/-- The actual managed address operation preserves nonoverlap for EVERY
reuse/generation outcome. Actual reuse holes supply their insertion geometry;
fresh fallback uses actual checked align-up and the cursor frontier. No
successful take, generator, cache or assignment is an input premise. -/
theorem assign (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId → Size)
    (initial : Apart addresses.intToPtrMap sizes) (ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap)
    (frontier : Frontier addresses.intToPtrMap sizes generation.generator)
    (holes : Contents generation.reusePool (Hole addresses.intToPtrMap sizes))
    (managed : addresses.addressMode=.managed) (generationEq : addresses.generation=some generation)
    (cursor : generation.generator.nextBaseAddr≠0) (id : AllocId) (size : Size) (sizeEq : sizes id=size)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (align : Align) (valid : align.pow2≤29) (kind : AddressMemoryKind) (thread : AddressThreadId) (choices : AddressRandomChoices)
    (room : Room generation.generator size align choices.slack) :
    Apart (addresses.addrFromAllocId id (some (GlobalAddressAlignedManagedFormation.info size align kind thread)) choices).state.intToPtrMap sizes := by
  have takeFacts:=take_separated generation.reusePool addresses.intToPtrMap sizes holes ordered id size sizeEq
    choices.reuse choices.crossThread choices.poolIndex align kind thread
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,managed,generationEq,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  cases outcome : (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread).outcome with
  | error error => exact initial
  | ok optional =>
    try dsimp only
    cases optional with
    | none =>
      try dsimp only
      have bump:=generated generation.generator size align valid choices.slack room
      simp only [bump]
      have geometry:=placement addresses.intToPtrMap sizes generation.generator frontier id size align valid choices.slack room
      have positive : base generation.generator align choices.slack≠0 := by
        intro zero
        have lower:=(base_bounds generation.generator size align valid choices.slack room).1
        rw [zero] at lower
        change generation.generator.nextBaseAddr.toNat+choices.slack.val≤0 at lower
        have nz : generation.generator.nextBaseAddr.toNat≠0 := by intro eq;exact cursor (UInt64.toNat_inj.mp eq)
        omega
      simp only [←managed]
      let staged : GlobalAddressState := {addresses with generation:=some ⟨next generation.generator size align choices.slack,
        if (next generation.generator size align choices.slack).nextBaseAddr > (next generation.generator size align choices.slack).endAddr/2 then
          ((generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread).state).addressSpaceShortage
        else (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread).state⟩}
      change Apart (match (staged.cacheAddress id (base generation.generator align choices.slack)).outcome with
        | .ok _ => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id (base generation.generator align choices.slack)).state,.ok (.ready (base generation.generator align choices.slack))⟩)
        | .error error => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id (base generation.generator align choices.slack)).state,.error error⟩)).state.intToPtrMap sizes
      exact returned staged id _ sizes (cache staged sizes initial id _ uncached positive _ geometry.1 geometry.2).2
    | some used =>
      try dsimp only
      obtain ⟨positive,cut,partition,placement⟩:=takeFacts.2 used outcome
      cases clock : used.clockToAcquire with
      | some clock => exact initial
      | none =>
        simp only [←managed]
        let staged : GlobalAddressState := {addresses with generation:=some {generation with reusePool:=
          (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread).state}}
        change Apart (match (staged.cacheAddress id used.address).outcome with
          | .ok _ => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id used.address).state,.ok (.ready used.address)⟩)
          | .error error => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id used.address).state,.error error⟩)).state.intToPtrMap sizes
        exact returned staged id _ sizes (cache staged sizes initial id _ uncached positive cut partition placement).2
end DuplicatePrefix.GlobalAddressReuseAssignmentRanges
