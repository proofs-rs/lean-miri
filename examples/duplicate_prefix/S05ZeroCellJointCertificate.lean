import duplicate_prefix.S05ZeroCellTypedGeneratedPrefix
import duplicate_prefix.GeneralBorrowExposedConditionalWritePermissions
import duplicate_prefix.S05ZeroCellJointPhysical
import duplicate_prefix.S05ZeroCellWildcardCast

/-! Finite joint authority for this one generated caller.  The static guards
below read one precise state; no access-success or future Result defines them.
This is not a definition or coverage theorem for all ordinary callers. -/
namespace DuplicatePrefix.S05ZeroCellJointCertificate
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open S05ZeroCellTypedGeneratedPrefix
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def raw : BorrowTree := w.tree
def precise : BorrowTree := preciseW.tree
def preciseLocation : LocationTree :=
  (precise.locations.entries[0]'(by cbv)).data

theorem node_shape : precise.nodes.data.size = 6 ∧
    precise.nodes.data.all Option.isSome = true := by cbv <;> decide +kernel

/-- The default is unused: node_shape proves every one of the six slots exists. -/
def node (i : Fin 6) : TreeNode :=
  (precise.nodeAt (ix i.val)).getD ⟨tag 1,none,#[],.Disabled,.None,false,none⟩

def state (i : Fin 6) : LocationState :=
  (preciseLocation.perms.get (ix i.val)).getD (node i).defaultLocationState

/-- Project only the static fields used by the permission tables. -/
theorem static_projection :
    (Array.ofFn fun i : Fin 6 => ((state i).possible,(state i).permission,(state i).accessed)) =
      #[(true,.Unique,true),(true,.Cell,true),(true,.Disabled,true),
        (true,.Cell,true),(true,.ReservedFrz false,false),(true,.ReservedFrz false,true)] := by cbv <;> decide +kernel

/-- Both bytes use this same precise location and the same raw location. -/
theorem common_window :
    precise.locations.entries.size = 1 ∧
    (precise.locations.entries[0]'(by cbv)).range = ⟨0,2⟩ ∧
    raw.locations.entries.size = 1 ∧
    (raw.locations.entries[0]'(by cbv)).range = ⟨0,2⟩ := by cbv <;> decide +kernel

/-- The full W ancestry terminates at original1: W6, B4, original1. -/
theorem w_ancestor_chain :
    precise.nthParent (tag 6) 0 = .ok (tag 6) ∧
    precise.nthParent (tag 6) 1 = .ok (tag 4) ∧
    precise.nthParent (tag 6) 2 = .ok (tag 1) ∧
    precise.nthParent (tag 6) 3 = .error (.missingParent (tag 6) 3) := by cbv <;> decide +kernel

/-- Parent edges of EVERY precise node, derived from the generated tree. -/
theorem parents :
    precise.nodes.data.map (Option.map TreeNode.parent) =
      #[some none,some (some (ix 0)),some (some (ix 1)),
        some (some (ix 0)),some (some (ix 2)),some (some (ix 3))] := by cbv <;> decide +kernel

/-- The source Local/Foreign Write guards for all six nodes, with the actual
empty protector set. Ancestors are original1/B4/W6; competitors A2/D3/V5 are
checked in this SAME precise state, not in separate successful executions. -/
theorem static_joint_permissions : ∀ i : Fin 6,
    (state i).possible = true ∧
    let held := ({} : ProtectedTags).contains (node i).tag
    if i.val = 0 ∨ i.val = 3 ∨ i.val = 5 then
      (state i).permission ≠ .Disabled ∧ (state i).permission ≠ .Frozen ∧
      (held = true → (state i).permission ≠ .ReservedFrz true)
    else
      (held = true → (state i).permission = .Cell ∨
        ((state i).permission ≠ .ReservedIM ∧ (state i).accessed = false)) := by
  intro i
  have table := congrArg (fun rows : Array (Bool × Permission × Bool) => (rows[i.val]?).getD (false,.Disabled,false)) static_projection
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some] at table
  have possible := congrArg Prod.fst table
  have permission := congrArg (fun row : Bool × Permission × Bool => row.2.1) table
  have accessed := congrArg (fun row : Bool × Permission × Bool => row.2.2) table
  have unprotected : ({} : ProtectedTags).contains (node i).tag = false := rfl
  rcases i with ⟨i,bound⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all


/-- Exact connection to the existing source permission-table predicate. -/
theorem source_compatible (i : Fin 6) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible (state i)
      (if i.val = 0 ∨ i.val = 3 ∨ i.val = 5 then .LocalAccess else .ForeignAccess)
      (({} : ProtectedTags).contains (node i).tag) := by
  have guards := static_joint_permissions i
  unfold GeneralBorrowExposedConditionalWritePermissions.Compatible
  by_cases ancestor : i.val = 0 ∨ i.val = 3 ∨ i.val = 5
  · simpa only [ancestor,↓reduceIte] using guards
  · simpa only [ancestor,↓reduceIte] using guards

/-- The same tag identities and exposure flags are kept in the two correlated
representations; only A/B ancestry and the induced precise states differ. -/
theorem same_identities :
    raw.tagMapping = precise.tagMapping ∧
    raw.nodes.data.map (Option.map TreeNode.tag) = precise.nodes.data.map (Option.map TreeNode.tag) ∧
    raw.nodes.data.map (Option.map TreeNode.isExposed) =
      precise.nodes.data.map (Option.map TreeNode.isExposed) := by cbv <;> decide +kernel

/-- Both shared creations resolve ONE wildcard family to original1. The
ordinary interpretation fixes this once, rather than choosing per byte/use. -/
theorem fixed_origins :
    (a.tree.nodeAt (ix 1)).map TreeNode.parent = some none ∧
    (b.tree.nodeAt (ix 3)).map TreeNode.parent = some none ∧
    (preciseA.tree.nodeAt (ix 1)).map TreeNode.parent = some (some (ix 0)) ∧
    (preciseB.tree.nodeAt (ix 3)).map TreeNode.parent = some (some (ix 0)) := by cbv <;> decide +kernel

/-- Explicit coupling of the five retags: both traces use the same tags,
sizes, initial states and protectors. ONE origin1 replaces the two uses of
the same wildcard family; all concrete D/V/W parents retain their identity.
Each input is the preceding trace's actual output, not an independent fixture. -/
def SameRetagEvents : Prop :=
    a = exposed.tree.newChild Size.ZERO .wildcard (tag 2)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false ∧
    preciseA = exposed.tree.newChild Size.ZERO (.concrete (tag 1)) (tag 2)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false ∧
    d = dRead.tree.newChild Size.ZERO (.concrete (tag 2)) (tag 3)
      (DedupRangeMap.new (Size.ofBytes 2) mutable) (.ReservedFrz false) false ∧
    preciseD = preciseDRead.tree.newChild Size.ZERO (.concrete (tag 2)) (tag 3)
      (DedupRangeMap.new (Size.ofBytes 2) mutable) (.ReservedFrz false) false ∧
    b = firstWrite.tree.newChild Size.ZERO .wildcard (tag 4)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false ∧
    preciseB = preciseFirstWrite.tree.newChild Size.ZERO (.concrete (tag 1)) (tag 4)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false ∧
    v = b.tree.newChild Size.ZERO (.concrete (tag 3)) (tag 5)
      (DedupRangeMap.new Size.ZERO mutable) (.ReservedFrz false) false ∧
    preciseV = preciseB.tree.newChild Size.ZERO (.concrete (tag 3)) (tag 5)
      (DedupRangeMap.new Size.ZERO mutable) (.ReservedFrz false) false ∧
    w = wRead.tree.newChild Size.ZERO (.concrete (tag 4)) (tag 6)
      (DedupRangeMap.new (Size.ofBytes 2) mutable) (.ReservedFrz false) false ∧
    preciseW = preciseWRead.tree.newChild Size.ZERO (.concrete (tag 4)) (tag 6)
      (DedupRangeMap.new (Size.ofBytes 2) mutable) (.ReservedFrz false) false

theorem same_retag_events : SameRetagEvents :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Reads, original writes and V exposure are the SAME intervening events. -/
def SameInterveningEvents : Prop :=
    dRead = a.tree.performBorrowAccessRange (.concrete (tag 2)) Size.ZERO (Size.ofBytes 2) .Read {} .VisitChildrenOfAccessed ∧
    preciseDRead = preciseA.tree.performBorrowAccessRange (.concrete (tag 2)) Size.ZERO (Size.ofBytes 2) .Read {} .VisitChildrenOfAccessed ∧
    firstWrite = d.tree.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 2) .Write {} .VisitChildrenOfAccessed ∧
    preciseFirstWrite = preciseD.tree.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 2) .Write {} .VisitChildrenOfAccessed ∧
    exposedV = v.tree.exposeTag {} (tag 5) ∧ preciseExposedV = preciseV.tree.exposeTag {} (tag 5) ∧
    secondWrite = exposedV.tree.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 2) .Write {} .VisitChildrenOfAccessed ∧
    preciseSecondWrite = preciseExposedV.tree.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 2) .Write {} .VisitChildrenOfAccessed ∧
    wRead = secondWrite.tree.performBorrowAccessRange (.concrete (tag 4)) Size.ZERO (Size.ofBytes 2) .Read {} .VisitChildrenOfAccessed ∧
    preciseWRead = preciseSecondWrite.tree.performBorrowAccessRange (.concrete (tag 4)) Size.ZERO (Size.ofBytes 2) .Read {} .VisitChildrenOfAccessed

theorem same_intervening_events : SameInterveningEvents :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- One finite cast-site snapshot, after original1 exposure and before A.
This is witness data, not an operation resetting metadata or the final packet. -/
noncomputable def castSite : MachineHooks.State MiriMemoryKind Machine.RootUser :=
  let entry := {S05ZeroCellJointPacket.sourceEntry with allocation := S05ZeroCellCorrelatedWrite.sourceFor exposed.tree}
  let memory := {PreparedReflection.actual.initialMemory.setIssuedIds
    (PreparedReflection.actual.memoryData.issuedIds ++ #[S05ZeroCellJointPacket.sourceId]) with
    nextAllocId := 720, live := #[(S05ZeroCellJointPacket.sourceId,entry)]}
  ⟨⟨#[]⟩,{S05ZeroCellJointPacket.before with
    memory := memory
    borrowTracker := some ⟨{nextPointerTag := tag 2,rootPointerTags := #[(S05ZeroCellJointPacket.sourceId,tag 1)]},.Default⟩
    allocationSpans := #[(S05ZeroCellJointPacket.sourceId,PreparedReflection.actual.dummySpan,none)]
    user := {S05ZeroCellJointPacket.before.user with
      addresses := {S05ZeroCellJointPacket.before.user.addresses with
        baseAddr := #[⟨S05ZeroCellJointPacket.sourceId,4096⟩]
        intToPtrMap := #[⟨4096,S05ZeroCellJointPacket.sourceId⟩]
        exposed := #[S05ZeroCellJointPacket.sourceId]}
      payload := {S05ZeroCellJointPacket.before.user.payload with
        payload := {S05ZeroCellJointPacket.before.user.payload.payload with
          user := {S05ZeroCellJointPacket.before.user.payload.payload.user with
            runtime := {S05ZeroCellJointPacket.before.user.payload.payload.user.runtime with
              extras := {allocations := #[(S05ZeroCellJointPacket.sourceId,⟨none,#[]⟩)]}}}}}}}⟩

noncomputable def wildcardFamily : Pointer Provenance := Pointer.new .wildcard (Size.ofBytes 4096)
noncomputable def origin : Pointer Provenance := Pointer.new (.concrete S05ZeroCellJointPacket.sourceId (tag 1)) (Size.ofBytes 4096)
noncomputable def savedRawD : Pointer Provenance := Pointer.new (.concrete S05ZeroCellJointPacket.sourceId (tag 3)) (Size.ofBytes 4096)

/-- One invocation, with two copies of its returned bound variable. This is
stronger than equating bits of two independently constructed wildcard values. -/
theorem one_cast_family (h : PointerMachine.Hooks MiriMemoryKind
    (ValidityMachine.Control (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost))) :
    S05ZeroCellWildcardCast.copies h 4096 castSite =
      .ok (wildcardFamily,wildcardFamily) castSite :=
  S05ZeroCellWildcardCast.one_cast_two_copies h castSite 4096 rfl

/-- The family is assigned origin1 once, for BOTH A/B uses. Origin1 is present
and exposed at the selected cast site and both source retag points. -/
theorem family_origin_available :
    origin.provenance = .concrete S05ZeroCellJointPacket.sourceId (tag 1) ∧
    (exposed.tree.nodeAt (ix 0)).map TreeNode.isExposed = some true ∧
    (firstWrite.tree.nodeAt (ix 0)).map TreeNode.isExposed = some true ∧
    wildcardFamily.provenance = .wildcard := by
  refine ⟨rfl,?_,?_,rfl⟩ <;> cbv

/-- Bind the TWO actual source-cast copies to the A/B event slots. The
same selected origin supplies both precise parents; it is not reselected. -/
def FamilyBindings : Prop :=
  let rawParent : ProvenanceExtra := match wildcardFamily.provenance with
    | .wildcard => .wildcard | .concrete _ tag => .concrete tag
  let preciseParent : ProvenanceExtra := match origin.provenance with
    | .wildcard => .wildcard | .concrete _ tag => .concrete tag
  a = exposed.tree.newChild Size.ZERO rawParent (tag 2)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false ∧
  b = firstWrite.tree.newChild Size.ZERO rawParent (tag 4)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false ∧
  preciseA = exposed.tree.newChild Size.ZERO preciseParent (tag 2)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false ∧
  preciseB = preciseFirstWrite.tree.newChild Size.ZERO preciseParent (tag 4)
      (DedupRangeMap.new Size.ZERO zeroCell) .Cell false

theorem family_bindings : FamilyBindings := ⟨rfl,rfl,rfl,rfl⟩

/-- Actual dataflow from ONE source invocation to both A/B event arguments.
The two pointer projections belong to its returned pair, not two casts. -/
def CastFamilyBindings : Prop := ∀ h : PointerMachine.Hooks MiriMemoryKind
    (ValidityMachine.Control (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost)),
  (do
    let family ← S05ZeroCellWildcardCast.copies h 4096
    let parentA : ProvenanceExtra := match family.1.provenance with
      | .wildcard => .wildcard | .concrete _ tag => .concrete tag
    let parentB : ProvenanceExtra := match family.2.provenance with
      | .wildcard => .wildcard | .concrete _ tag => .concrete tag
    pure (exposed.tree.newChild Size.ZERO parentA (tag 2)
        (DedupRangeMap.new Size.ZERO zeroCell) .Cell false,
      firstWrite.tree.newChild Size.ZERO parentB (tag 4)
        (DedupRangeMap.new Size.ZERO zeroCell) .Cell false)) castSite = .ok (a,b) castSite

theorem cast_family_bindings : CastFamilyBindings := by
  intro h
  simp only [bind,EStateM.bind,one_cast_family h]
  rfl

/-- Scope/role assignment of this finite caller: only W and the independent
Bool place are active typed claims at entry. D's output was copied to Scalar
by runToD; V's only typed use/exposure ends in run's local block. The D scalar
remains RAW, with no content-ownership claim. These are current roles, not a
GC operation or deletion of D/V from the borrow graph. -/
def activeTags : Array BorTag := #[tag 6,tag 7]
def endedTypedTags : Array BorTag := #[tag 3,tag 5]
noncomputable def retainedRaw : Array (Pointer Provenance) := #[savedRawD]

theorem current_roles :
    S05ZeroCellJointPacket.sourcePointer.provenance = .concrete S05ZeroCellJointPacket.sourceId (tag 6) ∧
    S05ZeroCellJointPacket.destinationPointer.provenance = .concrete S05ZeroCellJointPacket.destinationId (tag 7) ∧
    savedRawD.provenance = .concrete S05ZeroCellJointPacket.sourceId (tag 3) ∧
    tag 3 ∉ activeTags ∧ tag 5 ∉ activeTags ∧
    S05ZeroCellJointPacket.sourceEntry.allocation.provenanceMap = ProvenanceMap.new ∧
    S05ZeroCellJointPacket.destinationEntry.allocation.provenanceMap = ProvenanceMap.new ∧
    S05ZeroCellJointPacket.state.stack.frames = #[] ∧ S05ZeroCellJointPacket.before.user.payload.payload.registry.inactive = #[] := by
  exact ⟨rfl,rfl,rfl,by decide_cbv,by decide_cbv,rfl,rfl,rfl,rfl⟩

theorem ancestor_indices (i : Fin 6) :
    (i.val = 0 ∨ i.val = 3 ∨ i.val = 5) ↔ i.val ∈ ([0,3,5] : List Nat) := by simp

/-- The index classification is tied to the actual tag-to-index mapping and
terminating ancestor query, not selected separately from the precise graph. -/
theorem ancestor_grants :
    precise.tagMapping.get (tag 1) = some (ix 0) ∧
    precise.tagMapping.get (tag 4) = some (ix 3) ∧
    precise.tagMapping.get (tag 6) = some (ix 5) := by cbv <;> decide +kernel

/-- Explicit finite typed-use endpoints from the chosen scoped caller:
D3 is erased to the saved Scalar before original Write1, V5's typed block ends
with exposure before Write2; W6 is created after Write2. This accompanies the
actual empty current stack/inactive stacks and pointer-free backing bytes. -/
def dLastTypedUse : Nat := 3
def firstOriginalWrite : Nat := 4
def vLastTypedUse : Nat := 7
def secondOriginalWrite : Nat := 8
def wCreation : Nat := 9

theorem scoped_roles : dLastTypedUse < firstOriginalWrite ∧
    vLastTypedUse < secondOriginalWrite ∧ secondOriginalWrite < wCreation := by decide

/-- One CLOSED finite joint certificate. Its fields expose the selected
interpretation; this is not an opaque Ordinary predicate or all-input theorem. -/
structure Certificate : Prop where
  sourceAt : S05ZeroCellJointPacket.before.memory.live.find? (fun row => row.1 == S05ZeroCellJointPacket.sourceId) = some (S05ZeroCellJointPacket.sourceId,S05ZeroCellJointPacket.sourceEntry)
  destinationAt : S05ZeroCellJointPacket.before.memory.live.find? (fun row => row.1 == S05ZeroCellJointPacket.destinationId) = some (S05ZeroCellJointPacket.destinationId,S05ZeroCellJointPacket.destinationEntry)
  rawAt : S05ZeroCellJointPacket.sourceEntry.allocation.extra = raw
  sourceValue : OrdinaryPhysicalValidity.MutU8Slice S05ZeroCellJointPacket.sourceEntry.allocation 0 2
  destinationValue : OrdinaryPhysicalValidity.BoolDestination S05ZeroCellJointPacket.destinationEntry.allocation 0
  separate : S05ZeroCellJointPacket.sourceId ≠ S05ZeroCellJointPacket.destinationId
  held : S05ZeroCellJointPacket.before.borrowTracker.map (fun tracker => tracker.global.protectedTags) = some ({} : ProtectedTags)
  currentMetadata : S05ZeroCellJointPacket.before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  profile : S05ZeroCellJointPacket.before.user.payload.ghost = false ∧ S05ZeroCellJointPacket.before.user.payload.validation = .Shallow ∧
    S05ZeroCellJointPacket.before.user.payload.alignment = .Int ∧ S05ZeroCellJointPacket.before.dataRace = none ∧
    S05ZeroCellJointPacket.before.user.payload.payload.user.backend = .none ∧ S05ZeroCellJointPacket.before.threads.fixedScheduling = true ∧
    S05ZeroCellJointPacket.before.user.payload.payload.user.host.control.checkedArithmetic = false ∧
    S05ZeroCellJointPacket.before.user.payload.payload.user.host.control.gcInterval = 0
  harness : S05ZeroCellJointPacket.state.stack.frames = #[]
  noStoredTypedFrame : S05ZeroCellJointPacket.before.user.payload.payload.registry.inactive = #[]
  sourceNoPointerBytes : S05ZeroCellJointPacket.sourceEntry.allocation.provenanceMap = ProvenanceMap.new
  destinationNoPointerBytes : S05ZeroCellJointPacket.destinationEntry.allocation.provenanceMap = ProvenanceMap.new
  rawIdentity : savedRawD.provenance = .concrete S05ZeroCellJointPacket.sourceId (tag 3)
  retainedRawIdentity : retainedRaw = #[savedRawD]
  activeW : S05ZeroCellJointPacket.sourcePointer.provenance = .concrete S05ZeroCellJointPacket.sourceId (tag 6)
  activeBool : S05ZeroCellJointPacket.destinationPointer.provenance = .concrete S05ZeroCellJointPacket.destinationId (tag 7)
  inactiveD : tag 3 ∉ activeTags
  inactiveV : tag 5 ∉ activeTags
  scope : dLastTypedUse < firstOriginalWrite ∧ vLastTypedUse < secondOriginalWrite ∧ secondOriginalWrite < wCreation
  castFamily : ∀ h : PointerMachine.Hooks MiriMemoryKind
    (ValidityMachine.Control (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost)),
    S05ZeroCellWildcardCast.copies h 4096 castSite = .ok (wildcardFamily,wildcardFamily) castSite
  originAtA : (exposed.tree.nodeAt (ix 0)).map TreeNode.isExposed = some true
  originAtB : (firstWrite.tree.nodeAt (ix 0)).map TreeNode.isExposed = some true
  castUseBindings : CastFamilyBindings
  familyBindings : FamilyBindings
  originRights :
    (exposed.tree.nodeAt (ix 0)).map TreeNode.isExposed = some true ∧
    (preciseFirstWrite.tree.nodeAt (ix 0)).map TreeNode.isExposed = some true ∧
    (exposed.tree.locations.entries[0]'(by cbv)).data.perms.get (ix 0) = some ⟨.Unique,true,.None⟩ ∧
    (preciseFirstWrite.tree.locations.entries[0]'(by cbv)).data.perms.get (ix 0) = some ⟨.Unique,true,.None⟩
  sameOrigin : origin.provenance = .concrete S05ZeroCellJointPacket.sourceId (tag 1)
  retags : SameRetagEvents
  intervening : SameInterveningEvents
  preciseParents : precise.nodes.data.map (Option.map TreeNode.parent) =
      #[some none,some (some (ix 0)),some (some (ix 1)),some (some (ix 0)),some (some (ix 2)),some (some (ix 3))]
  ancestorGrants : precise.tagMapping.get (tag 1) = some (ix 0) ∧
    precise.tagMapping.get (tag 4) = some (ix 3) ∧ precise.tagMapping.get (tag 6) = some (ix 5)
  ancestorChain : precise.nthParent (tag 6) 0 = .ok (tag 6) ∧ precise.nthParent (tag 6) 1 = .ok (tag 4) ∧
    precise.nthParent (tag 6) 2 = .ok (tag 1) ∧ precise.nthParent (tag 6) 3 = .error (.missingParent (tag 6) 3)
  nodeCoverage : precise.nodes.data.size = 6 ∧ precise.nodes.data.all Option.isSome = true
  permissions : ∀ i : Fin 6, GeneralBorrowExposedConditionalWritePermissions.Compatible (state i)
      (if i.val ∈ ([0,3,5] : List Nat) then .LocalAccess else .ForeignAccess)
      (({} : ProtectedTags).contains (node i).tag)
  currentArgument : (DuplicatePrefixSliceArgument.first PreparedReflection.actual.runtime.target.base S05ZeroCellJointPacket.argument 2).op =
    .immediate S05ZeroCellJointPacket.argumentValue2.imm ∧
    (DuplicatePrefixSliceArgument.first PreparedReflection.actual.runtime.target.base S05ZeroCellJointPacket.argument 2).layout = RootCompilerFacts.sliceLayout ∧
    S05ZeroCellJointPacket.argumentValue2.layout = RootCompilerFacts.sliceLayout
  boolAuthority : OrdinaryBorrowAuthority.LocalWrite
    (((S05ZeroCellJointPacket.destinationEntry.allocation.extra.locations.entries[0]'(by decide +kernel)).data.perms.get (ix 0)).getD
      ⟨.Disabled,false,.None⟩) false

/-- All fields refer to the same actualBefore/raw endpoint and ONE precise
state, including the same protector set. No operation-success premise occurs. -/
theorem certificate : Certificate := by
  refine {
    sourceAt := S05ZeroCellJointPacket.source_present
    destinationAt := S05ZeroCellJointPacket.destination_present
    rawAt := rfl
    sourceValue := S05ZeroCellJointPhysical.source_physical
    destinationValue := S05ZeroCellJointPhysical.destination_physical
    separate := S05ZeroCellJointPacket.distinct_ids
    held := S05ZeroCellJointPacket.no_protectors
    currentMetadata := S05ZeroCellJointPacket.current_metadata
    profile := S05ZeroCellJointPacket.profile
    harness := S05ZeroCellJointPacket.empty_stack
    noStoredTypedFrame := rfl
    sourceNoPointerBytes := rfl
    destinationNoPointerBytes := rfl
    rawIdentity := rfl
    retainedRawIdentity := rfl
    activeW := rfl
    activeBool := rfl
    inactiveD := by decide_cbv
    inactiveV := by decide_cbv
    scope := scoped_roles
    castFamily := one_cast_family
    originAtA := family_origin_available.2.1
    originAtB := family_origin_available.2.2.1
    castUseBindings := cast_family_bindings
    familyBindings := family_bindings
    originRights := stable_origin_available
    sameOrigin := rfl
    retags := same_retag_events
    intervening := same_intervening_events
    preciseParents := parents
    ancestorGrants := ancestor_grants
    ancestorChain := w_ancestor_chain
    nodeCoverage := node_shape
    permissions := ?_
    currentArgument := S05ZeroCellJointPhysical.current_argument
    boolAuthority := S05ZeroCellJointPhysical.destination_static_authority }
  intro i
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using source_compatible i

end DuplicatePrefix.S05ZeroCellJointCertificate

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellJointCertificate." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved finite joint-certificate dependency {dependency}"
