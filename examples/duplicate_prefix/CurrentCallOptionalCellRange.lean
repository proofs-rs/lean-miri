import duplicate_prefix.CurrentCallOptionalCellAccess
import duplicate_prefix.GeneralBorrowConcreteRangeEntry

/-! A range consumer for ONE optional ambient Cell leaf. Every intersecting
actual stored row is supplied by the SAME current resource embedding, with
one fixed completion and grant. This is not ordinary-input admission. -/
namespace DuplicatePrefix.CurrentCallOptionalCellRange
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentGrantResources
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowExposureCardinality
open GeneralRangeMapOrigins GeneralRangeMapState CurrentCallOptionalCellAccess
set_option autoImplicit false
set_option cbv.warning false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Existing current embeddings supply each overlapping physical row. Neither
an origin nor a grant is chosen independently at individual bytes. -/
theorem rows_of_embedding (allocation : Allocation Provenance BorrowTree)
    (completion : Completion) (protections : ProtectedTags) (grant : UniIndex)
    (lower upper : UInt64) (well : allocation.extra.locations.WellFormed)
    (embedding : ∀ byte, lower.toNat ≤ byte → byte < upper.toNat →
      Embeds allocation protections completion grant byte .exclusive) :
    OwnedOn (RowResources allocation.extra completion protections grant) lower upper allocation.extra.locations := by
  intro position valid positive beforeUpper afterLower
  have segmentPositive := (GeneralRangeMapGeometry.facts allocation.extra.locations well (by omega)).2.1 position valid
  have member : allocation.extra.locations.entries[position] ∈ allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  by_cases earlier : lower.toNat ≤ allocation.extra.locations.entries[position].range.start.toNat
  · exact resources_of_embedding allocation completion protections grant _
      (embedding _ earlier beforeUpper) _ member (Nat.le_refl _) segmentPositive
  · exact resources_of_embedding allocation completion protections grant lower.toNat
      (embedding _ (Nat.le_refl _) positive) _ member (by omega) afterLower

/-- Actual resolved concrete range access, including splitting/materializing
rows and the real per-row primary/ambient root scans. The resource assignment
and actual node/root/tag arrays remain fixed. No success or raw-table premise
is exported. Ordinary coverage and repeated constructor/release framing remain
separate from this bounded access consumer. -/
theorem write (allocation : Allocation Provenance BorrowTree) (completion : Completion)
    (protections : ProtectedTags) (primary cell source : UniIndex)
    (cellNode sourceNode : TreeNode)
    (rep : Representation allocation.extra completion protections primary cell cellNode)
    (formed : GeneralBorrowStructuralHistoryState.GraphState allocation.extra)
    (sourcePresent : allocation.extra.nodes.get source = some sourceNode)
    (sourcePath : Path allocation.extra primary source)
    (offset len : Size) (lower upper : UInt64)
    (embedding : ∀ byte, lower.toNat ≤ byte → byte < upper.toNat →
      Embeds allocation protections completion source byte .exclusive)
    (cellStates : Every (fun location => (RawState location cell cellNode).permission = .Cell)
      allocation.extra.locations)
    (well : allocation.extra.locations.WellFormed)
    (runtime : Every (fun location => LocationCoherent allocation.extra location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile allocation.extra location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible allocation.extra location) allocation.extra.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ allocation.extra.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract allocation.extra
      (RowResources allocation.extra completion protections source)
      (fun location => LocationCoherent allocation.extra location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile allocation.extra location protections ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible allocation.extra location)
      (fun _ _ => True) lower upper
      (allocation.extra.performBorrowAccessRange (.concrete sourceNode.tag) offset len .Write protections mode) := by
  have owned := rows_of_embedding allocation completion protections source lower upper well embedding
  have input : OwnedOn (fun location => RowResources allocation.extra completion protections source location ∧
      (RawState location cell cellNode).permission = .Cell) lower upper allocation.extra.locations := by
    intro position valid positive beforeUpper afterLower
    exact ⟨owned position valid positive beforeUpper afterLower,cellStates position valid⟩
  have mapped : allocation.extra.indexOfTag sourceNode.tag = some source :=
    formed.allocator.nodeTags source sourceNode sourcePresent
  apply GeneralBorrowConcreteRangeEntry.access allocation.extra protections sourceNode.tag source mapped offset len
    .Write mode _ _ _ (fun _ _ => True) (fun _ initial => initial.1) (fun _ => True.intro)
    _ lower upper input well runtime bounds requestLower requestUpper
  intro location initial current range
  have result := CurrentCallOptionalCellAccess.write allocation.extra completion location protections primary cell source
    cellNode sourceNode rep formed sourcePresent sourcePath initial.2 current.1 current.2.1 current.2.2 initial.1 mode range
  exact ⟨result.1,result.2.2.2.2,⟨result.2.1,result.2.2.1,result.2.2.2.1⟩,True.intro⟩

/-- The exact initialized two-byte necessity packet executes the concrete
range Write on its retained two-root tree. This is a closed kernel calculation,
not an execution-equivalence postulate or a whole-program safety claim. -/
def packetWrite : BorrowTree.BorrowTreeAccessResult :=
  CurrentCallNeutralCellNecessity.sourceTree.performBorrowAccessRange
    (.concrete CurrentCallNeutralCellNecessity.sourceTag) (Size.ofBytes 0) (Size.ofBytes 2)
    .Write CurrentCallNeutralCellNecessity.held .VisitChildrenOfAccessed

private def packetRow : LocationTree :=
  ((packetWrite.tree.locations.entries[0]?).map (·.data)).getD CurrentCallNeutralCellNecessity.row

/-- Actual SIFA.Write is retained, rather than asserting the old SIFA.None. -/
theorem packet_cell_state :
    RawState packetRow CurrentCallNeutralCellNecessity.ambient CurrentCallNeutralCellNecessity.cellNode =
      ⟨.Cell,false,.Write⟩ := by decide_cbv

theorem packet_resources :
    RowResources packetWrite.tree CurrentCallNeutralCellNecessity.newCompletion
      CurrentCallNeutralCellNecessity.held CurrentCallNeutralCellNecessity.primary packetRow := by
  intro index node present
  constructor
  · intro below
    have same : index = CurrentCallNeutralCellNecessity.primary := by
      cases below with
      | refl => rfl
      | step edge _ =>
        simp [CurrentCallNeutralCellNecessity.newCompletion,CurrentCallNeutralCellNecessity.primary,UniIndex.toNat] at edge
    subst index
    have slot : packetRow.perms.get CurrentCallNeutralCellNecessity.primary = some ⟨.Unique,true,.None⟩ := by decide_cbv
    unfold RawState
    rw [slot]
    change Demand.exclusive ∈ tokens (denote ⟨.Unique,true,.None⟩ false)
    decide
  · intro clash
    have unheld : CurrentCallNeutralCellNecessity.held.contains node.tag = false := rfl
    rw [unheld] at clash
    simp [denote,CandidateCurrentGrantResources.guard,Clash] at clash

/-- The actual access changes only borrow metadata. Source initialization,
separate Bool storage, and the original simultaneous pointer/loan/content
assignment are retained literally. -/
theorem packet_storage_families :
    OrdinaryPhysicalValidity.MutU8Slice
      (CurrentCallNeutralCellNecessity.sourceAfter.setExtra packetWrite.tree) 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination CurrentCallNeutralCellNecessity.boolAllocation 0 ∧
    CandidateFreezeContentResources.Valid CurrentCallNeutralCellNecessity.contents ∧
    (CurrentCallNeutralCellNecessity.interpretation false).pointers =
      (CurrentCallNeutralCellNecessity.interpretation true).pointers ∧
    (CurrentCallNeutralCellNecessity.interpretation false).loans =
      (CurrentCallNeutralCellNecessity.interpretation true).loans ∧
    (CurrentCallNeutralCellNecessity.interpretation false).content =
      (CurrentCallNeutralCellNecessity.interpretation true).content := by
  have initial := CurrentCallNeutralCellNecessity.source_physical
  refine ⟨?_,CurrentCallNeutralCellNecessity.bool_physical,
    CurrentCallNeutralCellNecessity.content_composition,
    CurrentCallNeutralCellNecessity.same_families⟩
  exact ⟨⟨initial.storage.byteLength,initial.storage.maskLength,
    initial.storage.maskCapacity,initial.storage.provenance⟩,
    initial.nonempty,initial.signedSize,initial.contained,initial.writable,initial.values⟩

/-- Same concrete families, same current grant/completion and initialized source
storage coexist with actual accepted access, despite strict completion failure.
This bounded acceptance witness does not construct a full Before or Proposed. -/
theorem necessity_two_byte_write :
    packetWrite.status = .Completed ∧
    packetWrite.tree.nodes = CurrentCallNeutralCellNecessity.sourceTree.nodes ∧
    packetWrite.tree.roots = CurrentCallNeutralCellNecessity.sourceTree.roots ∧
    packetWrite.tree.tagMapping = CurrentCallNeutralCellNecessity.sourceTree.tagMapping ∧
    OwnedOn (RowResources packetWrite.tree CurrentCallNeutralCellNecessity.newCompletion
      CurrentCallNeutralCellNecessity.held CurrentCallNeutralCellNecessity.primary)
      0 2 packetWrite.tree.locations ∧
    (∀ completion, ¬ Completes CurrentCallNeutralCellNecessity.sourceTree completion) := by
  refine ⟨by decide_cbv,by decide_cbv,by decide_cbv,by decide_cbv,?_,CurrentCallNeutralCellNecessity.no_completion⟩
  intro position valid _ _ _
  have length : packetWrite.tree.locations.entries.size = 1 := by decide_cbv
  have zero : position = 0 := by omega
  subst position
  change RowResources packetWrite.tree _ _ _ packetWrite.tree.locations.entries[0].data
  have row : packetWrite.tree.locations.entries[0].data = packetRow := by
    simp only [packetRow,Array.getElem?_eq_getElem valid,Option.map_some,Option.getD_some]
  rw [row]
  exact packet_resources

end
end DuplicatePrefix.CurrentCallOptionalCellRange

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallOptionalCellRange.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved optional Cell range dependency {dependency}"
