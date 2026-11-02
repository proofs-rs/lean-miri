import duplicate_prefix.GeneralBorrowConcreteRangeInvariant
namespace DuplicatePrefix.GeneralBorrowReadRowRange
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedConditionalRangeFrames
open GeneralBorrowSnapshotWildcardRangeBoth (Runtime VacantFrame authorization_locations runtime_locations)
open GeneralBorrowReadRowNormal (ReadRow)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

abbrev Row (tree : BorrowTree) (protections : ProtectedTags) (anchor selected : UniIndex)
    (maximum : Option BorTag) (location : LocationTree) : Prop :=
  Nonempty (ReadRow tree location protections (some anchor) (some selected) maximum)

/-- Internal operation-specific owner window. Public S01 Positive is unchanged. -/
structure Positive (tree : BorrowTree) (protections : ProtectedTags)
    (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64) where
  positive : 0 < len.toNat
  bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat
  sourcePresent : ∃ node, tree.nodeAt anchor = some node
  rows : OwnedOn (Row tree protections anchor selected maximum) offset (offset + len) tree.locations

/-- Existing public Both permission data supplies this internal Read window. -/
theorem of_positive (tree : BorrowTree) (protections : ProtectedTags) (anchor selected : UniIndex)
    (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections (some anchor) (some selected) maximum offset len) :
    Nonempty (Positive tree protections anchor selected maximum offset len) := by
  refine ⟨⟨positive.positive,positive.bounds,positive.sourcePresent anchor rfl,?_⟩⟩
  intro position valid nonempty beforeUpper afterLower
  obtain ⟨row⟩ := positive.rows position valid nonempty beforeUpper afterLower
  exact ⟨GeneralBorrowReadRowNormal.of_row tree _ protections _ _ maximum row⟩

theorem row_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (anchor selected : UniIndex)
    (maximum : Option BorTag) (row : Row tree protections anchor selected maximum location) :
    Row {tree with locations := locations} protections anchor selected maximum location := by
  obtain ⟨row⟩ := row
  refine ⟨{
    wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,
    cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro source equal
    obtain ⟨normal⟩ := row.normal source equal
    exact ⟨{component := normal.component,permissions := normal.permissions}⟩
  · intro position valid different
    obtain ⟨support,read,write⟩ := row.callbacks position valid different
    exact ⟨support,authorization_locations tree locations location protections _ _ _ _ support read,
      authorization_locations tree locations location protections _ _ _ _ support write⟩

/-- Actual full concrete-source Read from one raw owner row. -/
theorem location (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag) (before : LocationTree)
    (row : Row tree protections anchor selected maximum before)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (runtime : Runtime tree protections before) (short : tree.nodes.size < 65536)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let accessed := source_tree_access_at tree before (some anchor) .Read protections mode range
    source_access_status accessed = none ∧ Row tree protections anchor selected maximum (source_access_location accessed) ∧
      Runtime tree protections (source_access_location accessed) ∧ VacantFrame tree before (source_access_location accessed) := by
  obtain ⟨row⟩ := row
  obtain ⟨complete,coherent,profile,possible,afterRow⟩ :=
    GeneralBorrowReadRowAccess.access tree before protections formed anchor selected anchorNode present
      maximum row distinct order runtime.coherent runtime.profile runtime.possible short mode range
  refine ⟨complete,afterRow,⟨coherent,profile,possible⟩,?_⟩
  intro query missing
  rw [profile.vacant query missing,runtime.profile.vacant query missing]

/-- Physical ranged concrete Read completion with the same raw owner-window rows
and runtime properties installed on the actual result tree. -/
structure Contract (before : BorrowTree) (protections : ProtectedTags)
    (anchor selected : UniIndex) (maximum : Option BorTag) (lower upper : UInt64) (result : BorrowTree.BorrowTreeAccessResult) : Prop where
  completed : result.status = .Completed
  runtime : Every (Runtime result.tree protections) result.tree.locations
  rows : OwnedOn (Row result.tree protections anchor selected maximum) lower upper result.tree.locations
  well : result.tree.locations.WellFormed
  capacity : result.tree.locations.size = before.locations.size
  frames : Origins (VacantFrame before) before.locations result.tree.locations
  nodes : result.tree.nodes = before.nodes
  roots : result.tree.roots = before.roots
  tags : result.tree.tagMapping = before.tagMapping

/-- Installing the actual ranged result reconstructs full runtime facts from
its preserved graph metadata and every physical result row. -/
theorem install (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchor selected : UniIndex) (maximum : Option BorTag) (lower upper : UInt64) (result : BorrowTree.BorrowTreeAccessResult)
    (contract : Contract tree global.protectedTags anchor selected maximum lower upper result) :
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global := by
  have same : result.tree = {tree with locations := result.tree.locations} := by
    have nodes := contract.nodes
    have roots := contract.roots
    have tags := contract.tags
    cases tree
    cases result with
    | mk after visited status =>
      cases after
      simp_all
  have graph := GeneralBorrowStructuralHistoryState.graph_locations tree result.tree.locations before.formed.toGraphState
  rw [←same] at graph
  refine ⟨⟨⟨graph,contract.well⟩,?_⟩,?_,?_,?_⟩
  · intro position valid
    exact (contract.runtime position valid).profile
  · intro position valid
    exact (contract.runtime position valid).coherent
  · intro position valid
    exact (contract.runtime position valid).possible
  · refine ⟨?_,before.below.protectors⟩
    rw [contract.tags]
    exact before.below.mapping

/-- A bounded actual concrete Read from raw Read-only owner-window data.
All local operational steps are derived, and the exact owner length survives. -/
theorem access (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (mode : ChildrenVisitMode) (sliceStart sliceLen : UInt64)
    (positive : Positive tree global.protectedTags anchor selected maximum sliceStart sliceLen)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len .Read global.protectedTags mode
    Contract tree global.protectedTags anchor selected maximum sliceStart (sliceStart + sliceLen) result ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧
    Nonempty (Positive result.tree global.protectedTags anchor selected maximum sliceStart sliceLen) := by
  have all : Every (Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  have bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat := by
    have ownerBounds := positive.bounds
    omega
  have fits : offset.bytes.toNat + len.bytes.toNat < 2^64 :=
    Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
  have ownerFits : sliceStart.toNat + sliceLen.toNat < 2^64 :=
    Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have requestUpper : (offset.bytes + len.bytes).toNat ≤ (sliceStart + sliceLen).toNat := by
    rw [UInt64.toNat_add,UInt64.toNat_add,Nat.mod_eq_of_lt fits,Nat.mod_eq_of_lt ownerFits]
    exact requestStop
  obtain ⟨anchorNode,anchorPresent⟩ := positive.sourcePresent
  have localCallback := fun current row runtime range => location tree global.protectedTags before.formed.toGraphState
    anchor selected anchorNode anchorPresent maximum current row distinct order runtime short mode range
  have composed := GeneralBorrowConcreteRangeInvariant.access tree global.protectedTags tag anchor tagPresent offset len
    .Read mode (Row tree global.protectedTags anchor selected maximum) (Runtime tree global.protectedTags)
    (VacantFrame tree) (by intro current query missing;rfl) localCallback
    sliceStart (sliceStart + sliceLen) positive.rows before.formed.well all bounds requestLower requestUpper
  have same := GeneralBorrowConcreteRangeInvariant.Contract.tree_eq composed
  have contract : Contract tree global.protectedTags anchor selected maximum sliceStart (sliceStart + sliceLen)
      (tree.performBorrowAccessRange (.concrete tag) offset len .Read global.protectedTags mode) := by
    refine ⟨composed.completed,?_,?_,composed.well,composed.capacity,composed.frames,composed.nodes,composed.roots,composed.tags⟩
    · intro position valid
      have transported := runtime_locations tree
        (tree.performBorrowAccessRange (.concrete tag) offset len .Read global.protectedTags mode).tree.locations
        _ global.protectedTags (composed.runtime position valid)
      simpa only [←same] using transported
    · intro position valid nonempty beforeUpper afterLower
      have transported := row_locations tree
        (tree.performBorrowAccessRange (.concrete tag) offset len .Read global.protectedTags mode).tree.locations
        _ global.protectedTags anchor selected maximum
        (composed.rows position valid nonempty beforeUpper afterLower)
      simpa only [←same] using transported
  refine ⟨contract,install tree global before anchor selected maximum _ _ _ contract,⟨{
    positive := positive.positive,bounds := ?_,sourcePresent := ?_,rows := contract.rows}⟩⟩
  · rw [contract.capacity]
    exact positive.bounds
  · exact ⟨anchorNode,by unfold BorrowTree.nodeAt;rw [contract.nodes];exact anchorPresent⟩
end DuplicatePrefix.GeneralBorrowReadRowRange
