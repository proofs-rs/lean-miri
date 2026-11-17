import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowFreshConstructor
import duplicate_prefix.GeneralBorrowFreshReuseConstructor
import duplicate_prefix.GeneralBorrowFreshSharedConstructor
namespace DuplicatePrefix.GeneralBorrowFreshReborrowStages
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

inductive Kind where | mutable | shared deriving DecidableEq

def initial : Kind → LocationState
  | .mutable => GeneralBorrowFreshChild.inside
  | .shared => GeneralBorrowFreshAnchor.sharedState

def outside : Kind → Permission
  | .mutable => .ReservedFrz false
  | .shared => .Frozen

def ownerKind : Kind → AccessKind
  | .mutable => .Write
  | .shared => .Read

set_option autoImplicit false in
/-- Explicit allocator data for the next newChild. The reuse rank slack is a
data certificate bound; it is not an assumption that any operation succeeds. -/
inductive Slot (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (parent : UniIndex) : Type
  | append (noFree : tree.tagMapping.deassigned.back? = none)
      (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
      (fits : tree.tagMapping.mapping.size ≤ 4294967295)
  | reuse (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index)
      (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
      (slack : depth.depth parent < tree.nodes.size)

/-- Completion turns the real result record into the exact constructor form
used by the interpreter driver. The completion proof is derived by the stages. -/
theorem child_complete (result : BorrowTree.ChildInsertResult) (done : result.outcome = .ok ()) :
    result = ⟨result.tree,.ok ()⟩ := by
  cases result with
  | mk tree outcome => cases done;rfl

/-- Actual fresh protector registration, real parent read and real protected
mutable/Frozen child construction are composed without operation-success inputs.
The single-root condition is explicit; ownership outside the slice is free. -/
theorem protected_construct (tree : BorrowTree) (protections : ProtectedTags) (kind : Kind)
    (parentTag newTag : BorTag) (parent root : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (parentPresent : tree.nodeAt parent = some parentNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (protectorFresh : GeneralBorrowProtector.Fresh tree newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent (ownerKind kind))
      offset (offset+len) tree.locations) :
    let registered := protections.insert newTag .StrongProtector
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) (initial kind)) (outside kind) true
    ∃ index, read.status = .Completed ∧ child.outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned child.tree registered index (ownerKind kind))
        offset (offset+len) child.tree.locations := by
  let registered := protections.insert newTag .StrongProtector
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := protector_owned_on tree protections newTag .StrongProtector protectorFresh parent (ownerKind kind)
    offset (offset+len) owned
  have good := GeneralBorrowRangeLocal.access tree registered parentTag parent root (Size.ofBytes offset) (Size.ofBytes len)
    .Read (ownerKind kind) .VisitChildrenOfAccessed (fun _ => rfl) nodeFits depth children parentNode parentPresent roots covered
    parentTagPresent well offset (offset+len) owners bounds (Nat.le_refl _) (Nat.le_refl _)
  change read.status = .Completed ∧
    OwnedOn (GeneralBorrowRange.LocationOwned read.tree registered parent (ownerKind kind)) offset (offset+len) read.tree.locations ∧
    read.tree.locations.WellFormed ∧ read.tree.locations.size = tree.locations.size at good
  have framed := frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read registered .VisitChildrenOfAccessed
  have nodesKnown := congrArg BorrowTree.nodes framed
  have nodes : read.tree.nodes = tree.nodes := nodesKnown
  have tagsKnown := congrArg BorrowTree.tagMapping framed
  have tags : read.tree.tagMapping = tree.tagMapping := tagsKnown
  let readDepth := depth_on tree read.tree nodes depth
  have parentAfter : read.tree.nodeAt parent = some parentNode := by
    change read.tree.nodes.get parent = some parentNode
    rw [nodes]
    exact parentPresent
  have parentTagAfter : read.tree.tagMapping.get parentTag = some parent := by
    rw [tags]
    exact parentTagPresent
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping newTag := by rw [tags];exact tagFresh
  have boundsAfter : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by
    rw [good.2.2.2]
    exact bounds
  have fitsAfter : read.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact nodeFits
  dsimp only
  cases slot with
  | append noFree aligned fits =>
    have noFreeAfter : read.tree.tagMapping.deassigned.back? = none := by rw [tags];exact noFree
    have alignedAfter : read.tree.tagMapping.mapping.size = read.tree.nodes.data.size := by rw [tags,nodes];exact aligned
    have indexFits : read.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [tags];exact fits
    refine ⟨⟨UInt32.ofNat read.tree.tagMapping.mapping.size⟩,good.1,?_⟩
    cases kind with
    | mutable =>
      exact GeneralBorrowFreshConstructor.mutable_owned read.tree readDepth parentTag newTag parent parentNode
        parentTagAfter parentAfter freshAfter noFreeAfter alignedAfter indexFits offset len nonzero good.2.2.1 boundsAfter
        registered .Write good.2.1
    | shared =>
      exact GeneralBorrowFreshSharedConstructor.append_owned read.tree readDepth parentTag newTag parent parentNode
        parentTagAfter parentAfter freshAfter noFreeAfter alignedAfter indexFits true offset len nonzero good.2.2.1 boundsAfter
        registered good.2.1
  | reuse index available bounded vacant slack =>
    have availableAfter : read.tree.tagMapping.deassigned.back? = some index := by rw [tags];exact available
    have boundedAfter : index.toNat < read.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : read.tree.nodes.get index = none := by rw [nodes];exact vacant
    have slackAfter : readDepth.depth parent < read.tree.nodes.size := by
      change depth.depth parent < read.tree.nodes.size
      rw [nodes]
      exact slack
    refine ⟨index,good.1,?_⟩
    cases kind with
    | mutable =>
      exact GeneralBorrowFreshReuseConstructor.mutable_owned read.tree readDepth parentTag newTag parent parentNode
        parentTagAfter parentAfter freshAfter index availableAfter boundedAfter vacantAfter slackAfter fitsAfter
        offset len nonzero good.2.2.1 boundsAfter registered .Write good.2.1
    | shared =>
      exact GeneralBorrowFreshSharedConstructor.reuse_owned read.tree readDepth parentTag newTag parent parentNode
        parentTagAfter parentAfter freshAfter index availableAfter boundedAfter vacantAfter slackAfter fitsAfter
        true offset len nonzero good.2.2.1 boundsAfter registered good.2.1
end DuplicatePrefix.GeneralBorrowFreshReborrowStages
#print axioms DuplicatePrefix.GeneralBorrowFreshReborrowStages.protected_construct

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReborrowStages." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected construction stages dependency {dependency}"
