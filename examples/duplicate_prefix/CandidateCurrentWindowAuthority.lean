import duplicate_prefix.CandidateCurrentUniformOwnerWindow
import duplicate_prefix.S05WildcardFnEntryRaw
import duplicate_prefix.S05ConcreteFnEntryDisjoint

/-! Convert uniform current content rights to the segment authority consumed by
actual FnEntry borrowing. No operation-success assumption occurs here. -/
namespace DuplicatePrefix.CandidateCurrentWindowAuthority
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins
set_option autoImplicit false

theorem owned (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (precise : PreciseAllocation) (pointer : PointerInstance)
    (well : allocation.extra.locations.WellFormed)
    (offset len : UInt64) (sum : (offset+len).toNat = offset.toNat+len.toNat)
    (mode : CandidateFreezeContentResources.Mode) (write : mode ≠ .read)
    (rights : ∀ byte, offset.toNat ≤ byte → byte < offset.toNat+len.toNat →
      RawRights allocation held precise pointer byte mode) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority allocation.extra precise.completion held pointer.grant)
      offset (offset+len) allocation.extra.locations := by
  intro position valid positive start stop
  let byte := max offset.toNat allocation.extra.locations.entries[position].range.start.toNat
  have lower : offset.toNat ≤ byte := Nat.le_max_left _ _
  have begin : allocation.extra.locations.entries[position].range.start.toNat ≤ byte := Nat.le_max_right _ _
  have upper : byte < offset.toNat+len.toNat := by
    dsimp only [byte]
    rw [sum] at positive start
    omega
  have endAt : byte < allocation.extra.locations.entries[position].range.stop.toNat := by
    dsimp only [byte]
    have segment := (GeneralRangeMapGeometry.facts allocation.extra.locations well (by omega)).2.1 position valid
    omega
  intro index node present
  have raw := rights byte lower upper allocation.extra.locations.entries[position]
    (Array.mem_toList_iff.mpr (Array.getElem_mem valid)) begin endAt index node present
  simpa only [Allows,write,ite_false,GeneralBorrowExposedConditionalWritePermissions.Compatible,
    OrdinaryBorrowAuthority.LocalWrite,OrdinaryBorrowAuthority.ForeignWrite] using raw

/-- A current graph selects an actual physical root for the fixed grant. -/
theorem root_path (tree : BorrowTree)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (grant : UniIndex) (node : TreeNode) (present : tree.nodes.get grant = some node) :
    ∃ (position : Nat) (root : UniIndex) (rootNode : TreeNode), tree.roots[position]? = some root ∧
      tree.nodes.get root = some rootNode ∧ GeneralBorrowExposedNonleafPrimaryPath.Path tree root grant := by
  obtain ⟨depth⟩ := graph.depth
  have walk : ∀ fuel index current, tree.nodes.get index = some current → depth.depth index < fuel →
      ∃ root rootNode, root ∈ tree.roots.toList ∧ tree.nodes.get root = some rootNode ∧
        GeneralBorrowExposedNonleafPrimaryPath.Path tree root index := by
    intro fuel
    induction fuel with
    | zero => intro index current present bound; omega
    | succ fuel ih =>
      intro index current present bound
      cases edge : current.parent with
      | none => exact ⟨index,current,graph.covered index current present edge,present,.refl index current present⟩
      | some parent =>
        obtain ⟨parentNode,parentPresent,smaller⟩ := depth.parent index current present parent edge
        obtain ⟨root,rootNode,member,rootPresent,path⟩ := ih parent parentNode parentPresent (by omega)
        exact ⟨root,rootNode,member,rootPresent,.step path current present edge⟩
  obtain ⟨root,rootNode,member,rootPresent,path⟩ := walk (depth.depth grant+1) grant node present (by omega)
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  exact ⟨position,root,rootNode,by simpa [same] using (Array.getElem?_eq_getElem valid),rootPresent,path⟩

/-- Nat claim endpoints fit UInt64 by the physical allocation bound. -/
theorem nat_window (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (precise : PreciseAllocation) (pointer : PointerInstance) (id : AllocId)
    (offset length : Nat) (mode : CandidateFreezeContentResources.Mode)
    (positive : 0 < length) (write : mode ≠ .read)
    (well : allocation.extra.locations.WellFormed) (room : allocation.len < 2^64)
    (rights : ∀ byte, Window id offset length byte →
      byte.2 < allocation.len ∧ RawRights allocation held precise pointer byte.2 mode) :
    offset+length ≤ allocation.len ∧
    (UInt64.ofNat offset).toNat = offset ∧ (UInt64.ofNat length).toNat = length ∧
    (UInt64.ofNat offset+UInt64.ofNat length).toNat = offset+length ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority allocation.extra precise.completion held pointer.grant)
      (UInt64.ofNat offset) (UInt64.ofNat offset+UInt64.ofNat length) allocation.extra.locations := by
  have last := (rights (id,offset+length-1) ⟨rfl,by omega,by omega⟩).1
  have bounds : offset+length ≤ allocation.len := by omega
  have offsetFits : offset < 2^64 := by omega
  have lengthFits : length < 2^64 := by omega
  have sumFits : offset+length < 2^64 := by omega
  have offsetEq : (UInt64.ofNat offset).toNat = offset := by simp [Nat.mod_eq_of_lt offsetFits]
  have lengthEq : (UInt64.ofNat length).toNat = length := by simp [Nat.mod_eq_of_lt lengthFits]
  have sumEq : (UInt64.ofNat offset+UInt64.ofNat length).toNat = offset+length := by
    rw [UInt64.toNat_add,offsetEq,lengthEq,Nat.mod_eq_of_lt sumFits]
  refine ⟨bounds,offsetEq,lengthEq,sumEq,?_⟩
  apply owned allocation held precise pointer well (UInt64.ofNat offset) (UInt64.ofNat length)
    (by rw [sumEq,offsetEq,lengthEq]) mode write
  intro byte lower upper
  apply (rights (id,byte) ⟨rfl,?_,?_⟩).2
  · simpa only [offsetEq] using lower
  · simpa only [offsetEq,lengthEq] using upper

end DuplicatePrefix.CandidateCurrentWindowAuthority

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentWindowAuthority." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current window authority dependency {dependency}"
