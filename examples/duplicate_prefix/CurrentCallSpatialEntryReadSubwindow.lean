import duplicate_prefix.CurrentCallSpatialEntryRead

namespace DuplicatePrefix.CurrentCallSpatialEntryReadSubwindow
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Recover one fixed cell's authority on an actual subwindow from the
universal saved-row frame of the SAME full-span associated Read. -/
theorem owned_subwindow {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (i : Fin role.backing.cells.size)
    (overlap : ∃ byte,Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (lower upper : UInt64)
    (requestLower : offset≤lower.toNat) (requestUpper : upper.toNat≤offset+length)
    (cellLower : role.backing.cells[i].offset≤lower.toNat)
    (cellUpper : upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length) :
    let accessed := CurrentCallSpatialEntryRead.read role frame room start amount
    OwnedOn (S05CompletedAncestryReadMutable.Authority accessed.tree role.backing.cells[i].completion
      (CurrentCallSpatialEntryRead.registeredTracker role frame room).global.protectedTags (role.roles i overlap).grant)
      lower upper accessed.tree.locations := by
  obtain ⟨contract,_,_⟩ := CurrentCallSpatialEntryRead.invoke role exclusive runtime distinct short frame room
    start amount startEq amountEq nonzero bounds
  let current := CurrentCallSpatialEntryRead.registeredRole role runtime frame room
  let accessed := CurrentCallSpatialEntryRead.read role frame room start amount
  dsimp only
  intro cursor valid positive beforeUpper afterLower
  change cursor<accessed.tree.locations.entries.size at valid
  change accessed.tree.locations.entries[cursor].range.start.toNat<upper.toNat at beforeUpper
  change lower.toNat<accessed.tree.locations.entries[cursor].range.stop.toNat at afterLower
  have segmentPositive := (GeneralRangeMapGeometry.facts accessed.tree.locations contract.well (by omega)).2.1 cursor valid
  let point := max lower.toNat accessed.tree.locations.entries[cursor].range.start.toNat
  have pointLower : lower.toNat≤point := Nat.le_max_left _ _
  have pointUpper : point<upper.toNat := by dsimp only [point];omega
  have rowLower : accessed.tree.locations.entries[cursor].range.start.toNat≤point := Nat.le_max_right _ _
  have rowUpper : point<accessed.tree.locations.entries[cursor].range.stop.toNat := by dsimp only [point];omega
  have pointFits : point<2^64 := Nat.lt_trans pointUpper (UInt64.toNat_lt upper)
  have pointEq : (UInt64.ofNat point).toNat=point := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt pointFits]
  have atPoint : ValueAt accessed.tree.locations (UInt64.ofNat point) accessed.tree.locations.entries[cursor].data :=
    ⟨cursor,valid,by rw [pointEq];exact rowLower,by rw [pointEq];exact rowUpper,rfl⟩
  have request : Window role.backing.id offset length (role.backing.id,(UInt64.ofNat point).toNat) :=
    ⟨rfl,by rw [pointEq];omega,by rw [pointEq];omega⟩
  have cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length
      (role.backing.id,(UInt64.ofNat point).toNat) := ⟨rfl,by rw [pointEq];exact Nat.le_trans cellLower pointLower,by rw [pointEq];omega⟩
  have original := recover current accessed.tree.locations contract.frames (UInt64.ofNat point)
    accessed.tree.locations.entries[cursor].data atPoint request i overlap cell
  rw [CurrentCallSpatialEntryRead.grant role runtime frame room i overlap] at original
  intro index node present
  rw [contract.nodes] at present
  exact original index node present

end
end DuplicatePrefix.CurrentCallSpatialEntryReadSubwindow
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialEntryReadSubwindow.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Read subwindow dependency {dependency}"
