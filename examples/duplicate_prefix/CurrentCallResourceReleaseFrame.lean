import duplicate_prefix.CurrentCallResourceRelease
import duplicate_prefix.S02HiddenLeafQuietTreeAccess
import duplicate_prefix.S05CurrentReleaseIterator

namespace DuplicatePrefix.CurrentCallResourceReleaseFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposureCardinality
open GeneralBorrowExposedNonleafPrimaryPath BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

theorem preserve {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (concrete : ∃ suppliedId tag,W.pointer.value.provenance=.concrete suppliedId tag)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536)
    (node : TreeNode) (present : W.allocation.extra.nodes.get W.pointer.grant=some node)
    (hidden : node.isExposed=false) (start amount : UInt64)
    (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (positive : start.toNat<(start+amount).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra W.pointer.grant .Write start (start+amount))
    (targetLower targetUpper : UInt64) (targetPositive : targetLower.toNat<targetUpper.toNat)
    (disjoint : (start+amount).toNat≤targetLower.toNat ∨ targetUpper.toNat≤start.toNat)
    (predicate : LocationTree→Prop)
    (owned : OwnedOn predicate targetLower targetUpper W.allocation.extra.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetAt : W.allocation.extra.nodes.get target=some targetNode)
    (targetLeaf : targetNode.children=#[]) (targetHidden : targetNode.isExposed=false) (different : target≠W.pointer.grant)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra target .Write targetLower targetUpper) :
    let result:=W.allocation.extra.releaseProtector node.tag tracker.global.protectedTags
    OwnedOn predicate targetLower targetUpper result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree target .Write targetLower targetUpper := by
  obtain ⟨G⟩:=geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) exclusive
  have witness (position : Nat) (valid : position<W.allocation.extra.locations.entries.size)
      (lower : W.allocation.extra.locations.entries[position].range.start.toNat<(start+amount).toNat)
      (upper : start.toNat<W.allocation.extra.locations.entries[position].range.stop.toNat) :
      ∃ byte : AllocId × Nat,Window id offset length byte ∧
        W.allocation.extra.locations.entries[position].range.start.toNat≤byte.2 ∧
        byte.2<W.allocation.extra.locations.entries[position].range.stop.toNat := by
    have segmentPositive:=(GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
    by_cases earlier : start.toNat≤W.allocation.extra.locations.entries[position].range.start.toNat
    · exact ⟨(id,W.allocation.extra.locations.entries[position].range.start.toNat),⟨rfl,by omega,by omega⟩,Nat.le_refl _,segmentPositive⟩
    · exact ⟨(id,start.toNat),⟨rfl,by omega,by omega⟩,by omega,upper⟩
  let P:=fun (range : ByteRange) (location : LocationTree)=>
    LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location ∧
    (range.start.toNat<targetUpper.toNat→targetLower.toNat<range.stop.toNat→predicate location) ∧
    (∀ point : UInt64,range.start.toNat≤point.toNat→point.toNat<range.stop.toNat→∀ state,
      location.perms.get target=some state→state.accessed=true→∀ kind,state.permission.associatedAccess=some kind→
      targetLower.toNat≤point.toNat ∧ point.toNat<targetUpper.toNat)
  have rows : S05CurrentReleaseIterator.Rows P W.allocation.extra.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid,
      (fun lower upper=>owned position valid targetPositive lower upper),by
        intro point lower upper state stored accessed kind associated
        have initial:=targetActive point _ ⟨position,valid,lower,upper,rfl⟩ state stored accessed kind associated
        exact ⟨initial.1,initial.2.1⟩⟩
  have activeRows:=GeneralBorrowFreshActiveWithin.active_on _ _ .Write start (start+amount) runtime.formed.well active
  have mapped:=runtime.formed.allocator.nodeTags W.pointer.grant node present
  obtain ⟨_,_,afterRows,_,_,_⟩:=S05CurrentReleaseIterator.release W.allocation.extra tracker.global.protectedTags
    node.tag W.pointer.grant node present hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨lower,upper,_⟩:=activeRows position valid state stored accessed kind associated
      obtain ⟨byte,byteInside,low,high⟩:=witness position valid lower upper
      have member : W.allocation.extra.locations.entries[position]∈W.allocation.extra.locations.entries.toList:=Array.mem_toList_iff.mpr (Array.getElem_mem valid)
      have current:=rows position valid
      have outside : ¬ (W.allocation.extra.locations.entries[position].range.start.toNat < targetUpper.toNat ∧
          targetLower.toNat < W.allocation.extra.locations.entries[position].range.stop.toNat) := by
        have activeAtStart := active W.allocation.extra.locations.entries[position].range.start W.allocation.extra.locations.entries[position].data
          ⟨position,valid,Nat.le_refl _,(GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid,rfl⟩
          state stored accessed kind associated
        -- Whole active rows lie inside the W.pointer.grant interval by pointwise activity.
        have insideStop : W.allocation.extra.locations.entries[position].range.stop.toNat ≤ (start+amount).toNat := by
          by_cases greater : W.allocation.extra.locations.entries[position].range.stop.toNat ≤ (start+amount).toNat
          · exact greater
          have atEnd := active (start+amount) W.allocation.extra.locations.entries[position].data
            ⟨position,valid,by omega,by omega,rfl⟩ state stored accessed kind associated
          omega
        intro overlaps
        rcases disjoint with left | right <;> omega
      have nextActive : ∀ point : UInt64, W.allocation.extra.locations.entries[position].range.start.toNat ≤ point.toNat →
          point.toNat < W.allocation.extra.locations.entries[position].range.stop.toNat → ∀ state,
          (source_access_location (source_tree_access_at W.allocation.extra W.allocation.extra.locations.entries[position].data (some W.pointer.grant) kind tracker.global.protectedTags
            .SkipChildrenOfAccessed W.allocation.extra.locations.entries[position].range)).perms.get target = some state → state.accessed = true →
          ∀ accessKind, state.permission.associatedAccess = some accessKind → targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat := by
        intro point atStart atStop state afterStored afterAccessed accessKind afterAssociated
        by_cases inside : targetLower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
        · exact inside
        have quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective W.allocation.extra.locations.entries[position].data target targetNode) := by
          cases beforeStored : W.allocation.extra.locations.entries[position].data.perms.get target with
          | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,beforeStored,Option.getD_none,TreeNode.defaultLocationState]
          | some old =>
            simp only [GeneralBorrowWildcardVirtualLeaf.effective,beforeStored,Option.getD_some]
            by_cases cell : old.permission = .Cell
            · exact .inr cell
            · left
              cases h : old.accessed with
              | false => rfl
              | true =>
                have associated : ∃ k,old.permission.associatedAccess = some k := by cases p : old.permission <;> simp_all [Permission.associatedAccess]
                obtain ⟨k,associated⟩ := associated
                exact False.elim (inside (current.2.2.2.2 point atStart atStop old beforeStored h k associated))
        obtain ⟨normal⟩:=CurrentCallResourceAccess.selected_normal W G exclusive byte byteInside _ member low high current.2.1 current.2.2.1
        have afterQuiet := (S02HiddenLeafQuietTreeAccess.concrete W.allocation.extra runtime.formed.toGraphState W.allocation.extra.locations.entries[position].data tracker.global.protectedTags
          target W.pointer.grant targetNode node targetAt present targetLeaf targetHidden different normal current.1 kind .SkipChildrenOfAccessed
          W.allocation.extra.locations.entries[position].range quiet).1
        change S02HiddenLeafQuietNormal.Quiet (((source_access_location (source_tree_access_at W.allocation.extra W.allocation.extra.locations.entries[position].data (some W.pointer.grant) kind tracker.global.protectedTags
          .SkipChildrenOfAccessed W.allocation.extra.locations.entries[position].range)).perms.get target).getD targetNode.defaultLocationState) at afterQuiet
        rw [afterStored] at afterQuiet
        rcases afterQuiet with inactive | cell
        · simp only [Option.getD_some] at inactive;rw [afterAccessed] at inactive;cases inactive
        · simp only [Option.getD_some] at cell;rw [cell,Permission.associatedAccess] at afterAssociated;cases afterAssociated
      cases kind with
      | Read =>
        have result:=CurrentCallResourceRead.concrete_read W G exclusive byte byteInside _ member low high concrete distinct current.1 short current.2.1 current.2.2.1
          .SkipChildrenOfAccessed W.allocation.extra.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,(fun lower upper=>False.elim (outside ⟨lower,upper⟩)),nextActive⟩
      | Write =>
        have result:=CurrentCallResourceAccess.concrete_write W G exclusive byte byteInside _ member low high concrete distinct current.1 short current.2.1 current.2.2.1
          .SkipChildrenOfAccessed W.allocation.extra.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,(fun lower upper=>False.elim (outside ⟨lower,upper⟩)),nextActive⟩)
  constructor
  · intro position valid _ lower upper
    exact (afterRows position valid).2.2.2.1 lower upper
  · intro point location atPoint state stored accessed kind associated
    obtain ⟨position,valid,lower,upper,dataEq⟩:=atPoint
    have inside:=(afterRows position valid).2.2.2.2 point lower upper state (by rw [dataEq];exact stored) accessed kind associated
    exact ⟨inside.1,inside.2,by intro impossible;cases impossible⟩

end
end DuplicatePrefix.CurrentCallResourceReleaseFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceReleaseFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource release-frame dependency {dependency}"
