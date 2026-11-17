import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAccessClosed
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSkipFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowSparseLeafCallback
open GeneralBorrowExposedScopedInactiveWritableAccessData (Data)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
open Lean Elab Tactic in
elab "name_inactive_skip_scan" : tactic => do
  liftMetaTactic fun goal=>goal.withContext do
    let target←goal.getType
    let some loop:=target.find? (fun expr=>expr.isAppOf ``ForIn.forIn)
      | throwError "expected actual ordered root loop"
    let body:=loop.getAppArgs.back!
    let goal←goal.define `scan (←Lean.Meta.inferType body) body
    let (scan,goal)←goal.intro1P
    return [←goal.change (target.replace fun expr=>if expr==body then some (mkFVar scan) else none)]

/-- The real nonleaf Skip mode retains its actual minimum-exposure cutoff and
stop flag. Every visited old root executes its real callback; stopped suffixes
stay unchanged. No leaf, minimum-none or Visit-equivalence premise is used. -/
theorem frame (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (kind : AccessKind) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat→Prop) (data : Data tree location protections anchor selected head tail support) :
    let result:=source_tree_access_at tree location (some anchor) kind protections .SkipChildrenOfAccessed range
    source_access_status result=none ∧ (source_access_location result).exposedCache=location.exposedCache ∧
    Writable tree protections area.support (source_access_location result) ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    (∀query,¬area.support query→(source_access_location result).perms.get query=
      (tree.performNormalAccessAt location anchor kind protections .SkipChildrenOfAccessed).location.perms.get query) := by
  let normalLocation:=(tree.performNormalAccessAt location anchor kind protections .SkipChildrenOfAccessed).location
  have normal:=GeneralBorrowExposedScopedInactiveExposureNormal.access tree location protections anchor kind .SkipChildrenOfAccessed data.base.base.forest
    data.base.base.component (GeneralBorrowExposedScopedInactiveWritableAccessData.owned data kind) context.depth context.children context.anchorNode context.anchorPresent
    data.base.base.ancestors data.base.base.coherent
  have normalWritable : Writable tree protections area.support normalLocation := by
    intro query node member present
    have same:=normal.2.2.2.2 query node present (data.base.base.separate query member)
    change GeneralBorrowExposedConditionalWritePermissions.Compatible
      ((tree.performNormalAccessAt location anchor kind protections .SkipChildrenOfAccessed).location.perms.get query |>.getD node.defaultLocationState)
      .LocalAccess (protections.contains node.tag)
    rw [same];exact data.writableLeaves query node member present
  have rootEq : (tree.performNormalAccessAt location anchor kind protections .SkipChildrenOfAccessed).access.root=selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans data.base.base.rootPath
  simp_tree_helpers
  simp only [normal.1,normal.2.1,rootEq,index_self,context.selectedPresent,context.roots,Option.bind_some,Option.map_some,beq_self_eq_true]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,List.size_toArray,List.length_cons]
  name_inactive_skip_scan
  let property := fun state : LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool=>
    state.2.1=none ∧ state.1.exposedCache=location.exposedCache ∧
    Writable tree protections area.support state.1 ∧ GeneralBorrowExposureCardinality.LocationCoherent tree state.1 protections ∧
    (∀query,¬area.support query→state.1.perms.get query=normalLocation.perms.get query)
  have step : ∀position∈List.range' 0 (tail.length+1),∀state,property state→property (scan position state).value := by
    intro position member state good
    rcases state with ⟨current,status,stopped⟩
    rcases good with ⟨statusEq,cache,ready,coherent,keep⟩
    dsimp only at statusEq
    subst status
    have untouched (stop : Bool) : property (current,none,stop) := ⟨rfl,cache,ready,coherent,keep⟩
    cases stopped with
    | true=>simpa only [scan,Option.isNone_none,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte,ForInStep.value] using untouched true
    | false=>
      cases lookup : (head::tail)[position]? with
      | none=>simpa only [scan,Option.isNone_none,Bool.not_false,Bool.and_self,↓reduceIte,List.getElem?_toArray,lookup,ForInStep.value] using untouched false
      | some root=>
        have memberRoot : root∈head::tail:=List.mem_of_getElem? lookup
        by_cases same : root=selected
        · simp only [scan,Option.isNone_none,Bool.not_false,Bool.and_self,↓reduceIte,List.getElem?_toArray,lookup,
            same,beq_self_eq_true,bne_self_eq_false,Bool.and_true,Bool.true_and,Option.bind_some,context.selectedPresent,Option.map_some]
          repeat' first | exact untouched false | split
        · have included : area.support root := by
            rcases List.mem_cons.mp memberRoot with equal | member
            · subst root
              let first:=data.base.base.primary same
              exact first.base.included head first.base.rooted
            · let other:=data.base.base.virtual root member same
              exact other.included root other.rooted
          obtain ⟨node,present,leaf,exposed⟩:=data.leaves root included
          obtain ⟨after,called,finalCoherent,finalCache,finalReady,others⟩:=GeneralBorrowSparseLeafCallback.step tree current protections area.support root node
            (some context.selectedNode.tag) kind (position != 0) present leaf exposed included coherent data.short ready
            (by intro tag equal;cases equal;exact context.tags root node included present)
          have changed : property (after,none,false) := ⟨rfl,finalCache.trans cache,finalReady,finalCoherent,
            fun query outside=>(others query (by intro equal;subst query;exact outside included)).trans (keep query outside)⟩
          simp only [scan,Option.isNone_none,Bool.not_false,Bool.and_self,↓reduceIte,List.getElem?_toArray,lookup,
            beq_self_eq_true,Bool.and_true,Bool.true_and,Option.bind_some,context.selectedPresent,Option.map_some,
            beq_eq_false_iff_ne.mpr (show some selected≠some root from fun equal=>same (Option.some.inj equal).symm),
            Bool.not_false,called,bne_self_eq_false]
          repeat' first | exact untouched false | exact changed | split
  have initial : property (normalLocation,none,false):=⟨rfl,normal.2.2.1,normalWritable,normal.2.2.2.1,fun _ _=>rfl⟩
  have final:=GeneralBorrowLoop.list_invariant _ scan property step _ initial
  exact ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSkipFrame
