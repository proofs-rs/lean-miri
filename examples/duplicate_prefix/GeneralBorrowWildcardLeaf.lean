import duplicate_prefix.GeneralBorrowNodeUpdate
namespace DuplicatePrefix.GeneralBorrowWildcardLeaf
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem insert_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (present : nodes.get index = some value) : nodes.insert index value = nodes := by
  have valid := lookup_valid nodes index value present
  have cell : nodes.data[index.toNat]'valid = some value := by
    unfold UniValMap.get at present
    simpa only [Array.getElem?_eq_getElem valid] using present
  have data := insert_existing nodes index value value present
  rw [←cell] at data
  simp only [Array.set_getElem_self] at data
  cases nodes with
  | mk original =>
    cases result : (UniValMap.mk original).insert index value with
    | mk changed => exact congrArg UniValMap.mk (by simpa only [result] using data)

open Lean Elab Tactic in
elab "unfold_leaf_helpers" : tactic => do
  let names ← [".BorrowTree.wildcardRelatedness", ".BorrowTree.exactRelatedness?"].mapM fun (suffix : String) => do
    let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
      if name.toString.endsWith suffix then some name else none
    match candidates with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected wildcard helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| dsimp only [$[$names:ident],*]))

def unique : LocationState := ⟨.Unique,true,.None⟩

/-- A positive exposed-reference witness and exact leaf cache counters.
This is raw state data: it contains no operation-success assertion. -/
structure Data (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : BorTag) : Prop where
  present : tree.nodes.get root = some node
  leaf : node.children = #[]
  exposed : node.isExposed = true
  writable : location.perms.get root = some unique
  cache : location.exposedCache.nodes.get root = some ⟨1,1⟩
  boundedTag : node.tag.value ≤ maximum.value

/-- An additional original root can be visited successfully as a wildcard
subtree. Its exposed mutable leaf supplies the root0 exposure witness; exact
read/write counters select LocalAccess and the checked tag bound permits it.
Both read and write traverse the actual stack loop and preserve the location. -/
theorem access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (data : Data tree location root node maximum) :
    tree.performWildcardAccessAt location root (some maximum) kind protections false =
      ⟨location,.Completed⟩ := by
  have nonempty : 0 < tree.nodes.size := by
    have valid := lookup_valid tree.nodes root node data.present
    unfold UniValMap.size
    omega
  have notPast : ¬ 2 > tree.nodes.size*2+1 := by omega
  have notForeign : ¬ maximum.value < node.tag.value := by
    have lower := UInt64.le_iff_toNat_le.mp data.boundedTag
    simp only [UInt64.lt_iff_toNat_lt]
    omega
  have notPast1 : ¬ 1 > tree.nodes.size*2+1 := by omega
  have unchanged := insert_same location.perms root unique data.writable
  have related : location.exposedCache.accessRelatedness root root kind false false = some .LocalAccess := by
    cases kind <;> simp [ExposedCache.accessRelatedness,data.cache,Id.run,pure]
  have recorded : unique.recordNewAccess kind .LocalAccess = .Recorded unique := by cases kind <;> rfl
  have accessed : ∀ held, unique.performAccess kind .LocalAccess held = .Success unique ⟨.Unique,.Unique⟩ := by
    intro held
    cases kind <;> cases held <;> rfl
  have permits : (Permission.Unique.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind = true := by
    cases kind <;> rfl
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
      .yield (location,false,.Completed,#[(root,true)],1) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [data.present,data.leaf,data.writable,notForeign,related,
      LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,notPast1,Id.run,bind,pure]
    unfold_leaf_helpers
    simp [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,data.leaf]
  have step2 : scan () (location,false,.Completed,#[(root,true)],1) =
      .yield (location,true,.Completed,#[],2) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [data.present,data.leaf,data.exposed,data.writable,notForeign,related,
      notPast,Id.run,bind,pure,UniValMap.orInsert]
    all_goals try unfold_leaf_helpers
    all_goals simp [recorded,accessed,unchanged,permits,data.boundedTag,PermTransition.isNoop,
      LocationState.AccessResult.resultingState,bind,pure]
    simp [show unique.permission = Permission.Unique from rfl,permits]
  have step3 : scan () (location,true,.Completed,#[],2) = .done (location,true,.Completed,#[],2) := by
    simp [scan,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step3,bind,pure]
  rfl
end DuplicatePrefix.GeneralBorrowWildcardLeaf
