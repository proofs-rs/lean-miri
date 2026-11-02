import duplicate_prefix.GeneralBorrowSharedBankMixedGeneration

namespace DuplicatePrefix.GeneralBorrowSharedBankConcreteReplay
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankMixedAction
open DuplicatePrefix.GeneralBorrowSharedBankMixedHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Concrete chronological requests. Selected parent tags and retained GC tags
are recorded as data, independently of any operation result. -/
inductive Event where
  | borrow (tag : BorTag) (position : Nat) (parentTag : BorTag)
  | gc (extra retained : Array BorTag)
  | exposeRoot
  | rootAccess (kind : AccessKind)

def erase : Event → Action
  | .borrow tag position _ => .borrow tag position
  | .gc extra _ => .gc extra
  | .exposeRoot => .exposeRoot
  | .rootAccess kind => .rootAccess kind

def borrowRead (tree : BorrowTree) (parentTag : BorTag) (offset len : UInt64) :=
  tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read {} .VisitChildrenOfAccessed

def borrowChild (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  (borrowRead tree parentTag offset len).tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false

/-- Raw operation replay has no State, ownership, allocator or success input. -/
def step (rootTag : BorTag) (offset len : UInt64) (tree : BorrowTree) : Event → BorrowTree
  | .borrow tag _ parentTag => (borrowChild tree parentTag tag offset len).tree
  | .gc extra retained => (tree.removeUnreachableTags (extra ++ retained)).tree
  | .exposeRoot => (tree.exposeTag {} rootTag).tree
  | .rootAccess kind => (tree.performNormalAccessRange rootTag (Size.ofBytes offset)
      (Size.ofBytes len) kind {} .VisitChildrenOfAccessed).tree

def execute (rootTag : BorTag) (offset len : UInt64) (tree : BorrowTree) : List Event → BorrowTree
  | [] => tree
  | event :: rest => execute rootTag offset len (step rootTag offset len tree event) rest

def Completed (rootTag : BorTag) (offset len : UInt64) (tree : BorrowTree) : Event → Prop
  | .borrow tag _ parentTag => (borrowRead tree parentTag offset len).status = .Completed ∧
      (borrowChild tree parentTag tag offset len).outcome = .ok ()
  | .gc extra retained => (tree.removeUnreachableTags (extra ++ retained)).outcome = .ok ()
  | .exposeRoot => (tree.exposeTag {} rootTag).outcome = .ok ()
  | .rootAccess kind => (tree.performNormalAccessRange rootTag (Size.ofBytes offset)
      (Size.ofBytes len) kind {} .VisitChildrenOfAccessed).status = .Completed

/-- A conclusion about every chronological operation, not a validity definition. -/
def AllCompleted (rootTag : BorTag) (offset len : UInt64) (tree : BorrowTree) : List Event → Prop
  | [] => True
  | event :: rest => Completed rootTag offset len tree event ∧
      AllCompleted rootTag offset len (step rootTag offset len tree event) rest

/-- The abstract bank protocol supplies an exact concrete source-operation
replay, with all intermediate completions. No replay success is assumed. -/
theorem of_run {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    {positive : len ≠ 0} {terminal : BorTag}
    {s final : GeneralBorrowSharedRootBankState.State root rootTag offset len}
    {actions : List Action} (history : Run positive terminal s actions final) :
    ∃ events, events.map erase = actions ∧
      execute rootTag offset len s.bank.tree events = final.bank.tree ∧
      AllCompleted rootTag offset len s.bank.tree events := by
  induction history with
  | nil s => exact ⟨[],rfl,rfl,True.intro⟩
  | borrow s tag position rest valid fresh room readDone childDone tail ih =>
    obtain ⟨events,erased,actual,done⟩ := ih
    let selected := GeneralBorrowSharedRootBankState.select s
      (GeneralBorrowSharedRootBankHistory.parent s position valid)
      (GeneralBorrowSharedRootBankHistory.parent_mem s position valid)
    let data := GeneralBorrowRecursiveSharedHistory.supplied selected tag fresh positive
    let event := Event.borrow tag position data.parentTag
    have frame : step rootTag offset len s.bank.tree event =
        (GeneralBorrowSharedRootBankAdvance.next s
          (GeneralBorrowSharedRootBankHistory.parent s position valid)
          (GeneralBorrowSharedRootBankHistory.parent_mem s position valid) tag fresh positive room).bank.tree := rfl
    refine ⟨event :: events,?_,?_,?_⟩
    · simp only [List.map_cons,erase,event,erased]
    · simpa only [execute,frame] using actual
    · exact ⟨⟨readDone,childDone⟩,frame ▸ done⟩
  | gc s extra rest fresh completed tail ih =>
    obtain ⟨events,erased,actual,done⟩ := ih
    let retained := (s.bank.handles.filterMap fun index => (s.bank.tree.nodes.get index).map TreeNode.tag).toArray
    let event := Event.gc extra retained
    have frame : step rootTag offset len s.bank.tree event =
        (GeneralBorrowSharedBankGcAction.next s positive terminal fresh extra).bank.tree :=
      (GeneralBorrowSharedBankGcAction.tree s positive terminal fresh extra).symm
    refine ⟨event :: events,?_,?_,?_⟩
    · simp only [List.map_cons,erase,event,erased]
    · simpa only [execute,frame] using actual
    · exact ⟨completed,frame ▸ done⟩
  | exposeRoot s rest completed tail ih =>
    obtain ⟨events,erased,actual,done⟩ := ih
    refine ⟨.exposeRoot :: events,by simp only [List.map_cons,erase,erased],?_,?_⟩
    · exact actual
    · exact ⟨completed,done⟩
  | rootAccess s kind rest fresh completed tail ih =>
    obtain ⟨events,erased,actual,done⟩ := ih
    have frame : step rootTag offset len s.bank.tree (.rootAccess kind) =
        (GeneralBorrowSharedRootAccess.next s terminal fresh kind).bank.tree :=
      (GeneralBorrowSharedRootAccess.tree s terminal fresh kind).symm
    refine ⟨.rootAccess kind :: events,by simp only [List.map_cons,erase,erased],?_,?_⟩
    · simpa only [execute,frame] using actual
    · exact ⟨completed,frame ▸ done⟩

/-- Static parent-position choices, fresh tags and room form the concrete
chronological replay and every completion internally. These inputs describe
resources; none asserts the success of an operation or a prior execution. -/
theorem generate {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (terminal : BorTag) (terminalFresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping terminal)
    (actions : List Action) (choices : Choices s.bank.handles.length actions)
    (unique : (tags actions).Nodup) (terminalUnused : terminal ∉ tags actions)
    (fresh : ∀ tag ∈ tags actions, GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (room : s.bank.tree.nodes.size+(tags actions).length+4 ≤ 4294967295) :
    ∃ (final : GeneralBorrowSharedRootBankState.State root rootTag offset len) (events : List Event),
      Run positive terminal s actions final ∧ events.map erase = actions ∧
      execute rootTag offset len s.bank.tree events = final.bank.tree ∧
      AllCompleted rootTag offset len s.bank.tree events := by
  obtain ⟨final,history,_⟩ := GeneralBorrowSharedBankMixedHistory.generate s positive terminal terminalFresh
    actions choices unique terminalUnused fresh room
  obtain ⟨events,erased,actual,completed⟩ := of_run history
  exact ⟨final,events,history,erased,actual,completed⟩


/-- Real allocation forms the initial graph, allocator, permissions and parent
selection bank before replay. No initial physical tree certificate is an input.
The result concerns permission operations, not arbitrary MIR byte-writing callers. -/
theorem allocated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (offset len : UInt64) (positive : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (actions : List Action) (choices : Choices 1 actions) (unique : (tags actions).Nodup)
    (rootUnused : rootTag ∉ tags actions) (tagUnused : tag ∉ tags actions)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: tags actions)
    (room : 1+(tags actions).length+4 ≤ 4294967295) :
    ∃ (final : GeneralBorrowSharedRootBankState.State GeneralBorrowFullSharedSeed.root rootTag offset len)
      (events : List Event), events.map erase = actions ∧
      execute rootTag offset len (BorrowTree.new rootTag (Size.ofBytes capacity)) events = final.bank.tree ∧
      AllCompleted rootTag offset len (BorrowTree.new rootTag (Size.ofBytes capacity)) events ∧
      GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping tag ∧
      (∀ i, GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping (reserve i)) := by
  let generated := GeneralBorrowSharedBankMixedGeneration.generate capacity nonzero rootTag tag different
    offset len positive bounds actions choices unique rootUnused tagUnused reserve reserved room
  obtain ⟨events,erased,actual,completed⟩ := of_run generated.history
  exact ⟨generated.state,events,erased,actual,completed,generated.fresh,generated.reserved⟩

end DuplicatePrefix.GeneralBorrowSharedBankConcreteReplay

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowSharedBankConcreteReplay." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved concrete replay dependency {dependency}"
