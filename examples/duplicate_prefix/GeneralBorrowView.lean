import duplicate_prefix.GeneralBorrowSifa
namespace DuplicatePrefix.GeneralBorrowView
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
abbrev StateShape := Permission × Bool
abbrev NodeShape := BorTag × Option UniIndex × Array UniIndex × Permission

def stateShape (state : LocationState) : StateShape := (state.permission,state.accessed)
def nodeShape (node : TreeNode) : NodeShape := (node.tag,node.parent,node.children,node.defaultInitialPermission)
def locationShape (location : LocationTree) : Array (Option StateShape) := location.perms.data.map (Option.map stateShape)
def treeShape (tree : BorrowTree) :=
  (tree.tagMapping,tree.nodes.data.map (Option.map nodeShape),
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)),tree.roots)

theorem insert_existing_shape {α β : Type} (shape : α → β) (nodes : UniValMap α)
    (index : UniIndex) (old next : α) (present : nodes.get index = some old) (same : shape next = shape old) :
    (nodes.insert index next).data.map (Option.map shape) = nodes.data.map (Option.map shape) := by
  have valid := lookup_valid nodes index old present
  have slot : nodes.data[index.toNat] = some old := by
    simpa only [UniValMap.get,Array.getElem?_eq_getElem valid] using present
  rw [insert_existing nodes index old next present]
  apply Array.ext
  · simp
  · intro position left right
    simp only [Array.getElem_map,Array.getElem_set]
    by_cases equal : index.toNat = position
    · subst position
      simp [slot,same]
    · simp [equal]

def weakenLocation (location : LocationTree) (index : UniIndex) (strongest : IdempotentForeignAccess) : LocationTree :=
  match location.perms.get index with
  | none => location
  | some state => {location with perms := location.perms.insert index ({state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1})}

theorem weaken_location_shape (location : LocationTree) (index : UniIndex) (strongest : IdempotentForeignAccess) :
    locationShape (weakenLocation location index strongest) = locationShape location := by
  unfold weakenLocation
  cases present : location.perms.get index with
  | none => rfl
  | some state => exact insert_existing_shape stateShape location.perms index state _ present rfl

theorem weakened_tree_shape (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (strongest : IdempotentForeignAccess) :
    treeShape (GeneralBorrowSifa.weakened tree index node strongest) = treeShape tree := by
  have nodeEq := insert_existing_shape nodeShape tree.nodes index node
    {node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1} present rfl
  have locationsEq : ((GeneralBorrowSifa.weakened tree index node strongest).locations.entries.map
      (fun segment => (segment.range,locationShape segment.data))) =
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) := by
    apply Array.ext
    · simp [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll]
    · intro position left right
      have valid : position < tree.locations.entries.size := by simpa only [Array.size_map] using right
      simp only [GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.getElem_map]
      exact congrArg (fun value => ((tree.locations.entries[position]'valid).range,value))
        (weaken_location_shape (tree.locations.entries[position]'valid).data index strongest)
  have actualNodeEq : (GeneralBorrowSifa.weakened tree index node strongest).nodes.data.map (Option.map nodeShape) =
      tree.nodes.data.map (Option.map nodeShape) := nodeEq
  change (tree.tagMapping,(GeneralBorrowSifa.weakened tree index node strongest).nodes.data.map (Option.map nodeShape),
    (GeneralBorrowSifa.weakened tree index node strongest).locations.entries.map
      (fun segment => (segment.range,locationShape segment.data)),tree.roots) =
    (tree.tagMapping,tree.nodes.data.map (Option.map nodeShape),
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)),tree.roots)
  rw [actualNodeEq,locationsEq]
end DuplicatePrefix.GeneralBorrowView

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowView." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic permission-view dependency {dependency}"
