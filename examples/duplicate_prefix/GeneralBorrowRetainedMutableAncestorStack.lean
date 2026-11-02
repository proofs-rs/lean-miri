import duplicate_prefix.GeneralBorrowRetainedMutableAncestor
namespace DuplicatePrefix.GeneralBorrowRetainedMutableAncestorStack
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowRetainedMutableAccess GeneralBorrowRetainedMutableChain GeneralBorrowRetainedMutableAncestor
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
def Older (tree : BorrowTree) (newer older : Row) : Prop :=
  ∀location : LocationTree,∀position∈(source_normal_projection tree location {}).topology.ancestorPath older.index.toNat,
    position∈(source_normal_projection tree location {}).topology.ancestorPath newer.index.toNat
structure Stack (root : UniIndex) (offset len : UInt64) where
  current : Current root offset len
  ancestors : List Row
  known : ∀row∈ancestors,Handle current.state.tree current.index row
  ordered : List.Pairwise (Older current.state.tree) (⟨current.index,current.tag⟩::ancestors)

def initial {root offset len} (s : Current root offset len) : Stack root offset len :=
  {current:=s,ancestors:=[]
   known:=by intro row member;cases member
   ordered:=by simp}

theorem held {root offset len} (s : Stack root offset len) (row : Row)
    (member : row∈(⟨s.current.index,s.current.tag⟩::s.ancestors)) : Handle s.current.state.tree s.current.index row := by
  rcases List.mem_cons.mp member with equal | member
  · subst row;exact GeneralBorrowRetainedMutableAncestor.self s.current
  · exact s.known row member

/-- Every selectable ancestor has current full Write ownership derived from the
current pointer's data. No ancestor-ownership certificate is stored or assumed. -/
theorem ancestor_owned {root offset len} (s : Stack root offset len) (row : Row) (member : row∈s.ancestors) :
    GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned s.current.state.tree {} row.index .Write)
      offset (offset+len) s.current.state.tree.locations :=
  (GeneralBorrowRetainedMutableAncestor.select s.current row (s.known row member)).state.owned

def access {root offset len} (s : Stack root offset len) (kind : AccessKind) : Stack root offset len := by
  let current : Current root offset len:=⟨s.current.index,s.current.tag,(build s.current.state kind).state⟩
  have nodes:=GeneralBorrowRetainedMutableAccessFacts.build_nodes s.current.state kind
  refine ⟨current,s.ancestors,fun row member=>GeneralBorrowRetainedMutableAncestor.access s.current row (s.known row member) kind,?_⟩
  apply s.ordered.imp
  intro newer older previous location position member
  rw [GeneralBorrowRetainedMutableAncestor.topology s.current.state.tree _ nodes location] at member ⊢
  exact previous location position member

def pop {root offset len} (s : Stack root offset len) (valid : 0<s.ancestors.length) : Stack root offset len := by
  cases rows : s.ancestors with
  | nil => simp [rows] at valid
  | cons row rest =>
    have handle:=s.known row (by rw [rows];simp)
    let current:=GeneralBorrowRetainedMutableAncestor.select s.current row handle
    have tail : List.Pairwise (Older s.current.state.tree) (row::rest) := by
      have ordered:=s.ordered
      rw [rows] at ordered
      exact ordered.tail
    refine ⟨current,rest,?_,tail⟩
    intro older member
    have old:=s.known older (by rw [rows];exact List.mem_cons_of_mem _ member)
    exact ⟨old.present,old.lookup,(List.pairwise_cons.mp tail).1 older member⟩

theorem pop_length {root offset len} (s : Stack root offset len) (valid : 0<s.ancestors.length) :
    (pop s valid).ancestors.length+1=s.ancestors.length := by
  rcases s with ⟨current,ancestors,known,ordered⟩
  cases ancestors with
  | nil => simp at valid
  | cons row rest => rfl

def activate {root offset len} (s : Stack root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.current.state.tree.tagMapping tag) (positive : len≠0)
    (room : s.current.state.tree.nodes.size+5≤4294967295) : Stack root offset len := by
  let output:=GeneralBorrowRetainedMutableActivate.build s.current.state tag fresh positive room
  let current : Current root offset len:=⟨output.index,tag,output.state⟩
  let rows:=(⟨s.current.index,s.current.tag⟩:Row)::s.ancestors
  have known : ∀row∈rows,Handle current.state.tree current.index row := by
    intro row member
    exact GeneralBorrowRetainedMutableAncestor.activate s.current row (held s row member) tag fresh positive room
  refine ⟨current,rows,known,List.pairwise_cons.mpr ⟨?_,?_⟩⟩
  · intro row member
    exact (known row member).subset
  · apply s.ordered.imp_of_mem
    intro newer older newerMem olderMem previous location position member
    have newerPath:=GeneralBorrowRetainedMutableAncestor.activate_path s.current newer (held s newer newerMem) tag fresh positive room location
    have olderPath:=GeneralBorrowRetainedMutableAncestor.activate_path s.current older (held s older olderMem) tag fresh positive room location
    change position∈(source_normal_projection output.state.tree location {}).topology.ancestorPath newer.index.toNat
    rw [newerPath]
    apply previous location position
    change position∈(source_normal_projection output.state.tree location {}).topology.ancestorPath older.index.toNat at member
    rw [olderPath] at member
    exact member

theorem access_length {root offset len} (s : Stack root offset len) (kind : AccessKind) :
    (access s kind).ancestors.length=s.ancestors.length := rfl

theorem activate_length {root offset len} (s : Stack root offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.current.state.tree.tagMapping tag) (positive : len≠0)
    (room : s.current.state.tree.nodes.size+5≤4294967295) :
    (activate s tag fresh positive room).ancestors.length=s.ancestors.length+1 := by simp [activate]

theorem pop_tree {root offset len} (s : Stack root offset len) (valid : 0<s.ancestors.length) :
    (pop s valid).current.state.tree=s.current.state.tree := by
  rcases s with ⟨current,ancestors,known,ordered⟩
  cases ancestors with
  | nil => simp at valid
  | cons row rest => rfl

end
end DuplicatePrefix.GeneralBorrowRetainedMutableAncestorStack
