import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowMultiRootGap
namespace DuplicatePrefix.PrimaryWitnessCountermodel
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def tag (n : UInt64) (nonzero : n ≠ 0 := by decide) : BorTag := ⟨n, nonzero⟩
def n0 : TreeNode := ⟨tag 1,none,#[ix 1,ix 3],.Disabled,.None,false,none⟩
def n1 : TreeNode := ⟨tag 9,some (ix 0),#[ix 2],.Disabled,.None,false,none⟩
def n2 : TreeNode := ⟨tag 2,some (ix 1),#[],.Disabled,.None,true,none⟩
def n3 : TreeNode := ⟨tag 10,some (ix 0),#[],.Disabled,.None,true,none⟩
def n4 : TreeNode := ⟨tag 5,none,#[],.Disabled,.None,false,none⟩
def location : LocationTree := {
  perms := ⟨#[some ⟨.Unique,true,.None⟩,some ⟨.Disabled,false,.None⟩,
    some ⟨.Cell,true,.None⟩,some ⟨.Cell,true,.None⟩,some ⟨.Unique,true,.None⟩]⟩
  exposedCache := ⟨⟨#[some ⟨2,2⟩,some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩]⟩⟩ }
def tree : BorrowTree := ⟨⟨#[(n0.tag,ix 0),(n1.tag,ix 1),(n2.tag,ix 2),(n3.tag,ix 3),(n4.tag,ix 4)],#[]⟩,
  ⟨#[some n0,some n1,some n2,some n3,some n4]⟩,RangeMapNonempty.homogeneous 1 location,#[ix 0,ix 4]⟩

theorem entries_exact : tree.nodes.entries.toList = [(ix 0,n0),(ix 1,n1),(ix 2,n2),(ix 3,n3),(ix 4,n4)] := by
  with_unfolding_all rfl

theorem lookup_cases (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    (index=ix 0 ∧ node=n0) ∨ (index=ix 1 ∧ node=n1) ∨ (index=ix 2 ∧ node=n2) ∨
    (index=ix 3 ∧ node=n3) ∨ (index=ix 4 ∧ node=n4) := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  change index.toNat < 5 at valid
  have cases : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 ∨ index.toNat=3 ∨ index.toNat=4 := by omega
  rcases cases with h | h | h | h | h
  · have same : index = ix 0 := GeneralBorrowNodeUpdate.index_injective index (ix 0) h
    subst index
    have eq : node = n0 := Option.some.inj present.symm
    subst node
    simp
  · have same : index = ix 1 := GeneralBorrowNodeUpdate.index_injective index (ix 1) h
    subst index
    have eq : node = n1 := Option.some.inj present.symm
    subst node
    simp
  · have same : index = ix 2 := GeneralBorrowNodeUpdate.index_injective index (ix 2) h
    subst index
    have eq : node = n2 := Option.some.inj present.symm
    subst node
    simp
  · have same : index = ix 3 := GeneralBorrowNodeUpdate.index_injective index (ix 3) h
    subst index
    have eq : node = n3 := Option.some.inj present.symm
    subst node
    simp
  · have same : index = ix 4 := GeneralBorrowNodeUpdate.index_injective index (ix 4) h
    subst index
    have eq : node = n4 := Option.some.inj present.symm
    subst node
    simp

theorem index_small (index : UniIndex) (bound : index.toNat < 5) :
    index=ix 0 ∨ index=ix 1 ∨ index=ix 2 ∨ index=ix 3 ∨ index=ix 4 := by
  have cases : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 ∨ index.toNat=3 ∨ index.toNat=4 := by omega
  rcases cases with h | h | h | h | h
  · have eq : index=ix 0 := GeneralBorrowNodeUpdate.index_injective index (ix 0) h
    simp [eq]
  · have eq : index=ix 1 := GeneralBorrowNodeUpdate.index_injective index (ix 1) h
    simp [eq]
  · have eq : index=ix 2 := GeneralBorrowNodeUpdate.index_injective index (ix 2) h
    simp [eq]
  · have eq : index=ix 3 := GeneralBorrowNodeUpdate.index_injective index (ix 3) h
    simp [eq]
  · have eq : index=ix 4 := GeneralBorrowNodeUpdate.index_injective index (ix 4) h
    simp [eq]

theorem support_cases (index : UniIndex) (h : index.toNat < 4) :
    index=ix 0 ∨ index=ix 1 ∨ index=ix 2 ∨ index=ix 3 := by
  rcases index_small index (by omega) with rfl | rfl | rfl | rfl | rfl <;> simp_all [ix,UniIndex.toNat]

abbrev support (index : UniIndex) : Prop := index.toNat < 4

theorem no_removals (kind : AccessKind) (removed : List UniIndex)
    (legal : DuplicatePrefixResidualSupportAuthorization.Removal tree location {} (some (tag 5)) kind removed) :
    removed=[] := by
  cases removed with
  | nil => rfl
  | cons index tail =>
    obtain ⟨node,found,allowed⟩ := legal.allowed index (by simp)
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals cases kind <;> contradiction

theorem authorization (kind : AccessKind) :
    DuplicatePrefixResidualSupportAuthorization.Authorization tree location {} (ix 0) 0 (some (tag 5)) kind support := by
  refine ⟨by decide,?_,?_,?_,?_,?_,?_⟩
  · intro index inside
    rcases support_cases index inside with rfl | rfl | rfl | rfl
    all_goals exact ⟨_,rfl⟩
  · intro index node inside found child member
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [n0,n1,n2,n3,n4] at member
    all_goals rcases member with rfl | rfl <;> decide
  · intro index inside
    rcases support_cases index inside with rfl | rfl | rfl | rfl
    all_goals
      intro row member
      rw [entries_exact] at member
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro index node inside found
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · intro before after beforeLegal afterLegal subset index node inside found outside
    have b := no_removals kind before beforeLegal
    have a := no_removals kind after afterLegal
    subst before; subst after
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals cases kind
    all_goals first
      | (change 4 < 4 at inside; omega)
      | (with_unfolding_all exact ⟨rfl,Or.inl rfl⟩)
      | (with_unfolding_all exact ⟨rfl,Or.inr trivial⟩)
      | (with_unfolding_all refine ⟨rfl,Or.inr ⟨rfl,?_⟩⟩
         simp [DuplicatePrefixScalarAuthorization.Compatible,
           GeneralBorrowProtectedReadCompatible.Compatible,
           GeneralBorrowExposedConditionalWritePermissions.Compatible,
           location,n0,n3,UniValMap.get,ix,UniIndex.toNat,LocationState.possible,Permission.isUnique,ProtectedTags.contains,ProtectedTags.get])
  · intro primary
    exact ⟨ix 2,n2,by decide,rfl,by cases kind <;> unfold DuplicatePrefixCallbackAuthorization.Supports <;> decide⟩

def topology : TraversalTree := ⟨#[⟨none,[1,3]⟩,⟨some 0,[2]⟩,⟨some 1,[]⟩,⟨some 0,[]⟩,⟨none,[]⟩]⟩

theorem projection_topology (loc : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree loc protections).topology = topology := by
  unfold_general_projection
  unfold_general_topology
  with_unfolding_all rfl

def forest : GeneralBorrowForest.Forest topology where
  rank := id
  parents := by
    intro index valid parent edge
    have h : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 := by change index < 5 at valid; omega
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals simp [topology] at edge
    all_goals subst parent; decide
  childrenDistinct := by
    intro index valid
    have h : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 := by change index < 5 at valid; omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [topology]
  childParent := by
    intro parent valid child member
    have h : parent=0 ∨ parent=1 ∨ parent=2 ∨ parent=3 ∨ parent=4 := by change parent < 5 at valid; omega
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals simp [topology] at member
    all_goals first | (rcases member with rfl | rfl <;> exact ⟨by decide,rfl⟩) | (subst child; exact ⟨by decide,rfl⟩)
  parentChild := by
    intro child valid parent edge
    have h : child=0 ∨ child=1 ∨ child=2 ∨ child=3 ∨ child=4 := by change child < 5 at valid; omega
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals simp [topology] at edge
    all_goals subst parent; exact ⟨by decide,by decide⟩

def depth : GeneralBorrowExposure.ParentDepth tree.nodes where
  depth := UniIndex.toNat
  bounded := by
    intro index node found
    have h := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node found
    exact Nat.le_of_lt h
  parent := by
    intro index node found parent edge
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [n0,n1,n2,n3,n4] at edge
    all_goals subst parent; exact ⟨_,rfl,by decide⟩

theorem formed : GeneralBorrowStructuralHistorySifaState.Formed tree {} := by
  refine ⟨⟨⟨?_,⟨depth⟩,?_,?_,?_,?_,by decide⟩,?_⟩,?_⟩
  · intro loc protections
    rw [projection_topology]
    exact ⟨forest⟩
  · intro index node found child member
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [n0,n1,n2,n3,n4] at member
    all_goals first | (rcases member with rfl | rfl <;> exact ⟨_,rfl⟩) | (subst child; exact ⟨_,rfl⟩)
  · intro index node found parentless
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals first | decide | contradiction
  · intro root member
    change root ∈ [ix 0,ix 4] at member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨_,rfl,rfl⟩
  · refine ⟨⟨by simp [tree],by simp [tree],by decide⟩,rfl,by unfold GeneralBorrowGcAllocator.KeyUnique;decide,?_⟩
    intro index node found
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  · simp [tree,RangeMapNonempty.homogeneous,DedupRangeMap.WellFormed]
  · intro position valid
    have p : position=0 := by change position<1 at valid;omega
    subst position
    change GeneralBorrowLocationSifaConsistency.Profile tree location {}
    constructor
    · intro index node found
      rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals exact ⟨_,rfl,by decide⟩
    · intro index missing
      by_cases bound : index.toNat < 5
      · rcases index_small index bound with rfl | rfl | rfl | rfl | rfl <;> contradiction
      · unfold UniValMap.get
        rw [Array.getElem?_eq_none (by simpa [location] using bound)]

theorem coherent : LocationCoherent tree location {} := by
  intro query kind
  by_cases bound : query.toNat < 5
  · rcases index_small query bound with rfl | rfl | rfl | rfl | rfl
    all_goals cases kind <;> with_unfolding_all decide
  · have neq (n : Nat) (small : n < 5) : query ≠ ix n := by
      intro eq
      subst query
      have convert : (ix n).toNat = n := by simp [ix,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : n < 2^32)]
      rw [convert] at bound
      omega
    have absent : location.exposedCache.nodes.get query = none := by
      unfold UniValMap.get
      rw [Array.getElem?_eq_none (by change 4 ≤ query.toNat;omega)]
    have counts : cardinality tree.nodes (effective location {}) query kind = 0 := by
      unfold cardinality
      rw [entries_exact]
      have walk0 : GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) (ix 0) = [ix 0] := by with_unfolding_all rfl
      have walk1 : GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) (ix 1) = [ix 1,ix 0] := by with_unfolding_all rfl
      have walk2 : GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) (ix 2) = [ix 2,ix 1,ix 0] := by with_unfolding_all rfl
      have walk3 : GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) (ix 3) = [ix 3,ix 0] := by with_unfolding_all rfl
      have walk4 : GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) (ix 4) = [ix 4] := by with_unfolding_all rfl
      simp [contributes,walk0,walk1,walk2,walk3,walk4,List.contains_iff_mem,
        neq 0 (by decide),neq 1 (by decide),neq 2 (by decide),neq 3 (by decide),neq 4 (by decide)]

    cases kind <;> simp [counter,absent,counts]

def global : GlobalState := {nextPointerTag := tag 11}

theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global := by
  refine ⟨formed,?_,?_,?_⟩
  · intro position valid
    have p : position=0 := by change position<1 at valid;omega
    subst position
    exact coherent
  · intro position valid index node found
    have p : position=0 := by change position<1 at valid;omega
    subst position
    change ((location.perms.get index).getD node.defaultLocationState).possible = true
    rcases lookup_cases index node found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · constructor
    · intro row member
      change row ∈ #[(n0.tag,ix 0),(n1.tag,ix 1),(n2.tag,ix 2),(n3.tag,ix 3),(n4.tag,ix 4)] at member
      simp only [Array.mem_def,List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp [global,ProtectedTags.entries]

theorem callback_failure (kind : AccessKind) :
    (tree.performWildcardAccessAt location (ix 0) (some (tag 5)) kind {} false).status =
    .NoValidExposedReferences (ix 0) none := by
  let after : LocationTree := {location with perms := location.perms.insert (ix 3) ⟨.Cell,true,IdempotentForeignAccess.fromForeign kind⟩}
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have s1 : scan () (location,false,.Completed,#[(ix 0,false)],0) =
      .yield (location,false,.Completed,#[(ix 0,true),(ix 1,false),(ix 3,false)],1) := by
    cases kind <;> with_unfolding_all rfl
  have s2 : scan () (location,false,.Completed,#[(ix 0,true),(ix 1,false),(ix 3,false)],1) =
      .yield (location,false,.Completed,#[(ix 0,true),(ix 1,false),(ix 3,true)],2) := by
    cases kind <;> with_unfolding_all rfl
  have s3 : scan () (location,false,.Completed,#[(ix 0,true),(ix 1,false),(ix 3,true)],2) =
      .yield (after,false,.Completed,#[(ix 0,true),(ix 1,false)],3) := by
    cases kind <;> with_unfolding_all rfl
  have s4 : scan () (after,false,.Completed,#[(ix 0,true),(ix 1,false)],3) =
      .yield (after,false,.Completed,#[(ix 0,true)],4) := by
    cases kind <;> with_unfolding_all rfl
  have s5 : scan () (after,false,.Completed,#[(ix 0,true)],4) =
      .yield (after,false,.Completed,#[],5) := by
    cases kind <;> with_unfolding_all rfl
  have s6 : scan () (after,false,.Completed,#[],5) =
      .done (after,false,.Completed,#[],5) := by
    cases kind <;> with_unfolding_all rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s3,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s4,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s5,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s6,bind,pure]
  rfl

/-- The structural/runtime packet does not encode chronological tag causality. -/
theorem nonchronological_edge : tree.nodes.get (ix 2) = some n2 ∧
    n2.parent = some (ix 1) ∧ tree.nodes.get (ix 1) = some n1 ∧ n1.tag.value > n2.tag.value := by
  exact ⟨rfl,rfl,rfl,by decide⟩

/-- Local authorization insufficiency only. No call contract or reachability claim. -/
theorem local_countermodel : DuplicatePrefixBorrowContract.RuntimeFacts tree global ∧
    ∀ kind : AccessKind,
      DuplicatePrefixResidualSupportAuthorization.Authorization tree location {} (ix 0) 0 (some (tag 5)) kind support ∧
      (tree.performWildcardAccessAt location (ix 0) (some (tag 5)) kind {} false).status = .NoValidExposedReferences (ix 0) none :=
  ⟨runtime,fun kind => ⟨authorization kind,callback_failure kind⟩⟩

end DuplicatePrefix.PrimaryWitnessCountermodel
