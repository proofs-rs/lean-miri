import duplicate_prefix.S05RetainedConeNumericAdapter

namespace DuplicatePrefix.S05VirtualContributorStrictEnlargement
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open S05CutoffOwnershipGeometry S05LiveSubtreeCacheSoundness
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def ix (n : Nat) : UniIndex := ⟨UInt32.ofNat n⟩
def tag (n : UInt64) (nonzero : n ≠ 0 := by decide) : BorTag := ⟨n,nonzero⟩
def primary : TreeNode := ⟨tag 1,none,#[],.Cell,.None,true,none⟩
def ancestor : TreeNode := ⟨tag 2,none,#[ix 2],.ReservedFrz false,.None,false,none⟩
def descendant : TreeNode := ⟨tag 3,some (ix 1),#[],.Cell,.None,true,none⟩
def protections : ProtectedTags := ({} : ProtectedTags).insert (tag 2) .StrongProtector
def location : LocationTree := {
  perms := ⟨#[some ⟨.Cell,true,.None⟩,some ⟨.ReservedFrz true,true,.None⟩,some ⟨.Cell,true,.None⟩]⟩
  exposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩]⟩⟩ }
def tree : BorrowTree := ⟨⟨#[(tag 1,ix 0),(tag 2,ix 1),(tag 3,ix 2)],#[]⟩,
  ⟨#[some primary,some ancestor,some descendant]⟩,RangeMapNonempty.homogeneous 1 location,#[ix 0,ix 1]⟩

private theorem small (index : UniIndex) (bound : index.toNat < 3) :
    index=ix 0 ∨ index=ix 1 ∨ index=ix 2 := by
  have cases : index.toNat=0 ∨ index.toNat=1 ∨ index.toNat=2 := by omega
  rcases cases with h | h | h
  · exact Or.inl (GeneralBorrowNodeUpdate.index_injective index (ix 0) h)
  · exact Or.inr (Or.inl (GeneralBorrowNodeUpdate.index_injective index (ix 1) h))
  · exact Or.inr (Or.inr (GeneralBorrowNodeUpdate.index_injective index (ix 2) h))

theorem lookup_cases (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    (index=ix 0 ∧ node=primary) ∨ (index=ix 1 ∧ node=ancestor) ∨ (index=ix 2 ∧ node=descendant) := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  change index.toNat < 3 at bound
  rcases small index bound with rfl | rfl | rfl
  · have same : node=primary := Option.some.inj present.symm
    exact Or.inl ⟨rfl,same⟩
  · have same : node=ancestor := Option.some.inj present.symm
    exact Or.inr (Or.inl ⟨rfl,same⟩)
  · have same : node=descendant := Option.some.inj present.symm
    exact Or.inr (Or.inr ⟨rfl,same⟩)

theorem entries : tree.nodes.entries.toList = [(ix 0,primary),(ix 1,ancestor),(ix 2,descendant)] := by
  with_unfolding_all rfl

/-- All scalar SIFA bounds and clean vacancies hold. The protected reservation
is conflicted, but its cache is None; no history/ordinary-validity claim follows. -/
theorem profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections := by
  constructor
  · intro index node present
    rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨.Write,rfl,by decide⟩
    · exact ⟨.Read,rfl,by decide⟩
    · exact ⟨.Write,rfl,by decide⟩
  · intro index absent
    have outside : 3 ≤ index.toNat := by
      by_cases h : index.toNat < 3
      · rcases small index h with rfl | rfl | rfl <;> cases absent
      · omega
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by change 3 ≤ index.toNat;exact outside)]

def depth : GeneralBorrowExposure.ParentDepth tree.nodes where
  depth index := if index=ix 2 then 1 else 0
  bounded := by
    intro index node present
    rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  parent := by
    intro index node present parent edge
    rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · cases edge
    · cases edge
    · have same : parent=ix 1 := (Option.some.inj edge).symm
      subst parent
      exact ⟨ancestor,rfl,by decide⟩

theorem reciprocal : Reciprocal tree := by
  intro index node present parent edge
  rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases edge
  · cases edge
  · have same : parent=ix 1 := (Option.some.inj edge).symm
    subst parent
    exact ⟨ancestor,rfl,by decide⟩

theorem order : ParentTagOrder tree := by
  intro index node present parent parentNode edge parentPresent
  rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases edge
  · cases edge
  · have same : parent=ix 1 := (Option.some.inj edge).symm
    subst parent
    have same : parentNode=ancestor := Option.some.inj parentPresent.symm
    subst parentNode
    decide

/-- Numeric live-cone bounds hold even without using the live-cone hypothesis:
every queried ancestor contributes only the None cache strength. -/
theorem sound (support : UniIndex → Prop) : Soundness tree location protections support := by
  intro query node inside present witness witnessNode found walked live
  rcases lookup_cases query node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rcases lookup_cases witness witnessNode found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals first | exact ⟨.Write,rfl,by decide⟩ | exact ⟨.Read,rfl,by decide⟩

theorem coherent : LocationCoherent tree location protections := by
  intro query kind
  by_cases bound : query.toNat < 3
  · rcases small query bound with rfl | rfl | rfl
    all_goals cases kind <;> with_unfolding_all decide
  · have neq (n : Nat) (small : n < 3) : query ≠ ix n := by
      intro same
      subst query
      have converted : (ix n).toNat = n := by
        simp [ix,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : n < 2^32)]
      rw [converted] at bound
      omega
    have absent : location.exposedCache.nodes.get query = none := by
      unfold UniValMap.get
      rw [Array.getElem?_eq_none (by change 3 ≤ query.toNat;omega)]
    have counts : cardinality tree.nodes (effective location protections) query kind = 0 := by
      unfold cardinality
      rw [entries]
      have walk0 : walk tree.nodes (tree.nodes.size+1) (ix 0) = [ix 0] := by with_unfolding_all rfl
      have walk1 : walk tree.nodes (tree.nodes.size+1) (ix 1) = [ix 1] := by with_unfolding_all rfl
      have walk2 : walk tree.nodes (tree.nodes.size+1) (ix 2) = [ix 2,ix 1] := by with_unfolding_all rfl
      simp [contributes,walk0,walk1,walk2,List.contains_iff_mem,neq 0 (by decide),neq 1 (by decide),neq 2 (by decide)]
    simp only [counter,absent,Option.getD_none,counts]
    cases kind <;> rfl

def primaryArea : GeneralBorrowWildcardControlStack.Support tree (ix 0) where
  contains query := query=ix 0
  rooted := rfl
  present := by intro query same;subst query;exact ⟨primary,rfl⟩
  children := by
    intro query node same present child member
    subst query
    have same : node=primary := Option.some.inj present.symm
    subst node
    cases member

def virtualArea : GeneralBorrowWildcardControlStack.Support tree (ix 1) where
  contains query := query=ix 1 ∨ query=ix 2
  rooted := Or.inl rfl
  present := by
    intro query included
    rcases included with rfl | rfl
    · exact ⟨ancestor,rfl⟩
    · exact ⟨descendant,rfl⟩
  children := by
    intro query node included present child member
    rcases included with rfl | rfl
    · have same : node=ancestor := Option.some.inj present.symm
      subst node
      have same : child=ix 2 := by simpa [ancestor] using member
      exact Or.inr same
    · have same : node=descendant := Option.some.inj present.symm
      subst node
      cases member

theorem primary_covers (query : UniIndex) (inside : primaryArea.contains query) : Covers tree.nodes (ix 0) query := by
  change query=ix 0 at inside
  subst query
  intro row member walked
  exact walked

theorem virtual_covers (query : UniIndex) (inside : virtualArea.contains query) : Covers tree.nodes (ix 1) query := by
  have walk0 : walk tree.nodes (tree.nodes.size+1) (ix 0) = [ix 0] := by with_unfolding_all rfl
  have walk1 : walk tree.nodes (tree.nodes.size+1) (ix 1) = [ix 1] := by with_unfolding_all rfl
  have walk2 : walk tree.nodes (tree.nodes.size+1) (ix 2) = [ix 2,ix 1] := by with_unfolding_all rfl
  intro row member walked
  rw [entries] at member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases inside with rfl | rfl
  all_goals rcases member with rfl | rfl | rfl
  all_goals simp_all [walk0,walk1,walk2,ix]

theorem tag_binding (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    tree.tagMapping.get node.tag = some index := by
  rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl

theorem roots_distinct : tree.roots.toList.Nodup := by decide

/-- This is the actual second physical root, so its virtual alternative is
not obtained by passing a fictitious position for the primary root. -/
theorem virtual_position : tree.roots[1]? = some (ix 1) := rfl

def primaryRights : S05RetainedConeOwnership.GeneralizedOwnership tree location protections (ix 0) 0 none where
  area := primaryArea
  covers := primary_covers
  possible := by
    intro query node inside present
    change query=ix 0 at inside
    subst query
    have same : node=primary := Option.some.inj present.symm
    subst node
    decide
  foreign := by
    intro query node inside present guard
    change query=ix 0 at inside
    subst query
    have same : node=primary := Option.some.inj present.symm
    subst node
    exact ⟨rfl,by decide⟩
  primaryLocal := by
    intro zero query node inside present witness witnessNode found exposed walked kind supported
    change query=ix 0 at inside
    subst query
    have same : node=primary := Option.some.inj present.symm
    subst node
    cases kind <;> exact ⟨rfl,by decide⟩
  virtualLive := by intro notzero;exact False.elim (notzero rfl)
  cutoff := by
    intro zero
    exact ⟨ix 0,primary,rfl,rfl,by unfold DuplicatePrefixCallbackAuthorization.Supports;decide⟩

def virtualRights : S05RetainedConeOwnership.GeneralizedOwnership tree location protections (ix 1) 1 none where
  area := virtualArea
  covers := virtual_covers
  possible := by
    intro query node inside present
    rcases inside with rfl | rfl
    · have same : node=ancestor := Option.some.inj present.symm
      subst node
      decide
    · have same : node=descendant := Option.some.inj present.symm
      subst node
      decide
  foreign := by
    intro query node inside present guard
    have retained : S05RetainedConeOwnership.RetainedBelow tree location protections none query := by
      refine ⟨ix 2,descendant,rfl,by unfold DuplicatePrefixCallbackAuthorization.Supports;decide,?_⟩
      rcases inside with rfl | rfl
      · exact .step (.refl (ix 1) ancestor rfl) descendant rfl rfl
      · exact .refl (ix 2) descendant rfl
    rcases guard with above | missing
    · cases above
    · exact False.elim (missing retained)
  primaryLocal := by intro zero;cases zero
  virtualLive := by
    intro nonzero query node inside present witness witnessNode found exposed walked kind supported
    rcases inside with rfl | rfl
    · have same : node=ancestor := Option.some.inj present.symm
      subst node
      cases kind <;> exact ⟨rfl,by decide⟩
    · have same : node=descendant := Option.some.inj present.symm
      subst node
      cases kind <;> exact ⟨rfl,by decide⟩
  cutoff := by intro zero;cases zero

/-- Old formation fails at the protected conflicted ancestor of the exposed
Cell contributor. This is a strict input-domain witness, not a call counterexample. -/
theorem not_old : ¬ Nonempty (S05RetainedConeOwnership.Ownership tree location protections (ix 1) 1 none) := by
  intro old
  obtain ⟨rights⟩ := old
  have localWrite := rights.localRights (ix 1) ancestor rights.area.rooted rfl (ix 2) descendant rfl rfl
    (by with_unfolding_all decide) .Write (by decide)
  have impossible := localWrite.2.2.2 rfl
  exact impossible rfl

/-- The generalized raw formation derives the SAME existing borrow Row. All
roots, permissions, exposure counts, topology and numeric facts above are
finite initial data; no actual operation outcome or ordinary validity is assumed. -/
theorem row : DuplicatePrefixBorrowAuthorization.Row tree location protections none none none := by
  apply S05RetainedConeNumericAdapter.generalized_row tree location protections none none none
    depth reciprocal order coherent (by decide) (by intro _;rfl)
    (by intro anchor absent;cases absent) (by intro root absent;cases absent) rfl
    (by intro anchor absent;cases absent)
  intro position valid other
  have cases : position=0 ∨ position=1 := by change position < 2 at valid;omega
  rcases cases with rfl | rfl
  · exact ⟨primaryRights,sound _⟩
  · exact ⟨virtualRights,sound _⟩

/-- The same existing Positive capability covers the fixture's actual one-byte
partition, with its Row derived above rather than supplied as an assumption. -/
theorem positive : DuplicatePrefixBorrowAuthorization.Positive tree protections none none none 0 1 := by
  refine ⟨by decide,by decide,?_,?_,?_⟩
  · intro anchor absent
    cases absent
  · intro _
    decide
  · intro position valid nonempty beforeUpper afterLower
    have zero : position=0 := by change position < 1 at valid;omega
    subst position
    exact ⟨row⟩

/-- Concrete strict enlargement of formation while keeping the authorization
conclusion unchanged. Neither an ordinary-input domain nor a history theorem. -/
theorem strict_enlargement :
    Nonempty (S05RetainedConeOwnership.GeneralizedOwnership tree location protections (ix 1) 1 none) ∧
      ¬ Nonempty (S05RetainedConeOwnership.Ownership tree location protections (ix 1) 1 none) ∧
      DuplicatePrefixBorrowAuthorization.Row tree location protections none none none :=
  ⟨⟨virtualRights⟩,not_old,row⟩

end DuplicatePrefix.S05VirtualContributorStrictEnlargement
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05VirtualContributorStrictEnlargement." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved virtual contributor enlargement dependency {dependency}"
