import duplicate_prefix.DuplicatePrefixBorrowAuthorization

namespace DuplicatePrefix.S05ResidualCutoffCallDomain
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false

/-- A nonempty cutoff in the actual row API necessarily comes from a concrete
source and the tag of its selected physical root. In particular the remaining
Write/some-cutoff coverage gap is not a wildcard-input callback obligation.
This theorem extracts existing call-time data; it does not characterize valid
mutable references or prove that ordinary ownership supplies the callbacks. -/
theorem concrete_root_of_cutoff
    {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {source selectedRoot : Option UniIndex} {maximum : BorTag}
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot (some maximum)) :
    ∃ anchor root node,
      source = some anchor ∧ selectedRoot = some root ∧
      tree.nodeAt root = some node ∧ node.tag = maximum := by
  cases source with
  | none =>
    have impossible := row.wildcard_cutoff
    cases impossible
  | some anchor =>
    cases selectedRoot with
    | none =>
      have impossible := row.cutoff
      cases impossible
    | some root =>
      obtain ⟨node,present⟩ := row.rootPresent root rfl
      have same : maximum = node.tag := by
        have cutoff := row.cutoff
        simp only [Option.bind_some,present,Option.map_some] at cutoff
        exact Option.some.inj cutoff
      exact ⟨anchor,root,node,rfl,rfl,present,same.symm⟩

end DuplicatePrefix.S05ResidualCutoffCallDomain
