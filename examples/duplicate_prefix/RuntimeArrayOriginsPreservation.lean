import duplicate_prefix.DuplicatePrefixTypeCacheOrigins

namespace DuplicatePrefix.RuntimeArrayOriginsPreservation
open Miri Miri.Input Miri.ABI
open RuntimeArrayTypes DuplicatePrefixTypeCacheOrigins
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Compiler constructor aliases name actual ARRAY catalog nodes. This is
identity evidence only; it imposes no layout, key-uniqueness or allocation bound. -/
def AliasOrigins (world : World) : Prop :=
  ∀ alias ∈ world.aliases, ∃ node,
    world.metadata.source.types.find? (·.id == alias.2) = some node ∧ node.shapeKind = .array

private theorem push_preserves (world : World) (entry : Entry) (next : TypeId)
    (origins : Origins world) (aliases : AliasOrigins world)
    (added : EntryOrigin world entry) :
    Origins {world with entries := world.entries.push entry, nextId := next} ∧
      AliasOrigins {world with entries := world.entries.push entry, nextId := next} := by
  constructor
  · intro row member
    rcases Array.mem_push.mp member with old | new
    · exact origins row old
    · subst row; exact added
  · exact aliases

/-- Successful interning preserves the partial identity invariant. A hit leaves
all data unchanged; an alias miss uses catalog identity; a fresh miss uses the
constructor's explicit compiler-ID collision check. No success is assumed for
an error outcome, and no layout-correctness or history claim is made. -/
theorem intern_preserves (world : World) (element : Element) (count : UInt64)
    (value : TyAndLayout TypeId) (after : World)
    (origins : Origins world) (aliases : AliasOrigins world)
    (success : intern world element count = .ok (value, after)) :
    Origins after ∧ AliasOrigins after := by
  unfold intern at success
  simp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
    throw] at success
  iterate 12
    all_goals try first
      | (have eq := Except.ok.inj success
         have eqAfter := congrArg Prod.snd eq
         dsimp only at eqAfter
         subst after
         first
         | exact ⟨origins, aliases⟩
         | apply push_preserves world _ _ origins aliases
           first
           | (change _ ∧ ∃ _, _ ∧ _
              refine ⟨rfl, ?_⟩
              apply aliases (_, _)
              apply Array.mem_of_find?_eq_some
              assumption)
           | (change world.metadata.source.types.any _ = false
              simp_all only [Bool.not_eq_true', Bool.and_eq_true]))
      | contradiction
      | split at success
    all_goals try simp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure,
      throw] at success


/-- The public element-ID constructor has the same identity preservation. -/
theorem internElement_preserves (world : World) (element : TypeId) (count : UInt64)
    (value : TyAndLayout TypeId) (after : World)
    (origins : Origins world) (aliases : AliasOrigins world)
    (success : internElement world element count = .ok (value, after)) :
    Origins after ∧ AliasOrigins after := by
  unfold internElement at success
  exact intern_preserves world _ count value after origins aliases success

end DuplicatePrefix.RuntimeArrayOriginsPreservation

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RuntimeArrayOriginsPreservation.intern_preserves,
      ``DuplicatePrefix.RuntimeArrayOriginsPreservation.internElement_preserves] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "runtime array origin preservation depends on unapproved axiom {dependency}"
