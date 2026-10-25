import Lean.Elab.Tactic
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Raw

/-!
Executable structural `DecidableEq` instances for standard hash-map storage.

`HashMap` equality here compares its representation exactly: cached size, bucket array
length and order, and each bucket's association-list order and key/value entries. The
`DHashMap` well-formedness proof field is compared using proof irrelevance. These instances
do not identify maps extensionally when their bucket layouts differ.
-/


namespace Miri.Verification.ExactMap212

private def constAssocListDecEq {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] :
    (left right : Std.DHashMap.Internal.AssocList α (fun _ => β)) →
      Decidable (left = right)
  | .nil, .nil => isTrue rfl
  | .nil, .cons _ _ _ => isFalse (by intro h; cases h)
  | .cons _ _ _, .nil => isFalse (by intro h; cases h)
  | .cons key value tail, .cons key' value' tail' =>
      match decEq key key' with
      | .isFalse hkey =>
          isFalse (by
            intro h
            exact hkey ((Std.DHashMap.Internal.AssocList.cons.injEq
              key value tail key' value' tail').mp h).1)
      | .isTrue hkey =>
          match decEq value value' with
          | .isFalse hvalue =>
              isFalse (by
                intro h
                exact hvalue (eq_of_heq ((Std.DHashMap.Internal.AssocList.cons.injEq
                  key value tail key' value' tail').mp h).2.1))
          | .isTrue hvalue =>
              match constAssocListDecEq tail tail' with
              | .isFalse htail =>
                  isFalse (by
                    intro h
                    exact htail ((Std.DHashMap.Internal.AssocList.cons.injEq
                      key value tail key' value' tail').mp h).2.2)
              | .isTrue htail =>
                  isTrue (by
                    have h1 : Std.DHashMap.Internal.AssocList.cons key value tail =
                        Std.DHashMap.Internal.AssocList.cons key' value tail :=
                      congrArg (fun k => Std.DHashMap.Internal.AssocList.cons k value tail) hkey
                    have h2 : Std.DHashMap.Internal.AssocList.cons key' value tail =
                        Std.DHashMap.Internal.AssocList.cons key' value' tail :=
                      congrArg (fun v => Std.DHashMap.Internal.AssocList.cons key' v tail) hvalue
                    have h3 : Std.DHashMap.Internal.AssocList.cons key' value' tail =
                        Std.DHashMap.Internal.AssocList.cons key' value' tail' :=
                      congrArg (Std.DHashMap.Internal.AssocList.cons key' value') htail
                    exact h1.trans (h2.trans h3))

instance instDecidableEqConstAssocList {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] :
    DecidableEq (Std.DHashMap.Internal.AssocList α (fun _ => β)) := constAssocListDecEq

private def rawDecEq {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] :
    (left right : Std.DHashMap.Raw α (fun _ => β)) → Decidable (left = right)
  | ⟨size, buckets⟩, ⟨size', buckets'⟩ =>
      match decEq size size' with
      | .isFalse hsize => isFalse (fun h => hsize (congrArg Std.DHashMap.Raw.size h))
      | .isTrue hsize =>
          match decEq buckets buckets' with
          | .isFalse hbuckets => isFalse (fun h => hbuckets (congrArg Std.DHashMap.Raw.buckets h))
          | .isTrue hbuckets =>
              isTrue (by
                have h1 : Std.DHashMap.Raw.mk size buckets = Std.DHashMap.Raw.mk size' buckets :=
                  congrArg (fun n => Std.DHashMap.Raw.mk n buckets) hsize
                have h2 : Std.DHashMap.Raw.mk size' buckets = Std.DHashMap.Raw.mk size' buckets' :=
                  congrArg (Std.DHashMap.Raw.mk size') hbuckets
                exact h1.trans h2)

private def dHashMapDecEq {α : Type u} {β : Type v}
    [BEq α] [Hashable α] [DecidableEq α] [DecidableEq β] :
    (left right : Std.DHashMap α (fun _ => β)) → Decidable (left = right)
  | ⟨inner, wf⟩, ⟨inner', wf'⟩ =>
      match rawDecEq inner inner' with
      | .isFalse hinner => isFalse (fun h => hinner (congrArg Std.DHashMap.inner h))
      | .isTrue hinner =>
          isTrue (by
            cases hinner
            apply congrArg (fun proof : inner.WF => (⟨inner, proof⟩ : Std.DHashMap α (fun _ => β)))
            exact Subsingleton.elim wf wf')

private def hashMapRawDecEq {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] :
    (left right : Std.HashMap.Raw α β) → Decidable (left = right)
  | ⟨inner⟩, ⟨inner'⟩ =>
      match rawDecEq inner inner' with
      | .isFalse hinner => isFalse (fun h => hinner (congrArg Std.HashMap.Raw.inner h))
      | .isTrue hinner => isTrue (congrArg Std.HashMap.Raw.mk hinner)

private def hashMapDecEq {α : Type u} {β : Type v}
    [BEq α] [Hashable α] [DecidableEq α] [DecidableEq β] :
    (left right : Std.HashMap α β) → Decidable (left = right)
  | ⟨inner⟩, ⟨inner'⟩ =>
      match dHashMapDecEq inner inner' with
      | .isFalse hinner => isFalse (fun h => hinner (congrArg Std.HashMap.inner h))
      | .isTrue hinner => isTrue (congrArg Std.HashMap.mk hinner)

instance instDecidableEqConstDHashMapRaw {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] :
    DecidableEq (Std.DHashMap.Raw α (fun _ => β)) := rawDecEq

instance instDecidableEqConstDHashMap {α : Type u} {β : Type v}
    [BEq α] [Hashable α] [DecidableEq α] [DecidableEq β] :
    DecidableEq (Std.DHashMap α (fun _ => β)) := dHashMapDecEq

instance instDecidableEqHashMapRaw {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] :
    DecidableEq (Std.HashMap.Raw α β) := hashMapRawDecEq

instance instDecidableEqHashMap {α : Type u} {β : Type v}
    [BEq α] [Hashable α] [DecidableEq α] [DecidableEq β] :
    DecidableEq (Std.HashMap α β) := hashMapDecEq

end Miri.Verification.ExactMap212
