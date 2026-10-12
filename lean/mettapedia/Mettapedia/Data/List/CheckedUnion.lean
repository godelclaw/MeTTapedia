import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Basic

/-!
# Ordered checked union of finite declarations

Insertion retains the first occurrence of an equal declaration and checks
compatibility before adding a different declaration. A reflexive symmetric
compatibility relation supplies the extensional admission contract; successful
union retains the existing order and never invents an entry. The relation is
explicit, allowing distinct module-origin contracts to share this operation.
-/

set_option autoImplicit false

namespace List

universe u
variable {α : Type u} [DecidableEq α]

def insertCompatible? (compatible : α → α → Bool) (entry : α) : List α → Option (List α)
  | [] => some [entry]
  | first :: rest =>
      if entry = first then some (first :: rest)
      else if compatible first entry then
        (insertCompatible? compatible entry rest).map (first :: ·)
      else none

def unionCompatible? (compatible : α → α → Bool) : List α → List α → Option (List α)
  | kept, [] => some kept
  | kept, entry :: rest => do
      let next ← insertCompatible? compatible entry kept
      unionCompatible? compatible next rest

theorem unionCompatible?_append (compatible : α → α → Bool)
    (kept first second : List α) :
    unionCompatible? compatible kept (first ++ second) =
      (unionCompatible? compatible kept first).bind
        (fun next => unionCompatible? compatible next second) := by
  induction first generalizing kept with
  | nil => rfl
  | cons entry rest ih =>
      simp only [cons_append, unionCompatible?]
      cases next : insertCompatible? compatible entry kept with
      | none => rfl
      | some entries => exact ih entries

def AllCompatible (compatible : α → α → Bool) (entries : List α) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries, compatible first second = true

omit [DecidableEq α] in
theorem AllCompatible.mono {compatible : α → α → Bool} {entries smaller : List α}
    (accepted : AllCompatible compatible entries) (subset : smaller ⊆ entries) :
    AllCompatible compatible smaller :=
  fun first memberFirst second memberSecond =>
    accepted first (subset memberFirst) second (subset memberSecond)

omit [DecidableEq α] in
@[simp] theorem allCompatible_nil (compatible : α → α → Bool) :
    AllCompatible compatible [] := by simp [AllCompatible]

theorem insertCompatible?_toFinset (compatible : α → α → Bool) (entry : α)
    (kept result : List α) (inserted : insertCompatible? compatible entry kept = some result) :
    result.toFinset = insert entry kept.toFinset := by
  induction kept generalizing result with
  | nil =>
      simp only [insertCompatible?, Option.some.injEq] at inserted
      subst result
      simp
  | cons first rest ih =>
      by_cases same : entry = first
      · simp only [insertCompatible?, if_pos same, Option.some.injEq] at inserted
        subst result
        simp [same]
      · cases allowed : compatible first entry with
        | false => simp [insertCompatible?, same, allowed] at inserted
        | true =>
            cases next : insertCompatible? compatible entry rest with
            | none => simp [insertCompatible?, same, allowed, next] at inserted
            | some tail =>
                simp only [insertCompatible?, if_neg same, allowed, ↓reduceIte,
                  next, Option.map_some, Option.some.injEq] at inserted
                subst result
                simp only [List.toFinset_cons, ih tail next, Finset.insert_comm]

theorem insertCompatible?_kept_sublist (compatible : α → α → Bool) (entry : α)
    (kept result : List α) (inserted : insertCompatible? compatible entry kept = some result) :
    kept.Sublist result := by
  induction kept generalizing result with
  | nil => exact nil_sublist _
  | cons first rest ih =>
      by_cases same : entry = first
      · simp only [insertCompatible?, if_pos same, Option.some.injEq] at inserted
        subst result
        exact Sublist.refl _
      · cases allowed : compatible first entry with
        | false => simp [insertCompatible?, same, allowed] at inserted
        | true =>
            cases next : insertCompatible? compatible entry rest with
            | none => simp [insertCompatible?, same, allowed, next] at inserted
            | some tail =>
                simp only [insertCompatible?, if_neg same, allowed, ↓reduceIte,
                  next, Option.map_some, Option.some.injEq] at inserted
                subst result
                exact (ih tail next).cons_cons first

/-- An existing declaration keeps its first position. A new declaration is
appended after the retained declarations. -/
theorem insertCompatible?_order (compatible : α → α → Bool) (entry : α)
    (kept result : List α) (inserted : insertCompatible? compatible entry kept = some result) :
    result = if entry ∈ kept then kept else kept ++ [entry] := by
  induction kept generalizing result with
  | nil =>
      simp only [insertCompatible?, Option.some.injEq] at inserted
      subst result
      simp
  | cons first rest ih =>
      by_cases same : entry = first
      · simp only [insertCompatible?, if_pos same, Option.some.injEq] at inserted
        subst result
        simp [same]
      · cases allowed : compatible first entry with
        | false => simp [insertCompatible?, same, allowed] at inserted
        | true =>
            cases next : insertCompatible? compatible entry rest with
            | none => simp [insertCompatible?, same, allowed, next] at inserted
            | some tail =>
                simp only [insertCompatible?, if_neg same, allowed, ↓reduceIte,
                  next, Option.map_some, Option.some.injEq] at inserted
                subst result
                rw [ih tail next]
                by_cases seen : entry ∈ rest <;> simp [same, seen]

theorem insertCompatible?_isSome_iff (compatible : α → α → Bool)
    (entry : α) (kept : List α) (accepted : AllCompatible compatible kept) :
    (insertCompatible? compatible entry kept).isSome = true ↔
      ∀ previous ∈ kept, compatible previous entry = true := by
  induction kept with
  | nil => simp [insertCompatible?]
  | cons first rest ih =>
      have tailAccepted : AllCompatible compatible rest := accepted.mono (by simp)
      by_cases same : entry = first
      · subst entry
        constructor
        · intro _ previous member
          exact accepted previous member first (by simp)
        · intro _
          simp [insertCompatible?]
      · cases allowed : compatible first entry with
        | false => simp [insertCompatible?, same, allowed]
        | true =>
            simpa [insertCompatible?, same, allowed] using ih tailAccepted

theorem insertCompatible?_allCompatible (compatible : α → α → Bool)
    (reflexive : ∀ entry, compatible entry entry = true)
    (symmetric : ∀ first second, compatible first second = compatible second first)
    (entry : α) (kept result : List α) (accepted : AllCompatible compatible kept)
    (inserted : insertCompatible? compatible entry kept = some result) :
    AllCompatible compatible result := by
  have admitted : ∀ previous ∈ kept, compatible previous entry = true :=
    (insertCompatible?_isSome_iff compatible entry kept accepted).mp (by simp [inserted])
  have entries := insertCompatible?_toFinset compatible entry kept result inserted
  intro first firstMember second secondMember
  have firstMember' : first = entry ∨ first ∈ kept := by
    have member : first ∈ result.toFinset := by simpa using firstMember
    simpa only [entries, Finset.mem_insert, List.mem_toFinset] using member
  have secondMember' : second = entry ∨ second ∈ kept := by
    have member : second ∈ result.toFinset := by simpa using secondMember
    simpa only [entries, Finset.mem_insert, List.mem_toFinset] using member
  rcases firstMember' with rfl | firstMember' <;> rcases secondMember' with rfl | secondMember'
  · exact reflexive _
  · rw [symmetric]; exact admitted second secondMember'
  · exact admitted first firstMember'
  · exact accepted first firstMember' second secondMember'

theorem unionCompatible?_toFinset (compatible : α → α → Bool) (kept incoming result : List α)
    (joined : unionCompatible? compatible kept incoming = some result) :
    result.toFinset = kept.toFinset ∪ incoming.toFinset := by
  induction incoming generalizing kept with
  | nil =>
      simp only [unionCompatible?, Option.some.injEq] at joined
      subst result
      simp
  | cons entry rest ih =>
      cases next : insertCompatible? compatible entry kept with
      | none => simp [unionCompatible?, next] at joined
      | some entries =>
          simp only [unionCompatible?, next] at joined
          rw [ih entries joined, insertCompatible?_toFinset compatible entry kept entries next]
          simp only [List.toFinset_cons, Finset.insert_union, Finset.union_insert]

theorem unionCompatible?_allCompatible (compatible : α → α → Bool)
    (reflexive : ∀ entry, compatible entry entry = true)
    (symmetric : ∀ first second, compatible first second = compatible second first)
    (kept incoming result : List α) (accepted : AllCompatible compatible kept)
    (joined : unionCompatible? compatible kept incoming = some result) :
    AllCompatible compatible result := by
  induction incoming generalizing kept with
  | nil =>
      simp only [unionCompatible?, Option.some.injEq] at joined
      subst result
      exact accepted
  | cons entry rest ih =>
      cases next : insertCompatible? compatible entry kept with
      | none => simp [unionCompatible?, next] at joined
      | some entries =>
          simp only [unionCompatible?, next] at joined
          exact ih entries (insertCompatible?_allCompatible compatible reflexive symmetric entry kept entries accepted next) joined

theorem insertCompatible?_mem_iff (compatible : α → α → Bool) (entry : α)
    (kept result : List α) (inserted : insertCompatible? compatible entry kept = some result)
    (item : α) : item ∈ result ↔ item = entry ∨ item ∈ kept := by
  rw [← mem_toFinset, insertCompatible?_toFinset compatible entry kept result inserted,
    Finset.mem_insert, mem_toFinset]

theorem unionCompatible?_mem_iff (compatible : α → α → Bool) (kept incoming result : List α)
    (joined : unionCompatible? compatible kept incoming = some result) (item : α) :
    item ∈ result ↔ item ∈ kept ∨ item ∈ incoming := by
  rw [← mem_toFinset, unionCompatible?_toFinset compatible kept incoming result joined,
    Finset.mem_union, mem_toFinset, mem_toFinset]

theorem insertCompatible?_nodup (compatible : α → α → Bool) (entry : α)
    (kept result : List α) (distinct : kept.Nodup)
    (inserted : insertCompatible? compatible entry kept = some result) : result.Nodup := by
  induction kept generalizing result with
  | nil =>
      simp only [insertCompatible?, Option.some.injEq] at inserted
      subst result
      simp
  | cons first rest ih =>
      by_cases same : entry = first
      · simp only [insertCompatible?, if_pos same, Option.some.injEq] at inserted
        subst result
        exact distinct
      · cases allowed : compatible first entry with
        | false => simp [insertCompatible?, same, allowed] at inserted
        | true =>
            cases next : insertCompatible? compatible entry rest with
            | none => simp [insertCompatible?, same, allowed, next] at inserted
            | some tail =>
                simp only [insertCompatible?, if_neg same, allowed, ↓reduceIte,
                  next, Option.map_some, Option.some.injEq] at inserted
                subst result
                refine nodup_cons.mpr ⟨?_, ih tail distinct.tail next⟩
                rw [insertCompatible?_mem_iff compatible entry rest tail next]
                exact fun member => member.elim (fun equal => same equal.symm)
                  (nodup_cons.mp distinct).1

theorem unionCompatible?_nodup (compatible : α → α → Bool) (kept incoming result : List α)
    (distinct : kept.Nodup) (joined : unionCompatible? compatible kept incoming = some result) :
    result.Nodup := by
  induction incoming generalizing kept with
  | nil =>
      simp only [unionCompatible?, Option.some.injEq] at joined
      subst result
      exact distinct
  | cons entry rest ih =>
      cases next : insertCompatible? compatible entry kept with
      | none => simp [unionCompatible?, next] at joined
      | some entries =>
          simp only [unionCompatible?, next] at joined
          exact ih entries (insertCompatible?_nodup compatible entry kept entries distinct next) joined

theorem unionCompatible?_kept_sublist (compatible : α → α → Bool)
    (kept incoming result : List α) (joined : unionCompatible? compatible kept incoming = some result) :
    kept.Sublist result := by
  induction incoming generalizing kept with
  | nil =>
      simp only [unionCompatible?, Option.some.injEq] at joined
      subst result
      exact Sublist.refl _
  | cons entry rest ih =>
      cases next : insertCompatible? compatible entry kept with
      | none => simp [unionCompatible?, next] at joined
      | some entries =>
          simp only [unionCompatible?, next] at joined
          exact (insertCompatible?_kept_sublist compatible entry kept entries next).trans
            (ih entries joined)

theorem unionCompatible?_isSome_iff (compatible : α → α → Bool)
    (reflexive : ∀ entry, compatible entry entry = true)
    (symmetric : ∀ first second, compatible first second = compatible second first)
    (kept incoming : List α) (accepted : AllCompatible compatible kept) :
    (unionCompatible? compatible kept incoming).isSome = true ↔
      AllCompatible compatible (kept ++ incoming) := by
  constructor
  · intro completed
    cases joined : unionCompatible? compatible kept incoming with
    | none => simp [joined] at completed
    | some result =>
        apply (unionCompatible?_allCompatible compatible reflexive symmetric kept incoming result
          accepted joined).mono
        intro item member
        exact (unionCompatible?_mem_iff compatible kept incoming result joined item).mpr
          (mem_append.mp member)
  · intro fullAccepted
    induction incoming generalizing kept with
    | nil => simp [unionCompatible?]
    | cons entry rest ih =>
        have admitted : (insertCompatible? compatible entry kept).isSome = true :=
          (insertCompatible?_isSome_iff compatible entry kept accepted).mpr
            (fun previous member => fullAccepted previous (mem_append_left _ member)
              entry (by simp))
        cases next : insertCompatible? compatible entry kept with
        | none => simp [next] at admitted
        | some entries =>
            have nextAccepted : AllCompatible compatible entries :=
              insertCompatible?_allCompatible compatible reflexive symmetric entry kept entries
                accepted next
            have nextFull : AllCompatible compatible (entries ++ rest) := by
              apply fullAccepted.mono
              intro item member
              rcases mem_append.mp member with fromEntries | fromRest
              · rcases (insertCompatible?_mem_iff compatible entry kept entries next item).mp
                  fromEntries with same | fromKept
                · subst item
                  simp
                · exact mem_append_left _ fromKept
              · exact mem_append_right _ (mem_cons_of_mem _ fromRest)
            rw [unionCompatible?, next]
            exact ih entries nextAccepted nextFull

theorem unionCompatible?_from_empty_isSome_iff (compatible : α → α → Bool)
    (reflexive : ∀ entry, compatible entry entry = true)
    (symmetric : ∀ first second, compatible first second = compatible second first)
    (incoming : List α) :
    (unionCompatible? compatible [] incoming).isSome = true ↔
      AllCompatible compatible incoming := by
  simpa only [nil_append] using
    unionCompatible?_isSome_iff compatible reflexive symmetric [] incoming (allCompatible_nil _)

end List
