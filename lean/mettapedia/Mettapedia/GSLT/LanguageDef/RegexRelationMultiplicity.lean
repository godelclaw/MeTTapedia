import Mettapedia.GSLT.LanguageDef.RegexRelationKernel

/-!
# Exact occurrence multiplicity before public projection

Each accepting keyed-simple source occurrence occupies exactly one delivery
position. Different branch histories remain distinct even when projection
returns equal spans and captures. No deduplication is performed on public
values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexRelationMultiplicity

open RegexRelationEnumeration
open RegexObservationTrace (ObservedAction)

universe u v

theorem prepend_injective {State : Type u} {Key : Type v} (bits : List Bool) (point : Key) :
    Function.Injective (prepend (State := State) bits point) := by
  intro first second equal
  have values := congrArg Occurrence.value equal
  have choices := congrArg Occurrence.choices equal
  have points := congrArg Occurrence.points equal
  simp only [prepend] at values choices points
  have choicesEqual := List.append_cancel_left choices
  have pointsEqual := (List.cons.inj points).2
  cases first
  cases second
  cases values
  cases choicesEqual
  cases pointsEqual
  rfl

theorem opposite_branches_are_distinct {State : Type u} {Key : Type v} (point : Key)
    (first second : Occurrence State Key) : prepend [false] point first ≠ prepend [true] point second := by
  intro same
  have choices := congrArg Occurrence.choices same
  simp [prepend] at choices

theorem enumerate_occurrences_nodup {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (depth : Nat) : ∀ seen first, (enumerate step key eligible depth seen first).Nodup := by
  induction depth with
  | zero => simp [enumerate]
  | succ depth ih =>
      intro seen first
      by_cases visited : key first ∈ seen
      · simp [enumerate, visited]
      · cases operation : step first with
        | dead => simp [enumerate, visited, operation]
        | accept => cases allowed : eligible first <;> simp [enumerate, visited, operation, allowed]
        | next target bits =>
            simp only [enumerate, visited, ↓reduceIte, operation]
            exact (ih _ _).map (prepend_injective bits (key first))
        | branch left right =>
            simp only [enumerate, visited, ↓reduceIte, operation]
            apply List.nodup_append.mpr
            refine ⟨(ih _ _).map (prepend_injective [false] (key first)),
              (ih _ _).map (prepend_injective [true] (key first)), ?_⟩
            intro first firstMember second secondMember
            obtain ⟨first, _, rfl⟩ := List.mem_map.mp firstMember
            obtain ⟨second, _, rfl⟩ := List.mem_map.mp secondMember
            exact opposite_branches_are_distinct _ first second

theorem all_occurrences_nodup {State : Type u} {Key : Type v} [DecidableEq Key] [Fintype Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool) (first : State) :
    (all step key eligible first).Nodup := enumerate_occurrences_nodup _ _ _ _ _ _

theorem each_source_occurrence_has_one_position {State : Type u} {Key : Type v}
    [DecidableEq Key] [Fintype Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (first : State) (occurrence : Occurrence State Key) :
    (Trace step key eligible first occurrence.choices occurrence.points occurrence.value ∧ occurrence.points.Nodup) ↔
      ∃! position : Fin (all step key eligible first).length, (all step key eligible first)[position] = occurrence := by
  constructor
  · intro source
    have member := (all_exact step key eligible first occurrence).mpr source
    obtain ⟨index, bounded, value⟩ := List.mem_iff_getElem.mp member
    refine ⟨⟨index,bounded⟩, value, ?_⟩
    intro other same
    apply Fin.ext
    exact (List.getElem_inj (all_occurrences_nodup step key eligible first)).mp (same.trans value.symm)
  · rintro ⟨index, value, _⟩
    apply (all_exact step key eligible first occurrence).mp
    rw [← value]
    exact List.getElem_mem _

end Mettapedia.GSLT.LanguageDef.RegexRelationMultiplicity
