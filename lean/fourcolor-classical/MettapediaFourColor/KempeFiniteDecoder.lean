import MettapediaFourColor.KempeMatchingChromogram

/-!
# A checked finite bridge from chromograms to supplied matchings

The parser enumerates only accepted chromograms, following the reference
stack transitions. A source can validate a small list of inverse witnesses
and then use structural matching theorems in an arbitrary Kempe-closed
exterior. This is a bounded inverse bridge, not a general matching decoder.
-/

namespace FourColor.KempeFiniteDecoder

/-- Accepted parses in the exact reference stack context. -/
def parses (stack : List Bool) : List Color → List Chromogram
  | [] => if stack.isEmpty then [[]] else []
  | c :: cs => ([.skip, .push, .pop0, .pop1] : List GramSymbol).flatMap fun s =>
      match matchStep c s stack with
      | none => []
      | some next => (parses next cs).map (s :: ·)

theorem mem_parses (stack : List Bool) (cs : List Color) (w : Chromogram) :
    w ∈ parses stack cs ↔ matchg stack cs w = true := by
  induction cs generalizing stack w with
  | nil => cases w <;> simp [parses, matchg] <;> split <;> simp_all
  | cons c cs ih =>
    cases w with
    | nil =>
      simp only [parses, List.mem_flatMap, matchg_cons_nil, Bool.false_eq_true, iff_false]
      rintro ⟨s, _, hw⟩
      cases hs : matchStep c s stack <;> simp [hs] at hw
    | cons s w =>
      simp only [parses, List.mem_flatMap]
      constructor
      · rintro ⟨s', _, hw⟩
        cases hs : matchStep c s' stack with
        | none => simp [hs] at hw
        | some next =>
          simp only [hs, List.mem_map, List.cons.injEq] at hw
          obtain ⟨w', hw', rfl, rfl⟩ := hw
          simpa [matchg, hs] using (ih next w').mp hw'
      · intro hw
        refine ⟨s, by cases s <;> simp, ?_⟩
        cases hs : matchStep c s stack with
        | none => simp [matchg, hs] at hw
        | some next =>
          simp only [List.mem_map]
          exact ⟨w, (ih next w).mpr (by simpa [matchg, hs] using hw), rfl⟩

end FourColor.KempeFiniteDecoder
