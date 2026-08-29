import OfficialKrennDefinitions

/-!
Colour-dimension monotonicity for the official Krenn–Gu encoding
(Sol Pro second audit, `DimensionMonotonicity_candidate.lean`, repaired):
every official `D`-colour witness restricts along an injection
`Fin d ↪ Fin D` to a `d`-colour witness, so nonexistence at `D = 3`
settles every official `N = 6, D ≥ 3` instance at once.

Repairs relative to the candidate: the recursion bound uses `omega`
instead of a named `Nat` lemma; the witness transport rewrites the
dependent `if` via `if_congr` instead of `rw` on the condition; the
`Fin` inclusion reuses Mathlib's `Fin.castLEEmb`.
-/

namespace MonochromaticQuantumGraph

/-- Restrict a `D`-colour official weight system along a map `Fin d → Fin D`. -/
def restrictColors {N d D : Nat} {α : Type}
    (f : Fin d → Fin D) (W : WeightsN N D α) : WeightsN N d α
  | ⟨u, v, i, j⟩ => W ⟨u, v, f i, f j⟩

/-- Naturality of the recursive perfect-matching sum under colour restriction. -/
theorem pmSumListAux_restrictColors {N d D : Nat} {α : Type} [Semiring α]
    (f : Fin d → Fin D) (W : WeightsN N D α) (ι : V N → Fin d) :
    ∀ n L,
      pmSumListAux (restrictColors f W) ι n L =
        pmSumListAux W (fun v => f (ι v)) n L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro L
      match n, L with
      | 0, _ => rfl
      | 1, _ => rfl
      | (n + 2), [] => rfl
      | (n + 2), [_] => rfl
      | (n + 2), v :: u :: us =>
          simp only [pmSumListAux, restrictColors, mkEdge]
          apply congrArg List.sum
          apply List.map_congr_left
          intro w _
          congr 1
          exact ih n (by omega) ((u :: us).erase w)

/-- Naturality of the official `K_N` perfect-matching sum. -/
theorem pmSumN_restrictColors {N d D : Nat} {α : Type} [Semiring α]
    (f : Fin d → Fin D) (W : WeightsN N D α) (ι : V N → Fin d) :
    pmSumN N d (restrictColors f W) ι =
      pmSumN N D W (fun v => f (ι v)) := by
  simpa [pmSumN, pmSumList] using
    pmSumListAux_restrictColors f W ι (vertices N).length (vertices N)

/-- Injective colour renaming reflects the official all-equal predicate. -/
theorem allEqual_comp_iff {N d D : Nat} (f : Fin d → Fin D)
    (hf : Function.Injective f) (ι : V N → Fin d) :
    allEqual (fun v => f (ι v)) ↔ allEqual ι := by
  simp only [allEqual, allEqualList]
  induction vertices N with
  | nil => simp
  | cons v vs ih =>
      cases vs with
      | nil => simp
      | cons w ws =>
          simp only [List.isChain_cons] at ih ⊢
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨fun y hy => hf (h1 y hy), ih.mp h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨fun y hy => congrArg f (h1 y hy), ih.mpr h2⟩

/-- Every official `D`-colour witness restricts to a `d`-colour witness. -/
theorem EqSystemN.restrictColors {N d D : Nat} {α : Type} [Semiring α]
    (f : Fin d → Fin D) (hf : Function.Injective f)
    {W : WeightsN N D α} (hW : EqSystemN N D W) :
    EqSystemN N d (MonochromaticQuantumGraph.restrictColors f W) := by
  intro ι
  rw [pmSumN_restrictColors, hW (fun v => f (ι v))]
  exact if_congr (allEqual_comp_iff f hf ι) rfl rfl

/-- Nonexistence is monotone upward in the number of colours. -/
theorem noSolution_mono_colours {N d D : Nat} {α : Type} [Semiring α]
    (h : d ≤ D)
    (hsmall : ¬ ∃ W : WeightsN N d α, EqSystemN N d W) :
    ¬ ∃ W : WeightsN N D α, EqSystemN N D W := by
  rintro ⟨W, hW⟩
  exact hsmall ⟨restrictColors (Fin.castLEEmb h) W,
    hW.restrictColors (Fin.castLEEmb h) (Fin.castLEEmb h).injective⟩

/-- `N = 6, D = 3` settles every official `N = 6, D ≥ 3` instance. -/
theorem noSolution6_ge3_of_d3 {α : Type} [Semiring α]
    (h3 : ¬ ∃ W : WeightsN 6 3 α, EqSystemN 6 3 W) :
    ∀ D, 3 ≤ D → ¬ ∃ W : WeightsN 6 D α, EqSystemN 6 D W := by
  intro D hD
  exact noSolution_mono_colours hD h3

end MonochromaticQuantumGraph
