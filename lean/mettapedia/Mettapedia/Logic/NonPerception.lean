import Mathlib.Logic.Basic

/-!
# Non-perception: when absence is negation

Dharmakīrti's account of negative knowledge, inference from non-perception
(*anupalabdhi*): not perceiving a thing proves its absence when the thing is
perceptible, that is, when it would have been perceived had it been there; not
perceiving an imperceptible thing yields only doubt; and non-perception does not
reach the future.  (Mokṣākaragupta's *Tarkabhāṣā* §13.3–13.4, citing Dharmakīrti's
*Nyāyabindu* II.28 and *Pramāṇavārttika* I.3: the non-cognition of a perceptible
object works "through the presence of the counter-proof", that of an imperceptible
one "through the absence of the proof", hence through doubt.)

States are ordered by a reflexive relation `Future`: later stages, extensions of a
scenario, refinements of a vantage, more budget, or the facts themselves.
`Perceived w` says that the thing is perceived at `w`.

* **Absence** (`Absent w`): the thing is perceived at no future of `w`.  In a Kripke
  or presheaf reading this is native negation.
* **Perceptibility** (`Perceptible w`): whatever is perceived at a future of `w` is
  already perceived at `w`.
* **The law.**
  - Absence implies non-perception (`not_perceived_of_absent`).
  - At a perceptible state, non-perception is absence (`absent_iff_not_perceived`).
  - Perceptibility is exactly the condition under which non-perception establishes
    absence (`perceptible_iff`), and at every state of a frame exactly when every
    state is perceptible (`forall_perceptible_iff`).
  - At a state that is not perceptible the thing is neither perceived nor absent,
    and some future perceives it: doubt (`doubt_iff_not_perceptible`).
* **Truth.**  When what is perceived is true and every truth is perceived at some
  future of every state, absence is falsity (`absent_iff_not`), non-perception at a
  perceptible state refutes (`refutes_of_perceptible`), and at a state in doubt the
  claim is true (`true_of_doubt`).
* **Persistence.**  When perception persists along futures and futures compose,
  absence persists (`Absent.future`).

Controls: a two-stage frame in which the thing appears only at the later stage is
in doubt at the earlier one (`Control.early_doubt`) and perceptible at the later
one (`Control.late_perceptible`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.NonPerception

universe u

/-- States ordered by a reflexive future relation, with what is perceived at each. -/
structure Frame (W : Type u) where
  Future : W → W → Prop
  future_refl : ∀ w, Future w w
  Perceived : W → Prop

namespace Frame

variable {W : Type u} (F : Frame W)

/-- **Absence**: perceived at no future. -/
def Absent (w : W) : Prop :=
  ∀ w', F.Future w w' → ¬ F.Perceived w'

/-- **Perceptibility**: whatever a future perceives is already perceived. -/
def Perceptible (w : W) : Prop :=
  ∀ w', F.Future w w' → F.Perceived w' → F.Perceived w

/-- **Doubt**: neither perceived nor absent. -/
def Doubt (w : W) : Prop :=
  ¬ F.Perceived w ∧ ¬ F.Absent w

variable {F}

/-- Absence implies non-perception. -/
theorem not_perceived_of_absent {w : W} (absent : F.Absent w) : ¬ F.Perceived w :=
  absent w (F.future_refl w)

/-- A perceived state is perceptible. -/
theorem perceptible_of_perceived {w : W} (perceived : F.Perceived w) : F.Perceptible w :=
  fun _ _ _ => perceived

/-- **At a perceptible state, non-perception is absence.** -/
theorem absent_iff_not_perceived {w : W} (perceptible : F.Perceptible w) :
    F.Absent w ↔ ¬ F.Perceived w :=
  ⟨not_perceived_of_absent, fun notPerceived w' future perceived =>
    notPerceived (perceptible w' future perceived)⟩

/-- **Perceptibility is exactly what lets non-perception establish absence.** -/
theorem perceptible_iff {w : W} : F.Perceptible w ↔ (¬ F.Perceived w → F.Absent w) := by
  constructor
  · intro perceptible notPerceived
    exact (absent_iff_not_perceived perceptible).mpr notPerceived
  · intro establishes w' future perceived'
    exact Classical.byContradiction fun notPerceived =>
      establishes notPerceived w' future perceived'

/-- Over a whole frame: non-perception establishes absence everywhere exactly when
every state is perceptible. -/
theorem forall_perceptible_iff :
    (∀ w, F.Perceptible w) ↔ ∀ w, ¬ F.Perceived w → F.Absent w :=
  forall_congr' fun _ => perceptible_iff

/-- **Doubt is exactly the failure of perceptibility.** -/
theorem doubt_iff_not_perceptible {w : W} : F.Doubt w ↔ ¬ F.Perceptible w := by
  constructor
  · rintro ⟨notPerceived, notAbsent⟩ perceptible
    exact notAbsent ((absent_iff_not_perceived perceptible).mpr notPerceived)
  · intro notPerceptible
    refine ⟨fun perceived => notPerceptible (perceptible_of_perceived perceived), ?_⟩
    intro absent
    apply notPerceptible
    intro w' future perceived'
    exact (absent w' future perceived').elim

/-- At a state in doubt some future perceives the thing. -/
theorem exists_future_perceived_of_doubt {w : W} (doubt : F.Doubt w) :
    ∃ w', F.Future w w' ∧ F.Perceived w' :=
  Classical.byContradiction fun none =>
    doubt.2 fun w' future perceived => none ⟨w', future, perceived⟩

/-- Every state is perceived, absent, or in doubt, and the three exclude each other. -/
theorem perceived_or_absent_or_doubt (w : W) :
    F.Perceived w ∨ F.Absent w ∨ F.Doubt w := by
  by_cases perceived : F.Perceived w
  · exact Or.inl perceived
  · by_cases absent : F.Absent w
    · exact Or.inr (Or.inl absent)
    · exact Or.inr (Or.inr ⟨perceived, absent⟩)

theorem not_perceived_of_doubt {w : W} (doubt : F.Doubt w) : ¬ F.Perceived w := doubt.1

theorem not_absent_of_doubt {w : W} (doubt : F.Doubt w) : ¬ F.Absent w := doubt.2

/-! ## Truth -/

section Truth

variable (claim : Prop)

/-- What is perceived is true. -/
def Sound : Prop := ∀ w, F.Perceived w → claim

/-- A true claim is perceived at some future of every state. -/
def EventuallyComplete : Prop := claim → ∀ w, ∃ w', F.Future w w' ∧ F.Perceived w'

variable {claim}

/-- **Absence is falsity** for sound, eventually complete perception. -/
theorem absent_iff_not (sound : F.Sound claim) (complete : F.EventuallyComplete claim) (w : W) :
    F.Absent w ↔ ¬ claim := by
  constructor
  · intro absent holds
    obtain ⟨w', future, perceived⟩ := complete holds w
    exact absent w' future perceived
  · intro notHolds w' _ perceived
    exact notHolds (sound w' perceived)

/-- **Non-perception at a perceptible state refutes.** -/
theorem refutes_of_perceptible (sound : F.Sound claim) (complete : F.EventuallyComplete claim)
    {w : W} (perceptible : F.Perceptible w) (notPerceived : ¬ F.Perceived w) : ¬ claim :=
  (absent_iff_not sound complete w).mp ((absent_iff_not_perceived perceptible).mpr notPerceived)

/-- **At a state in doubt the claim is true**: doubt only arises where a future
perceives it. -/
theorem true_of_doubt (sound : F.Sound claim) {w : W} (doubt : F.Doubt w) : claim := by
  obtain ⟨w', _, perceived⟩ := exists_future_perceived_of_doubt doubt
  exact sound w' perceived

end Truth

/-! ## Persistence -/

/-- Perception persists along futures. -/
def Persistent : Prop :=
  ∀ w w', F.Future w w' → F.Perceived w → F.Perceived w'

/-- Futures compose. -/
def Transitive : Prop :=
  ∀ w w' w'', F.Future w w' → F.Future w' w'' → F.Future w w''

/-- With composable futures, absence persists. -/
theorem Absent.future (transitive : F.Transitive) {w w' : W} (absent : F.Absent w)
    (future : F.Future w w') : F.Absent w' :=
  fun w'' later perceived => absent w'' (transitive w w' w'' future later) perceived

/-- With persistent perception, a perceived state stays perceptible at every future. -/
theorem Perceptible.of_perceived_future (persistent : F.Persistent) {w w' : W}
    (future : F.Future w w') (perceived : F.Perceived w) : F.Perceptible w' :=
  perceptible_of_perceived (persistent w w' future perceived)

end Frame

/-! ## Controls -/

namespace Control

/-- Two stages, `false` before `true`; the thing appears only at the later stage. -/
def twoStages : Frame Bool where
  Future early late := early = false ∨ early = late
  future_refl _ := Or.inr rfl
  Perceived stage := stage = true

/-- Negative control: at the early stage non-perception is doubt, not absence. -/
theorem early_doubt : twoStages.Doubt false :=
  ⟨Bool.false_ne_true, fun absent => absent true (Or.inl rfl) rfl⟩

/-- Positive control: the late stage is perceptible. -/
theorem late_perceptible : twoStages.Perceptible true :=
  Frame.perceptible_of_perceived rfl

/-- Negative control: the early stage is not perceptible. -/
theorem early_not_perceptible : ¬ twoStages.Perceptible false :=
  Frame.doubt_iff_not_perceptible.mp early_doubt

end Control

end Mettapedia.Logic.NonPerception
