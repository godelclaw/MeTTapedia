import Mettapedia.TypeTheory.PromotionAdmission.Terms
import Mathlib.Data.Finset.Card
import Mathlib.Data.Prod.Lex

/-!
# Unification at a fuel, with three honest answers

Critical pairs are found by unifying a subterm of one left side with another left side. The
unifier here is the rule system of Martelli and Montanari (delete, decompose, eliminate, with
the occurs check), run for at most `n` rounds. It has three answers, kept apart:

* `ok θ`: θ unifies the equations, and it is a **most general** unifier in the strong sense
  that every unifier `ρ`, into terms over any variable type, satisfies `ρ = θ ; ρ`
  (`unify_ok_unifies`, `unify_ok_general`);
* `fail`: no substitution into any variable type unifies the equations (`unify_fail`), because
  two symbols clash or a variable occurs strictly inside its own value;
* `outOfFuel`: the rounds ran out. This is not a failure.

A decided answer does not change with more fuel (`unify_mono`), and some fuel always decides
(`unify_terminates`, by the lexicographic measure: number of distinct variables, then size).
The definition is structural in the fuel, so the kernel evaluates it on concrete rules.

Positive example: `add x zero` and `add y zero` unify. Negative examples: `add x zero` and
`add zero (succ y)` clash; `x` and `succ x` fail the occurs check.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u v w

open Term

/-- The answer of a unification run. -/
inductive UnifyResult (F : Type u) (X : Type v) where
  | ok (θ : X → Term F X)
  | fail
  | outOfFuel

variable {F : Type u} {X : Type v}

/-- `ρ` unifies every equation of the list. -/
def Unifies {W : Type w} (ρ : X → Term F W) (E : List (Term F X × Term F X)) : Prop :=
  ∀ p ∈ E, p.1.subst ρ = p.2.subst ρ

namespace UnifyResult

/-- Precompose a successful answer with a substitution. -/
def compose (r : UnifyResult F X) (σ : X → Term F X) : UnifyResult F X :=
  match r with
  | .ok θ => .ok fun y => (σ y).subst θ
  | .fail => .fail
  | .outOfFuel => .outOfFuel

theorem compose_ok {r : UnifyResult F X} {σ : X → Term F X} {θ : X → Term F X}
    (h : r.compose σ = .ok θ) : ∃ θ', r = .ok θ' ∧ θ = fun y => (σ y).subst θ' := by
  cases r with
  | ok θ' => simp only [compose, ok.injEq] at h; exact ⟨θ', rfl, h.symm⟩
  | fail => simp [compose] at h
  | outOfFuel => simp [compose] at h

theorem compose_fail {r : UnifyResult F X} {σ : X → Term F X} (h : r.compose σ = .fail) :
    r = .fail := by
  cases r <;> simp_all [compose]

theorem compose_ne_outOfFuel {r : UnifyResult F X} {σ : X → Term F X}
    (h : r.compose σ ≠ .outOfFuel) : r ≠ .outOfFuel := by
  cases r <;> simp_all [compose]

theorem compose_ne_outOfFuel_of {r : UnifyResult F X} {σ : X → Term F X}
    (h : r ≠ .outOfFuel) : r.compose σ ≠ .outOfFuel := by
  cases r <;> simp_all [compose]

end UnifyResult

/-! ## Unifiers -/

theorem unifies_cons {W : Type w} {ρ : X → Term F W} {s t : Term F X}
    {rest : List (Term F X × Term F X)} :
    Unifies ρ ((s, t) :: rest) ↔ s.subst ρ = t.subst ρ ∧ Unifies ρ rest := by
  simp [Unifies]

theorem unifies_append {W : Type w} {ρ : X → Term F W} {E E' : List (Term F X × Term F X)} :
    Unifies ρ (E ++ E') ↔ Unifies ρ E ∧ Unifies ρ E' := by
  simp only [Unifies, List.mem_append]
  exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
    fun h p hp => hp.elim (h.1 p) (h.2 p)⟩

/-- Arguments of equal length have equal instances exactly when every pair does. -/
theorem map_subst_eq_iff_zip {W : Type w} (ρ : X → Term F W) :
    ∀ (ss ts : List (Term F X)), ss.length = ts.length →
      (ss.map (Term.subst ρ) = ts.map (Term.subst ρ) ↔ Unifies ρ (ss.zip ts))
  | [], [], _ => by simp [Unifies]
  | s :: ss, t :: ts, same => by
      simp only [List.map_cons, List.cons.injEq, List.zip_cons_cons]
      rw [unifies_cons, map_subst_eq_iff_zip ρ ss ts (by simpa using same)]
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

theorem unifies_app_iff {W : Type w} (ρ : X → Term F W) {f g : F}
    {ss ts : List (Term F X)} :
    (Term.app f ss).subst ρ = (Term.app g ts).subst ρ ↔
      f = g ∧ ss.length = ts.length ∧ Unifies ρ (ss.zip ts) := by
  simp only [subst_app, app.injEq]
  constructor
  · rintro ⟨rfl, maps⟩
    have lengths : ss.length = ts.length := by simpa using congrArg List.length maps
    exact ⟨rfl, lengths, (map_subst_eq_iff_zip ρ ss ts lengths).mp maps⟩
  · rintro ⟨rfl, lengths, zipped⟩
    exact ⟨rfl, (map_subst_eq_iff_zip ρ ss ts lengths).mpr zipped⟩

theorem unifies_swap_head {W : Type w} {ρ : X → Term F W} {s t : Term F X}
    {rest : List (Term F X × Term F X)} :
    Unifies ρ ((s, t) :: rest) ↔ Unifies ρ ((t, s) :: rest) := by
  rw [unifies_cons, unifies_cons, eq_comm]

/-- An occurrence strictly inside the other side leaves no unifier. -/
theorem occurs_not_unifiable {W : Type w} {x : X} {t : Term F X} (notVar : t ≠ .var x)
    (occurs : x ∈ t.vars) (ρ : X → Term F W) : ρ x ≠ t.subst ρ := by
  intro same
  cases t with
  | var y =>
      simp only [vars_var, List.mem_singleton] at occurs
      exact notVar (by rw [occurs])
  | app f ss =>
      have := size_lt_subst_of_mem_app ρ occurs
      rw [← same] at this
      exact lt_irrefl _ this

/-- The variables of a list of equations. -/
def eqVars (E : List (Term F X × Term F X)) : List X :=
  E.flatMap fun p => p.1.vars ++ p.2.vars

/-- The size of a list of equations. -/
def eqSize (E : List (Term F X × Term F X)) : ℕ :=
  (E.map fun p => p.1.size + p.2.size).sum

theorem eqVars_cons (s t : Term F X) (rest : List (Term F X × Term F X)) :
    eqVars ((s, t) :: rest) = s.vars ++ t.vars ++ eqVars rest := by
  simp [eqVars]

theorem eqVars_append (E E' : List (Term F X × Term F X)) :
    eqVars (E ++ E') = eqVars E ++ eqVars E' := by
  simp [eqVars]

theorem eqSize_cons (s t : Term F X) (rest : List (Term F X × Term F X)) :
    eqSize ((s, t) :: rest) = s.size + t.size + eqSize rest := by
  simp [eqSize]

theorem eqSize_append (E E' : List (Term F X × Term F X)) :
    eqSize (E ++ E') = eqSize E + eqSize E' := by
  simp [eqSize]

theorem eqVars_zip : ∀ (ss ts : List (Term F X)), ss.length = ts.length →
    ∀ z, z ∈ eqVars (ss.zip ts) ↔ z ∈ ss.flatMap Term.vars ∨ z ∈ ts.flatMap Term.vars
  | [], [], _, z => by simp [eqVars]
  | s :: ss, t :: ts, same, z => by
      have := eqVars_zip ss ts (by simpa using same) z
      simp only [List.zip_cons_cons, eqVars_cons, List.mem_append, List.flatMap_cons] at this ⊢
      rw [this]
      tauto
  | [], _ :: _, same, _ => by simp at same
  | _ :: _, [], same, _ => by simp at same

theorem eqSize_zip : ∀ (ss ts : List (Term F X)), ss.length = ts.length →
    eqSize (ss.zip ts) = (ss.map Term.size).sum + (ts.map Term.size).sum
  | [], [], _ => by simp [eqSize]
  | s :: ss, t :: ts, same => by
      have := eqSize_zip ss ts (by simpa using same)
      simp only [List.zip_cons_cons, eqSize_cons, this, List.map_cons, List.sum_cons]
      omega
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

/-! ## One elimination -/

variable [DecidableEq X]

/-- The substitution of `t` for the variable `x`. -/
def single (x : X) (t : Term F X) (y : X) : Term F X := if y = x then t else .var y

/-- Instantiate both sides of every equation. -/
def substEqs (σ : X → Term F X) (E : List (Term F X × Term F X)) :
    List (Term F X × Term F X) :=
  E.map fun p => (p.1.subst σ, p.2.subst σ)

theorem subst_single_of_not_mem {x : X} {t : Term F X} {u : Term F X} (fresh : x ∉ u.vars) :
    u.subst (single x t) = u := by
  rw [subst_congr (τ := Term.var) u (fun y hy => by
    have : y ≠ x := fun same => fresh (same ▸ hy)
    simp [single, this]), subst_id]

/-- A substitution that already sends `x` to the value of `t` absorbs the elimination. -/
theorem single_absorb {W : Type w} {x : X} {t : Term F X} {ρ : X → Term F W}
    (agree : ρ x = t.subst ρ) (u : Term F X) :
    (u.subst (single x t)).subst ρ = u.subst ρ := by
  rw [subst_subst]
  apply subst_congr
  intro y _
  by_cases same : y = x
  · subst same; simp [single, agree]
  · simp [single, same]

/-- Every unifier of an elimination's equation unifies the instantiated remainder. -/
theorem unifies_substEqs {W : Type w} {x : X} {t : Term F X} {ρ : X → Term F W}
    (agree : ρ x = t.subst ρ) {rest : List (Term F X × Term F X)} (unified : Unifies ρ rest) :
    Unifies ρ (substEqs (single x t) rest) := by
  intro p member
  simp only [substEqs, List.mem_map] at member
  obtain ⟨q, qMember, rfl⟩ := member
  simp only [single_absorb agree]
  exact unified q qMember

/-- The answer after an elimination is a unifier and is most general. -/
theorem elim_ok {x : X} {t : Term F X} (fresh : x ∉ t.vars)
    {rest : List (Term F X × Term F X)} {θ' : X → Term F X}
    (unifiesRest : Unifies θ' (substEqs (single x t) rest))
    (generalRest : ∀ {W : Type w} (ρ : X → Term F W),
      Unifies ρ (substEqs (single x t) rest) → ∀ y, (θ' y).subst ρ = ρ y) :
    Unifies (fun y => (single x t y).subst θ') ((.var x, t) :: rest) ∧
      ∀ {W : Type w} (ρ : X → Term F W), Unifies ρ ((.var x, t) :: rest) →
        ∀ y, ((single x t y).subst θ').subst ρ = ρ y := by
  refine ⟨?_, ?_⟩
  · rw [unifies_cons]
    refine ⟨?_, ?_⟩
    · show (single x t x).subst θ' = t.subst (fun y => (single x t y).subst θ')
      rw [← subst_subst, subst_single_of_not_mem fresh]
      simp [single]
    · intro p member
      rw [← subst_subst, ← subst_subst]
      exact unifiesRest _ (List.mem_map_of_mem member)
  · intro W ρ unified y
    rw [unifies_cons] at unified
    obtain ⟨agree, unifiedRest⟩ := unified
    simp only [subst_var] at agree
    have general := generalRest ρ (unifies_substEqs agree unifiedRest)
    rw [subst_subst]
    have : (single x t y).subst (fun z => (θ' z).subst ρ) = (single x t y).subst ρ :=
      subst_congr _ (fun z _ => general z)
    rw [this]
    by_cases same : y = x
    · subst same; simp [single, agree]
    · simp [single, same]

theorem vars_subst_single {x : X} {t : Term F X} (fresh : x ∉ t.vars) (u : Term F X) {z : X}
    (member : z ∈ (u.subst (single x t)).vars) : z ≠ x ∧ (z ∈ u.vars ∨ z ∈ t.vars) := by
  rw [vars_subst, List.mem_flatMap] at member
  obtain ⟨y, yMember, zMember⟩ := member
  by_cases same : y = x
  · subst same
    simp only [single, if_true] at zMember
    exact ⟨fun h => fresh (h ▸ zMember), Or.inr zMember⟩
  · simp only [single, same, if_false, vars_var, List.mem_singleton] at zMember
    subst zMember
    exact ⟨same, Or.inl yMember⟩

theorem eqVars_substEqs {x : X} {t : Term F X} (fresh : x ∉ t.vars)
    (rest : List (Term F X × Term F X)) {z : X} (member : z ∈ eqVars (substEqs (single x t) rest)) :
    z ≠ x ∧ (z ∈ eqVars rest ∨ z ∈ t.vars) := by
  simp only [eqVars, substEqs, List.flatMap_map, List.mem_flatMap, List.mem_append] at member
  obtain ⟨p, pMember, side⟩ := member
  rcases side with left | right
  · obtain ⟨ne, origin⟩ := vars_subst_single fresh p.1 left
    refine ⟨ne, origin.imp (fun h => ?_) id⟩
    simp only [eqVars, List.mem_flatMap, List.mem_append]
    exact ⟨p, pMember, Or.inl h⟩
  · obtain ⟨ne, origin⟩ := vars_subst_single fresh p.2 right
    refine ⟨ne, origin.imp (fun h => ?_) id⟩
    simp only [eqVars, List.mem_flatMap, List.mem_append]
    exact ⟨p, pMember, Or.inr h⟩

/-- The measure of a list of equations: distinct variables, then size. -/
def unifyMeasure (E : List (Term F X × Term F X)) : ℕ ×ₗ ℕ :=
  toLex ((eqVars E).toFinset.card, eqSize E)

theorem measure_lt_of_le_lt {E E' : List (Term F X × Term F X)}
    (vars : ∀ z, z ∈ eqVars E' → z ∈ eqVars E) (size : eqSize E' < eqSize E) :
    unifyMeasure E' < unifyMeasure E := by
  have card : (eqVars E').toFinset.card ≤ (eqVars E).toFinset.card :=
    Finset.card_le_card (fun z hz => by simpa using vars z (by simpa using hz))
  simp only [unifyMeasure, Prod.Lex.toLex_lt_toLex]
  omega

theorem measure_lt_of_elim {x : X} {t : Term F X} (fresh : x ∉ t.vars)
    {E rest : List (Term F X × Term F X)} (xIn : x ∈ eqVars E)
    (restIn : ∀ z, z ∈ eqVars rest → z ∈ eqVars E) (tIn : ∀ z, z ∈ t.vars → z ∈ eqVars E) :
    unifyMeasure (substEqs (single x t) rest) < unifyMeasure E := by
  have card : (eqVars (substEqs (single x t) rest)).toFinset.card < (eqVars E).toFinset.card := by
    apply Finset.card_lt_card
    refine ⟨fun z hz => ?_, fun sub => ?_⟩
    · obtain ⟨_, origin⟩ := eqVars_substEqs fresh rest (by simpa using hz)
      simpa using origin.elim (restIn z) (tIn z)
    · have := sub (by simpa using xIn)
      exact (eqVars_substEqs fresh rest (by simpa using this)).1 rfl
  simp only [unifyMeasure, Prod.Lex.toLex_lt_toLex]
  exact Or.inl card

/-! ## The run -/

variable [DecidableEq F]

/-- **Unification at a fuel** (Martelli–Montanari). -/
def unify : ℕ → List (Term F X × Term F X) → UnifyResult F X
  | 0, _ => .outOfFuel
  | _ + 1, [] => .ok Term.var
  | n + 1, (.var x, t) :: rest =>
      if t = .var x then unify n rest
      else if x ∈ t.vars then .fail
      else (unify n (substEqs (single x t) rest)).compose (single x t)
  | n + 1, (.app f ss, .var y) :: rest =>
      if y ∈ (Term.app f ss).vars then .fail
      else (unify n (substEqs (single y (.app f ss)) rest)).compose (single y (.app f ss))
  | n + 1, (.app f ss, .app g ts) :: rest =>
      if f = g ∧ ss.length = ts.length then unify n (ss.zip ts ++ rest) else .fail

/-- **`ok` gives a unifier.** -/
theorem unify_ok_unifies : ∀ (n : ℕ) (E : List (Term F X × Term F X)) (θ : X → Term F X),
    unify n E = .ok θ → Unifies θ E ∧
      ∀ {W : Type w} (ρ : X → Term F W), Unifies ρ E → ∀ y, (θ y).subst ρ = ρ y
  | 0, E, θ, h => by simp [unify] at h
  | n + 1, [], θ, h => by
      simp only [unify, UnifyResult.ok.injEq] at h
      subst h
      exact ⟨fun p member => by simp at member, fun ρ _ y => by simp⟩
  | n + 1, (.var x, t) :: rest, θ, h => by
      simp only [unify] at h
      split_ifs at h with same occurs
      · obtain ⟨unifiesRest, generalRest⟩ := unify_ok_unifies n rest θ h
        subst same
        exact ⟨unifies_cons.mpr ⟨rfl, unifiesRest⟩,
          fun ρ unified => generalRest ρ (unifies_cons.mp unified).2⟩
      · obtain ⟨θ', inner, rfl⟩ := UnifyResult.compose_ok h
        obtain ⟨unifiesRest, generalRest⟩ := unify_ok_unifies n _ θ' inner
        exact elim_ok occurs unifiesRest generalRest
  | n + 1, (.app f ss, .var y) :: rest, θ, h => by
      simp only [unify] at h
      split_ifs at h with occurs
      obtain ⟨θ', inner, rfl⟩ := UnifyResult.compose_ok h
      obtain ⟨unifiesRest, generalRest⟩ := unify_ok_unifies n _ θ' inner
      obtain ⟨unifies, general⟩ := elim_ok occurs unifiesRest generalRest
      exact ⟨unifies_swap_head.mpr unifies,
        fun ρ unified => general ρ (unifies_swap_head.mp unified)⟩
  | n + 1, (.app f ss, .app g ts) :: rest, θ, h => by
      simp only [unify] at h
      split_ifs at h with heads
      obtain ⟨rfl, lengths⟩ := heads
      obtain ⟨unifiesAll, generalAll⟩ := unify_ok_unifies n _ θ h
      rw [unifies_append] at unifiesAll
      refine ⟨unifies_cons.mpr ⟨(unifies_app_iff θ).mpr ⟨rfl, lengths, unifiesAll.1⟩,
        unifiesAll.2⟩, fun ρ unified => generalAll ρ ?_⟩
      rw [unifies_cons, unifies_app_iff] at unified
      exact unifies_append.mpr ⟨unified.1.2.2, unified.2⟩

/-- **`ok` gives a unifier.** -/
theorem unify_ok_unify {n : ℕ} {E : List (Term F X × Term F X)} {θ : X → Term F X}
    (h : unify n E = .ok θ) : Unifies θ E :=
  (unify_ok_unifies.{u, v, 0} n E θ h).1

/-- **`ok` gives a most general unifier**: every unifier factors through it, by itself. -/
theorem unify_ok_general {n : ℕ} {E : List (Term F X × Term F X)} {θ : X → Term F X}
    (h : unify n E = .ok θ) {W : Type w} (ρ : X → Term F W) (unified : Unifies ρ E) (y : X) :
    (θ y).subst ρ = ρ y :=
  (unify_ok_unifies n E θ h).2 ρ unified y

/-- **`fail` means that no substitution unifies the equations.** -/
theorem unify_fail : ∀ (n : ℕ) (E : List (Term F X × Term F X)), unify n E = .fail →
    ∀ {W : Type w} (ρ : X → Term F W), ¬ Unifies ρ E
  | 0, E, h => by simp [unify] at h
  | n + 1, [], h => by simp [unify] at h
  | n + 1, (.var x, t) :: rest, h => by
      intro ρ unified
      simp only [unify] at h
      split_ifs at h with same occurs
      · exact unify_fail n rest h ρ (unifies_cons.mp unified).2
      · exact occurs_not_unifiable same occurs ρ (by simpa using (unifies_cons.mp unified).1)
      · have inner := UnifyResult.compose_fail h
        obtain ⟨agree, unifiedRest⟩ := unifies_cons.mp unified
        exact unify_fail n _ inner ρ (unifies_substEqs (by simpa using agree) unifiedRest)
  | n + 1, (.app f ss, .var y) :: rest, h => by
      intro ρ unified
      simp only [unify] at h
      obtain ⟨agree, unifiedRest⟩ := unifies_cons.mp (unifies_swap_head.mp unified)
      split_ifs at h with occurs
      · exact occurs_not_unifiable (by simp) occurs ρ (by simpa using agree)
      · have inner := UnifyResult.compose_fail h
        exact unify_fail n _ inner ρ (unifies_substEqs (by simpa using agree) unifiedRest)
  | n + 1, (.app f ss, .app g ts) :: rest, h => by
      intro ρ unified
      simp only [unify] at h
      obtain ⟨heads, unifiedRest⟩ := unifies_cons.mp unified
      obtain ⟨sameHead, lengths, zipped⟩ := (unifies_app_iff ρ).mp heads
      split_ifs at h with test
      · exact unify_fail n _ h ρ (unifies_append.mpr ⟨zipped, unifiedRest⟩)
      · exact test ⟨sameHead, lengths⟩

theorem unify_mono : ∀ (n : ℕ) (E : List (Term F X × Term F X)) (m : ℕ), n ≤ m →
    unify n E ≠ .outOfFuel → unify m E = unify n E
  | 0, E, m, _, h => by simp [unify] at h
  | n + 1, E, 0, le, _ => by omega
  | n + 1, [], m + 1, _, _ => by simp [unify]
  | n + 1, (.var x, t) :: rest, m + 1, le, h => by
      simp only [unify] at h ⊢
      split_ifs at h ⊢ with same occurs
      · exact unify_mono n rest m (by omega) h
      · rfl
      · rw [unify_mono n _ m (by omega) (UnifyResult.compose_ne_outOfFuel h)]
  | n + 1, (.app f ss, .var y) :: rest, m + 1, le, h => by
      simp only [unify] at h ⊢
      split_ifs at h ⊢ with occurs
      · rfl
      · rw [unify_mono n _ m (by omega) (UnifyResult.compose_ne_outOfFuel h)]
  | n + 1, (.app f ss, .app g ts) :: rest, m + 1, le, h => by
      simp only [unify] at h ⊢
      split_ifs at h ⊢ with heads
      · exact unify_mono n _ m (by omega) h
      · rfl

/-- **Some fuel decides every unification problem.** -/
theorem unify_terminates (E : List (Term F X × Term F X)) : ∃ n, unify n E ≠ .outOfFuel := by
  induction h : unifyMeasure E using WellFoundedLT.induction generalizing E with
  | _ m ih =>
  subst h
  match E with
  | [] => exact ⟨1, by simp [unify]⟩
  | (.var x, t) :: rest =>
      by_cases same : t = .var x
      · obtain ⟨n, hn⟩ := ih (unifyMeasure rest) (measure_lt_of_le_lt
          (fun z hz => by rw [eqVars_cons]; simp [hz])
          (by rw [eqSize_cons]; have := t.size_pos; omega)) rest rfl
        exact ⟨n + 1, by simpa [unify, same] using hn⟩
      · by_cases occurs : x ∈ t.vars
        · exact ⟨1, by simp [unify, same, occurs]⟩
        · obtain ⟨n, hn⟩ := ih _ (measure_lt_of_elim (rest := rest) occurs
            (by rw [eqVars_cons]; simp)
            (fun z hz => by rw [eqVars_cons]; simp [hz])
            (fun z hz => by rw [eqVars_cons]; simp [hz])) _ rfl
          refine ⟨n + 1, ?_⟩
          simp only [unify, same, occurs, if_false]
          exact UnifyResult.compose_ne_outOfFuel_of hn
  | (.app f ss, .var y) :: rest =>
      by_cases occurs : y ∈ (Term.app f ss).vars
      · exact ⟨1, by simp only [unify, occurs, if_true]; exact fun h => by cases h⟩
      · obtain ⟨n, hn⟩ := ih _ (measure_lt_of_elim (rest := rest) occurs
          (by rw [eqVars_cons]; simp)
          (fun z hz => by rw [eqVars_cons]; simp [hz])
          (fun z hz => by rw [eqVars_cons]; simp only [List.mem_append]; exact Or.inl (Or.inl hz)))
          _ rfl
        refine ⟨n + 1, ?_⟩
        simp only [unify, occurs, if_false]
        exact UnifyResult.compose_ne_outOfFuel_of hn
  | (.app f ss, .app g ts) :: rest =>
      by_cases heads : f = g ∧ ss.length = ts.length
      · obtain ⟨n, hn⟩ := ih _ (measure_lt_of_le_lt (E' := ss.zip ts ++ rest)
          (fun z hz => by
            rw [eqVars_append, List.mem_append, eqVars_zip ss ts heads.2] at hz
            rw [eqVars_cons]
            simp only [vars_app, List.mem_append]
            tauto)
          (by
            rw [eqSize_append, eqSize_zip ss ts heads.2, eqSize_cons]
            simp only [size_app]
            omega)) _ rfl
        exact ⟨n + 1, by simpa [unify, heads] using hn⟩
      · exact ⟨1, by simp only [unify, heads, if_false]; exact fun h => by cases h⟩

/-- A unification problem has a decided answer at every large enough fuel. -/
theorem unify_eventually (E : List (Term F X × Term F X)) :
    ∃ n, ∀ m, n ≤ m → unify m E = unify n E ∧ unify n E ≠ .outOfFuel := by
  obtain ⟨n, hn⟩ := unify_terminates E
  exact ⟨n, fun m le => ⟨unify_mono n E m le hn, hn⟩⟩

end Mettapedia.TypeTheory.PromotionAdmission
