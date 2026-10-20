import Mettapedia.Logic.HOL.Semantics.BethHenkin
import Mettapedia.Logic.HOL.Semantics.HenkinWitnessService

/-!
# Beth completeness on the tree of fair Henkin runs

The covering-system Beth completeness of `BethHenkin` goes through the
Lindenbaum algebra and needs no enumeration.  This file proves completeness for
Beth structures in Beth's own form, trees with bars, and there the schedules
of a Henkin construction become essential.

## The tree of Henkin runs

Fix a parameter-free theory `T` and schedules `S` of disjunction pairs and
existential bodies.  A node is a finite list of moves; a move is an
assumption, a disjunct choice and a witness offset.  The step at depth `n`

1. assumes the move's formula, unless that makes the theory inconsistent
   (`assumeStep`);
2. serves the scheduled pair `S.pair n`: if the theory proves its disjunction,
   it adds the chosen disjunct, or the other one when the choice is
   inconsistent (`decideStep`);
3. serves the scheduled body `S.body n`: if the theory proves its existential,
   it adds an instance at a parameter fresh for the theory and the body,
   shifted by the offset (`witnessStep`).

The node theory `theory T S s` is `T` together with everything added along
`s`.  A node forces a formula when its theory proves it (`model`).

## Where the schedule enters

Every node theory is consistent, and an unprovable formula stays unprovable at
some child (`exists_child_not_provable`); so a formula proved on a bar is
proved at its root (`provable_of_bar`), by following a path of unprovability.
That gives the cover clauses in one direction.  In the other direction,
`theory s ⊢ φ ∨ ψ` must be decided on a bar above `s`.  The nodes past a depth
serving `(φ, ψ)` form a bar exactly when `(φ, ψ)` is served infinitely often
(`Bar.infinitelyOften_iff_isBar`); so the disjunction clause holds when the
pair schedule is fair (`provable_or_iff_bar`), and so does the existential
clause when the body schedule is fair (`provable_ex_iff_bar`).

## Results

* `model`: the canonical tree Beth structure of fair schedules, with worlds
  `List (Move Const)`, prefix order and bars as covers.
* `provable_of_treeBethConsequence`: completeness for tree Beth structures from
  any fair pair and body schedules; `…_of_services` takes the schedules from
  services with constantly true eligibility.
* `provable_iff_treeBethConsequence_of_countable`: soundness and completeness
  for countable signatures, through enumerations.
* `BethTreeControls` holds the negative control: with a starving schedule the
  disjunction clause fails.  `TermEnumeration` makes the schedules computable
  for encodable signatures.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

namespace BethTree

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams ClosedTheorySet BethHenkin

/-! ## Parameter support and theories extended by lists -/

/-- A strict bound on the parameter indices occurring in a list of formulas. -/
def supp : List (ClosedFormula (WithParams Const)) → ℕ
  | [] => 0
  | φ :: A => max (maxParam φ) (supp A)

theorem noConstOccurrence_of_supp_le {A : List (ClosedFormula (WithParams Const))} {k : ℕ}
    (hk : supp A ≤ k) {σ : Ty Base} :
    ∀ φ ∈ A, NoConstOccurrence (param σ k : WithParams Const σ) φ := by
  induction A with
  | nil => intro φ hφ; cases hφ
  | cons ψ A ih =>
      intro φ hφ
      have hψ : maxParam ψ ≤ k := le_trans (le_max_left _ _) hk
      have hA : supp A ≤ k := le_trans (le_max_right _ _) hk
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact noConstOccurrence_param_of_ge k φ hψ
      · exact ih hA φ hφ

/-- A theory has no parameters. -/
def ParamFree (T : ClosedTheorySet (WithParams Const)) : Prop :=
  ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : ℕ), NoConstOccurrence (param σ k : WithParams Const σ) ψ

/-- `T` extended by the formulas of a list. -/
def withList (T : ClosedTheorySet (WithParams Const))
    (A : List (ClosedFormula (WithParams Const))) : ClosedTheorySet (WithParams Const) :=
  T ∪ {φ | φ ∈ A}

theorem withList_cons (T : ClosedTheorySet (WithParams Const))
    (φ : ClosedFormula (WithParams Const)) (A : List (ClosedFormula (WithParams Const))) :
    withList T (φ :: A) = insert φ (withList T A) := by
  ext ψ
  simp only [withList, Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, Set.mem_insert_iff]
  tauto

theorem withList_nil (T : ClosedTheorySet (WithParams Const)) : withList T [] = T := by
  ext ψ
  simp [withList]

theorem withList_mono (T : ClosedTheorySet (WithParams Const))
    {A A' : List (ClosedFormula (WithParams Const))} (h : ∀ φ ∈ A, φ ∈ A') :
    ∀ {φ}, φ ∈ withList T A → φ ∈ withList T A' := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact Or.inl hφ
  · exact Or.inr (h φ hφ)

theorem fresh_withList {T : ClosedTheorySet (WithParams Const)} (hT : ParamFree T)
    {A : List (ClosedFormula (WithParams Const))} {k : ℕ} (hk : supp A ≤ k) {σ : Ty Base} :
    ∀ ψ ∈ withList T A, NoConstOccurrence (param σ k : WithParams Const σ) ψ := by
  intro ψ hψ
  rcases hψ with hψ | hψ
  · exact hT ψ hψ σ k
  · exact noConstOccurrence_of_supp_le hk ψ hψ

/-! ## Small facts about provability -/

section Provability

variable {Γ : ClosedTheorySet (WithParams Const)}

theorem provable_of_bot {χ : ClosedFormula (WithParams Const)}
    (h : Provable (Const := WithParams Const) Γ .bot) : Provable (Const := WithParams Const) Γ χ := by
  rcases h with ⟨Δ, hΔ, d⟩
  exact ⟨Δ, hΔ, ExtDerivation.botE d⟩

/-- Adding `⊤` proves nothing new. -/
theorem not_provable_insert_top {χ : ClosedFormula (WithParams Const)}
    (h : ¬ Provable (Const := WithParams Const) Γ χ) :
    ¬ Provable (Const := WithParams Const) (insert .top Γ) χ := fun hχ =>
  h (provable_mp (provable_imp_of_insert hχ) (provable_top Γ))

/-- A theory that omits some formula is consistent. -/
theorem consistent_of_not_provable {χ : ClosedFormula (WithParams Const)}
    (h : ¬ Provable (Const := WithParams Const) Γ χ) : Consistent (Const := WithParams Const) Γ :=
  fun hbot => h (provable_of_bot hbot)

/-- Negation introduction: if `φ` makes `Γ` inconsistent, `Γ` proves `¬φ`. -/
theorem provable_not_of_insert_bot {φ : ClosedFormula (WithParams Const)}
    (h : Provable (Const := WithParams Const) (insert φ Γ) .bot) :
    Provable (Const := WithParams Const) Γ (.not φ) := by
  obtain ⟨Δ, hΔ, d⟩ := provable_imp_of_insert h
  refine ⟨Δ, hΔ, ExtDerivation.notI (ExtDerivation.impE (ExtDerivation.mono ?_ d)
    (ExtDerivation.hyp List.mem_cons_self))⟩
  intro ξ hξ
  exact List.mem_cons_of_mem _ hξ

theorem consistent_insert_top (h : Consistent (Const := WithParams Const) Γ) :
    Consistent (Const := WithParams Const) (insert .top Γ) :=
  not_provable_insert_top h

end Provability

/-! ## The steps of a Henkin run -/

/-- A move: an assumption, a disjunct choice and a witness offset. -/
abbrev Move (Const : Ty Base → Type v) := ClosedFormula (WithParams Const) × Bool × ℕ

instance : Inhabited (Move Const) := ⟨(.top, false, 0)⟩

/-- Schedules of disjunction pairs and existential bodies. -/
structure Schedules (Const : Ty Base → Type v) where
  pair : ℕ → ClosedFormulaPair Const
  body : ℕ → Body Const

/-- The disjunct selected by a choice bit. -/
def pick (b : Bool) (p : ClosedFormulaPair Const) : ClosedFormula (WithParams Const) :=
  if b then p.1 else p.2

theorem pick_eq (b : Bool) (p : ClosedFormulaPair Const) : pick b p = p.1 ∨ pick b p = p.2 := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The witness parameter for a body and an offset: fresh for the list and the
body. -/
def witnessParam (A : List (ClosedFormula (WithParams Const))) (bd : Body Const) (k : ℕ) :
    WithParams Const bd.1 :=
  param bd.1 (max (supp A) (maxParam bd.2) + k)

variable (T : ClosedTheorySet (WithParams Const))

open Classical in
/-- Assume a formula unless it is inconsistent with the current theory. -/
noncomputable def assumeStep (A : List (ClosedFormula (WithParams Const)))
    (α : ClosedFormula (WithParams Const)) : List (ClosedFormula (WithParams Const)) :=
  (if Consistent (Const := WithParams Const) (insert α (withList T A)) then α else .top) :: A

open Classical in
/-- Serve a disjunction pair: when the theory proves its disjunction, add the
chosen disjunct, or the other one when the choice is inconsistent. -/
noncomputable def decideStep (p : ClosedFormulaPair Const) (b : Bool)
    (A : List (ClosedFormula (WithParams Const))) : List (ClosedFormula (WithParams Const)) :=
  (if Provable (Const := WithParams Const) (withList T A) (.or p.1 p.2) then
    (if Consistent (Const := WithParams Const) (insert (pick b p) (withList T A)) then pick b p
      else pick (!b) p)
  else .top) :: A

open Classical in
/-- Serve an existential body: when the theory proves the existential, add an
instance at a fresh parameter. -/
noncomputable def witnessStep (bd : Body Const) (k : ℕ)
    (A : List (ClosedFormula (WithParams Const))) : List (ClosedFormula (WithParams Const)) :=
  (if Provable (Const := WithParams Const) (withList T A) (.ex bd.2) then
    instantiate (Base := Base) (.const (witnessParam A bd k)) bd.2
  else .top) :: A

/-- One step at depth `n`. -/
noncomputable def step (S : Schedules Const) (n : ℕ) (A : List (ClosedFormula (WithParams Const)))
    (m : Move Const) : List (ClosedFormula (WithParams Const)) :=
  witnessStep T (S.body n) m.2.2 (decideStep T (S.pair n) m.2.1 (assumeStep T A m.1))

/-- Run a list of moves from depth `n`. -/
noncomputable def runFrom (S : Schedules Const) :
    ℕ → List (ClosedFormula (WithParams Const)) → List (Move Const) →
      List (ClosedFormula (WithParams Const))
  | _, A, [] => A
  | n, A, m :: ms => runFrom S (n + 1) (step T S n A m) ms

/-- The formulas added along a node. -/
noncomputable def added (S : Schedules Const) (s : List (Move Const)) :
    List (ClosedFormula (WithParams Const)) :=
  runFrom T S 0 [] s

/-- The theory of a node. -/
noncomputable def theory (S : Schedules Const) (s : List (Move Const)) :
    ClosedTheorySet (WithParams Const) :=
  withList T (added T S s)

variable {T}

theorem runFrom_append (S : Schedules Const) :
    ∀ (s t : List (Move Const)) (n : ℕ) (A : List (ClosedFormula (WithParams Const))),
      runFrom T S n A (s ++ t) = runFrom T S (n + s.length) (runFrom T S n A s) t
  | [], t, n, A => by simp [runFrom]
  | m :: s, t, n, A => by
      simp only [List.cons_append, runFrom, List.length_cons]
      rw [runFrom_append S s t (n + 1) (step T S n A m)]
      congr 1
      omega

theorem added_append_singleton (S : Schedules Const) (s : List (Move Const)) (m : Move Const) :
    added T S (s ++ [m]) = step T S s.length (added T S s) m := by
  unfold added
  rw [runFrom_append, Nat.zero_add]
  rfl

theorem subset_step (S : Schedules Const) (n : ℕ) (A : List (ClosedFormula (WithParams Const)))
    (m : Move Const) : ∀ φ ∈ A, φ ∈ step T S n A m := by
  intro φ hφ
  unfold step witnessStep decideStep assumeStep
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hφ))

theorem subset_runFrom (S : Schedules Const) :
    ∀ (s : List (Move Const)) (n : ℕ) (A : List (ClosedFormula (WithParams Const))),
      ∀ φ ∈ A, φ ∈ runFrom T S n A s
  | [], _, _ => fun _ h => h
  | m :: s, n, A => fun φ h =>
      subset_runFrom S s (n + 1) (step T S n A m) φ (subset_step S n A m φ h)

theorem theory_mono (S : Schedules Const) {s t : List (Move Const)} (h : s <+: t) :
    ∀ {φ}, φ ∈ theory T S s → φ ∈ theory T S t := by
  obtain ⟨u, rfl⟩ := h
  apply withList_mono
  intro φ hφ
  unfold added
  rw [runFrom_append]
  exact subset_runFrom S u _ _ φ hφ

theorem theory_nil (S : Schedules Const) : theory T S [] = T := withList_nil T

/-! ## Consistency is preserved -/

section Consistency

variable {A : List (ClosedFormula (WithParams Const))}

theorem consistent_assumeStep (h : Consistent (Const := WithParams Const) (withList T A))
    (α : ClosedFormula (WithParams Const)) :
    Consistent (Const := WithParams Const) (withList T (assumeStep T A α)) := by
  classical
  unfold assumeStep
  rw [withList_cons]
  split_ifs with hα
  · exact hα
  · exact consistent_insert_top h

theorem consistent_decideStep (h : Consistent (Const := WithParams Const) (withList T A))
    (p : ClosedFormulaPair Const) (b : Bool) :
    Consistent (Const := WithParams Const) (withList T (decideStep T p b A)) := by
  classical
  unfold decideStep
  rw [withList_cons]
  split_ifs with hOr hb
  · exact hb
  · rcases exists_or_branch_omitting (Const := WithParams Const) h hOr with h1 | h2
    · cases b
      · exact h1
      · exact absurd h1 hb
    · cases b
      · exact absurd h2 hb
      · exact h2
  · exact consistent_insert_top h

theorem consistent_witnessStep (hT : ParamFree T)
    (h : Consistent (Const := WithParams Const) (withList T A)) (bd : Body Const) (k : ℕ) :
    Consistent (Const := WithParams Const) (withList T (witnessStep T bd k A)) := by
  classical
  unfold witnessStep
  rw [withList_cons]
  split_ifs with hEx
  · exact not_provable_insert_fresh_instance_of_ex_provable (Const := WithParams Const)
      (witnessParam A bd k) h hEx
      (fresh_withList hT (le_trans (le_max_left _ _) (Nat.le_add_right _ _)))
      (noConstOccurrence_param_of_ge _ _ (le_trans (le_max_right _ _) (Nat.le_add_right _ _)))
      .bot
  · exact consistent_insert_top h

theorem consistent_step (hT : ParamFree T) (S : Schedules Const) (n : ℕ)
    (h : Consistent (Const := WithParams Const) (withList T A)) (m : Move Const) :
    Consistent (Const := WithParams Const) (withList T (step T S n A m)) :=
  consistent_witnessStep hT (consistent_decideStep (consistent_assumeStep h m.1) _ _) _ _

theorem consistent_runFrom (hT : ParamFree T) (S : Schedules Const) :
    ∀ (s : List (Move Const)) (n : ℕ) (A : List (ClosedFormula (WithParams Const))),
      Consistent (Const := WithParams Const) (withList T A) →
        Consistent (Const := WithParams Const) (withList T (runFrom T S n A s))
  | [], _, _, h => h
  | m :: s, n, _, h => consistent_runFrom hT S s (n + 1) _ (consistent_step hT S n h m)

/-- **Every node theory is consistent** when `T` is. -/
theorem consistent_theory (hT : ParamFree T) (hCons : Consistent (Const := WithParams Const) T)
    (S : Schedules Const) (s : List (Move Const)) :
    Consistent (Const := WithParams Const) (theory T S s) :=
  consistent_runFrom hT S s 0 [] (by rw [withList_nil]; exact hCons)

end Consistency

/-! ## Unprovability survives at some child -/

section OneStep

variable {A : List (ClosedFormula (WithParams Const))} {χ : ClosedFormula (WithParams Const)}

/-- After the assumption, some disjunct choice and witness offset keep `χ`
unprovable. -/
theorem exists_child_not_provable_of_assume (hT : ParamFree T) (S : Schedules Const) (n : ℕ)
    (α : ClosedFormula (WithParams Const))
    (h : ¬ Provable (Const := WithParams Const) (withList T (assumeStep T A α)) χ) :
    ∃ (b : Bool) (k : ℕ),
      ¬ Provable (Const := WithParams Const) (withList T (step T S n A (α, b, k))) χ := by
  classical
  set A₁ := assumeStep T A α
  -- the decision
  have hDecide : ∃ b : Bool,
      ¬ Provable (Const := WithParams Const) (withList T (decideStep T (S.pair n) b A₁)) χ := by
    by_cases hOr : Provable (Const := WithParams Const) (withList T A₁)
        (.or (S.pair n).1 (S.pair n).2)
    · rcases exists_or_branch_omitting (Const := WithParams Const) h hOr with h1 | h2
      · refine ⟨true, ?_⟩
        unfold decideStep
        rw [withList_cons, if_pos hOr]
        have hc : Consistent (Const := WithParams Const)
            (insert (pick true (S.pair n)) (withList T A₁)) := consistent_of_not_provable h1
        rw [if_pos hc]
        exact h1
      · refine ⟨false, ?_⟩
        unfold decideStep
        rw [withList_cons, if_pos hOr]
        have hc : Consistent (Const := WithParams Const)
            (insert (pick false (S.pair n)) (withList T A₁)) := consistent_of_not_provable h2
        rw [if_pos hc]
        exact h2
    · refine ⟨false, ?_⟩
      unfold decideStep
      rw [withList_cons, if_neg hOr]
      exact not_provable_insert_top h
  obtain ⟨b, hb⟩ := hDecide
  set A₂ := decideStep T (S.pair n) b A₁
  refine ⟨b, maxParam χ, ?_⟩
  show ¬ Provable (Const := WithParams Const)
    (withList T (witnessStep T (S.body n) (maxParam χ) A₂)) χ
  unfold witnessStep
  rw [withList_cons]
  split_ifs with hEx
  · exact not_provable_insert_fresh_instance_of_ex_provable (Const := WithParams Const)
      (witnessParam A₂ (S.body n) (maxParam χ)) hb hEx
      (fresh_withList hT (le_trans (le_max_left _ _) (Nat.le_add_right _ _)))
      (noConstOccurrence_param_of_ge _ _ (le_trans (le_max_right _ _) (Nat.le_add_right _ _)))
      (noConstOccurrence_param_of_ge _ _ (Nat.le_add_left _ _))
  · exact not_provable_insert_top hb

/-- **One step of unprovability**: if `χ` is unprovable at a node, it is
unprovable at some child. -/
theorem exists_child_not_provable (hT : ParamFree T) (S : Schedules Const) (n : ℕ)
    (h : ¬ Provable (Const := WithParams Const) (withList T A) χ) :
    ∃ m : Move Const, ¬ Provable (Const := WithParams Const) (withList T (step T S n A m)) χ := by
  classical
  have h₁ : ¬ Provable (Const := WithParams Const) (withList T (assumeStep T A .top)) χ := by
    unfold assumeStep
    rw [withList_cons]
    split_ifs <;> exact not_provable_insert_top h
  obtain ⟨b, k, hbk⟩ := exists_child_not_provable_of_assume hT S n .top h₁
  exact ⟨(.top, b, k), hbk⟩

end OneStep

/-! ## A formula proved on a bar is proved at its root -/

section Bars

variable (S : Schedules Const) (χ : ClosedFormula (WithParams Const))

open Classical in
/-- A chain of nodes above `s` whose theories all omit `χ`, each a one-move
extension of the previous one. -/
noncomputable def omitChain (hT : ParamFree T) (s : List (Move Const))
    (hs : ¬ Provable (Const := WithParams Const) (theory T S s) χ) :
    ℕ → {t : List (Move Const) // ¬ Provable (Const := WithParams Const) (theory T S t) χ}
  | 0 => ⟨s, hs⟩
  | i + 1 =>
      have hex := exists_child_not_provable hT S (omitChain hT s hs i).1.length
        (A := added T S (omitChain hT s hs i).1) (omitChain hT s hs i).2
      ⟨(omitChain hT s hs i).1 ++ [Classical.choose hex], by
        show ¬ Provable (Const := WithParams Const)
          (withList T (added T S ((omitChain hT s hs i).1 ++ [Classical.choose hex]))) χ
        rw [added_append_singleton]
        exact Classical.choose_spec hex⟩

variable {S χ}

theorem omitChain_length {hT : ParamFree T} {s : List (Move Const)}
    {hs : ¬ Provable (Const := WithParams Const) (theory T S s) χ} :
    ∀ i, (omitChain S χ hT s hs i).1.length = s.length + i
  | 0 => rfl
  | i + 1 => by
      have ih := omitChain_length (hT := hT) (hs := hs) i
      show ((omitChain S χ hT s hs i).1 ++ _).length = _
      simp only [List.length_append, List.length_singleton]
      omega

theorem omitChain_prefix {hT : ParamFree T} {s : List (Move Const)}
    {hs : ¬ Provable (Const := WithParams Const) (theory T S s) χ} {i : ℕ} :
    ∀ {j}, i ≤ j → (omitChain S χ hT s hs i).1 <+: (omitChain S χ hT s hs j).1
  | 0, h => by
      rw [Nat.le_zero.mp h]
  | j + 1, h => by
      rcases Nat.lt_or_ge i (j + 1) with hij | hij
      · exact (omitChain_prefix (Nat.le_of_lt_succ hij)).trans (List.prefix_append _ _)
      · rw [Nat.le_antisymm h hij]

variable (S χ)

/-- **Local character on bars**: a formula proved at every node of a bar of `s`
is proved at `s`.  Otherwise a chain of children omitting it gives a path that
meets the bar at an omitting node. -/
theorem provable_of_bar (hT : ParamFree T) {s : List (Move Const)} {B : Set (List (Move Const))}
    (hB : Bar.IsBar s B) (h : ∀ t ∈ B, Provable (Const := WithParams Const) (theory T S t) χ) :
    Provable (Const := WithParams Const) (theory T S s) χ := by
  classical
  by_contra hs
  let c := omitChain S χ hT s hs
  have hlen : ∀ i, (c i).1.length = s.length + i := omitChain_length
  let p : ℕ → Move Const := fun j => (c (j + 1)).1[j]'(by rw [hlen]; omega)
  have hthrough : ∀ i, Bar.Through p (c i).1 := by
    intro i j hj
    have hj' : j < (c (j + 1)).1.length := by rw [hlen]; omega
    have h₁ : (c i).1[j] = (c (max i (j + 1))).1[j]'(by
        rw [hlen]; rw [hlen] at hj; omega) :=
      (omitChain_prefix (le_max_left i (j + 1))).getElem hj
    have h₂ : (c (j + 1)).1[j] = (c (max i (j + 1))).1[j]'(by
        rw [hlen]; rw [hlen] at hj'; omega) :=
      (omitChain_prefix (le_max_right i (j + 1))).getElem hj'
    rw [h₁, ← h₂]
  obtain ⟨t, htB, hpt⟩ := hB.2 p (hthrough 0)
  have hst : s <+: t := hB.1 t htB
  have hle : s.length ≤ t.length := hst.length_le
  have ht_eq : t = (c (t.length - s.length)).1 := by
    have hpre : t <+: (c (t.length - s.length)).1 :=
      Bar.prefix_of_through hpt (hthrough _) (by rw [hlen]; omega)
    exact hpre.eq_of_length (by rw [hlen]; omega)
  exact (c (t.length - s.length)).2 (ht_eq ▸ h t htB)

end Bars

/-! ## The cover clauses -/

section Clauses

variable (S : Schedules Const)

/-- The nodes above `s` past a depth that serves the pair `p`. -/
def pairBar (s : List (Move Const)) (p : ClosedFormulaPair Const) : Set (List (Move Const)) :=
  {t | s <+: t ∧ ∃ n, s.length ≤ n ∧ n < t.length ∧ S.pair n = p}

/-- The nodes above `s` past a depth that serves the body `bd`. -/
def bodyBar (s : List (Move Const)) (bd : Body Const) : Set (List (Move Const)) :=
  {t | s <+: t ∧ ∃ n, s.length ≤ n ∧ n < t.length ∧ S.body n = bd}

/-- **The bar property from liveness**: when the pair schedule serves `p`
infinitely often, the nodes past a serving depth bar every node. -/
theorem isBar_pairBar {p : ClosedFormulaPair Const} (hLive : ∀ N, ∃ n, N ≤ n ∧ S.pair n = p)
    (s : List (Move Const)) : Bar.IsBar s (pairBar S s p) :=
  (Bar.infinitelyOften_iff_isBar S.pair p).mp hLive s

theorem isBar_bodyBar {bd : Body Const} (hLive : ∀ N, ∃ n, N ≤ n ∧ S.body n = bd)
    (s : List (Move Const)) : Bar.IsBar s (bodyBar S s bd) :=
  (Bar.infinitelyOften_iff_isBar S.body bd).mp hLive s

/-- A node `t` above `s` splits at depth `n` with `|s| ≤ n < |t|`: its prefix of
length `n` extends `s`, and one more move stays below `t`. -/
theorem split_at {s t : List (Move Const)} (hst : s <+: t) {n : ℕ} (hsn : s.length ≤ n)
    (hnt : n < t.length) :
    s <+: t.take n ∧ (t.take n).length = n ∧ t.take n ++ [t[n]] <+: t := by
  refine ⟨?_, by simp; omega, ?_⟩
  · rw [List.prefix_iff_eq_take] at hst ⊢
    rw [List.take_take, Nat.min_eq_left hsn]
    exact hst
  · rw [← List.take_succ_eq_append_getElem hnt]
    exact List.take_prefix _ _

theorem mem_step_of_assume {n : ℕ} {A : List (ClosedFormula (WithParams Const))}
    {m : Move Const} {φ : ClosedFormula (WithParams Const)}
    (h : φ ∈ assumeStep T A m.1) : φ ∈ step T S n A m := by
  unfold step witnessStep decideStep
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem mem_step_of_decide {n : ℕ} {A : List (ClosedFormula (WithParams Const))}
    {m : Move Const} {φ : ClosedFormula (WithParams Const)}
    (h : φ ∈ decideStep T (S.pair n) m.2.1 (assumeStep T A m.1)) : φ ∈ step T S n A m := by
  unfold step witnessStep
  exact List.mem_cons_of_mem _ h

theorem subset_assumeStep (A : List (ClosedFormula (WithParams Const)))
    (α : ClosedFormula (WithParams Const)) : ∀ φ ∈ A, φ ∈ assumeStep T A α :=
  fun _ h => List.mem_cons_of_mem _ h

theorem subset_decideStep (p : ClosedFormulaPair Const) (b : Bool)
    (A : List (ClosedFormula (WithParams Const))) : ∀ φ ∈ A, φ ∈ decideStep T p b A :=
  fun _ h => List.mem_cons_of_mem _ h

/-- A served pair whose disjunction is provable is decided. -/
theorem decideStep_decides {p : ClosedFormulaPair Const} {b : Bool}
    {A : List (ClosedFormula (WithParams Const))}
    (hOr : Provable (Const := WithParams Const) (withList T A) (.or p.1 p.2)) :
    p.1 ∈ decideStep T p b A ∨ p.2 ∈ decideStep T p b A := by
  classical
  unfold decideStep
  rw [if_pos hOr]
  split_ifs
  · rcases pick_eq b p with h | h
    · exact Or.inl (h ▸ List.mem_cons_self)
    · exact Or.inr (h ▸ List.mem_cons_self)
  · rcases pick_eq (!b) p with h | h
    · exact Or.inl (h ▸ List.mem_cons_self)
    · exact Or.inr (h ▸ List.mem_cons_self)

/-- A served body whose existential is provable is witnessed. -/
theorem witnessStep_witnesses {bd : Body Const} {k : ℕ}
    {A : List (ClosedFormula (WithParams Const))}
    (hEx : Provable (Const := WithParams Const) (withList T A) (.ex bd.2)) :
    instantiate (Base := Base) (.const (witnessParam A bd k)) bd.2 ∈ witnessStep T bd k A := by
  classical
  unfold witnessStep
  rw [if_pos hEx]
  exact List.mem_cons_self

/-- On the bar of a served pair, a provable disjunction is decided. -/
theorem provable_disjunct_of_mem_pairBar {s t : List (Move Const)}
    {φ ψ : ClosedFormula (WithParams Const)}
    (hOr : Provable (Const := WithParams Const) (theory T S s) (.or φ ψ))
    (ht : t ∈ pairBar S s (φ, ψ)) :
    Provable (Const := WithParams Const) (theory T S t) φ ∨
      Provable (Const := WithParams Const) (theory T S t) ψ := by
  obtain ⟨hst, n, hsn, hnt, hp⟩ := ht
  obtain ⟨hsu, hulen, hut⟩ := split_at hst hsn hnt
  set u := t.take n
  set m := t[n]
  have hadded : added T S (u ++ [m]) = step T S n (added T S u) m := by
    rw [added_append_singleton, hulen]
  have hOr₁ : Provable (Const := WithParams Const)
      (withList T (assumeStep T (added T S u) m.1)) (.or (S.pair n).1 (S.pair n).2) := by
    rw [hp]
    exact provable_mono (fun hφ => withList_mono T (subset_assumeStep (added T S u) m.1) hφ)
      (provable_mono (theory_mono S hsu) hOr)
  have hmem := decideStep_decides (b := m.2.1) hOr₁
  rw [hp] at hmem
  rcases hmem with h | h
  · left
    refine provable_mono (theory_mono S hut) (provable_of_mem ?_)
    show φ ∈ withList T (added T S (u ++ [m]))
    rw [hadded]
    exact Or.inr (mem_step_of_decide S (hp ▸ h))
  · right
    refine provable_mono (theory_mono S hut) (provable_of_mem ?_)
    show ψ ∈ withList T (added T S (u ++ [m]))
    rw [hadded]
    exact Or.inr (mem_step_of_decide S (hp ▸ h))

/-- On the bar of a served body, a provable existential is witnessed. -/
theorem exists_instance_of_mem_bodyBar {s t : List (Move Const)} {σ : Ty Base}
    {φ : Formula (WithParams Const) [σ]}
    (hEx : Provable (Const := WithParams Const) (theory T S s) (.ex φ))
    (ht : t ∈ bodyBar S s ⟨σ, φ⟩) :
    ∃ r : ClosedTerm (WithParams Const) σ,
      Provable (Const := WithParams Const) (theory T S t) (instantiate (Base := Base) r φ) := by
  obtain ⟨hst, n, hsn, hnt, hb⟩ := ht
  obtain ⟨hsu, hulen, hut⟩ := split_at hst hsn hnt
  set u := t.take n
  set m := t[n]
  set A₂ := decideStep T (S.pair n) m.2.1 (assumeStep T (added T S u) m.1)
  have hadded : added T S (u ++ [m]) = witnessStep T (S.body n) m.2.2 A₂ := by
    rw [added_append_singleton, hulen]
    rfl
  have hsub : ∀ {χ}, χ ∈ theory T S u → χ ∈ withList T A₂ := fun hχ =>
    withList_mono T (fun χ hχ => subset_decideStep _ _ _ χ (subset_assumeStep _ _ χ hχ)) hχ
  have hEx₂ : Provable (Const := WithParams Const) (withList T A₂) (.ex (S.body n).2) := by
    rw [hb]
    exact provable_mono hsub (provable_mono (theory_mono S hsu) hEx)
  have hmem := witnessStep_witnesses (k := m.2.2) hEx₂
  rw [hb] at hmem
  refine ⟨.const (witnessParam A₂ ⟨σ, φ⟩ m.2.2), ?_⟩
  refine provable_mono (theory_mono S hut) (provable_of_mem ?_)
  show _ ∈ withList T (added T S (u ++ [m]))
  rw [hadded, hb]
  exact Or.inr hmem

/-- **The disjunction clause from a fair pair schedule.** -/
theorem provable_or_iff_bar (hT : ParamFree T) (hPair : ∀ p N, ∃ n, N ≤ n ∧ S.pair n = p)
    (s : List (Move Const)) (φ ψ : ClosedFormula (WithParams Const)) :
    Provable (Const := WithParams Const) (theory T S s) (.or φ ψ) ↔
      ∃ B, Bar.IsBar s B ∧ ∀ t ∈ B, Provable (Const := WithParams Const) (theory T S t) φ ∨
        Provable (Const := WithParams Const) (theory T S t) ψ := by
  constructor
  · intro h
    exact ⟨_, isBar_pairBar S (hPair (φ, ψ)) s, fun t ht => provable_disjunct_of_mem_pairBar S h ht⟩
  · rintro ⟨B, hB, h⟩
    refine provable_of_bar S _ hT hB fun t ht => ?_
    rcases h t ht with h | h
    · exact provable_or_intro_left h
    · exact provable_or_intro_right h

/-- **The existential clause from a fair body schedule.** -/
theorem provable_ex_iff_bar (hT : ParamFree T) (hBody : ∀ bd N, ∃ n, N ≤ n ∧ S.body n = bd)
    (s : List (Move Const)) {σ : Ty Base} (φ : Formula (WithParams Const) [σ]) :
    Provable (Const := WithParams Const) (theory T S s) (.ex φ) ↔
      ∃ B, Bar.IsBar s B ∧ ∀ t ∈ B, ∃ r : ClosedTerm (WithParams Const) σ,
        Provable (Const := WithParams Const) (theory T S t) (instantiate (Base := Base) r φ) := by
  constructor
  · intro h
    exact ⟨_, isBar_bodyBar S (hBody ⟨σ, φ⟩) s,
      fun t ht => exists_instance_of_mem_bodyBar S h ht⟩
  · rintro ⟨B, hB, h⟩
    refine provable_of_bar S _ hT hB fun t ht => ?_
    obtain ⟨r, hr⟩ := h t ht
    exact provable_ex_intro r hr

end Clauses

/-! ## The canonical tree Beth structure -/

section Model

variable (S : Schedules Const)

/-- Universal introduction at a fresh parameter over a node theory extended by
one formula. -/
theorem allIntro_theory (hT : ParamFree T) (s : List (Move Const)) {σ' : Ty Base}
    {φb : Formula (WithParams Const) [σ']} {ω : ClosedFormula (WithParams Const)}
    (h : ∀ r : ClosedTerm (WithParams Const) σ',
      Provable (Const := WithParams Const) (insert ω (theory T S s))
        (instantiate (Base := Base) r φb)) :
    Provable (Const := WithParams Const) (insert ω (theory T S s)) (.all φb) := by
  set k := max (supp (added T S s)) (max (maxParam ω) (maxParam φb))
  refine provable_all_intro_fresh (param σ' k) ?_ ?_ (h (.const (param σ' k)))
  · intro ψ hψ
    rcases Set.mem_insert_iff.mp hψ with rfl | hψ
    · exact noConstOccurrence_param_of_ge k ψ (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact fresh_withList hT (le_max_left _ _) ψ hψ
  · exact noConstOccurrence_param_of_ge k φb (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The Lindenbaum model of a node theory, used for the equality laws. -/
noncomputable def nodeLindenbaum (hT : ParamFree T) (s : List (Move Const)) :
    HeytingSem.HeytingGeneralModel Base (WithParams Const) :=
  HeytingSem.Lindenbaum.lindenbaumModelOfAllIntro (theory T S s)
    (fun {_ _ _} h => allIntro_theory S hT s h)

theorem cut {Γ : ClosedTheorySet (WithParams Const)} {a X : ClosedFormula (WithParams Const)}
    (h : Provable (Const := WithParams Const) (insert a Γ) X)
    (ha : Provable (Const := WithParams Const) Γ a) : Provable (Const := WithParams Const) Γ X :=
  HeytingSem.Lindenbaum.provable_cut h ha

/-- The assumption step adds a formula consistent with the node theory. -/
theorem assumeStep_of_consistent {A : List (ClosedFormula (WithParams Const))}
    {α : ClosedFormula (WithParams Const)}
    (h : Consistent (Const := WithParams Const) (insert α (withList T A))) :
    assumeStep T A α = α :: A := by
  classical
  unfold assumeStep
  rw [if_pos h]

/-- **The canonical tree Beth structure** of fair schedules: worlds are runs,
ordered by prefix, covered by bars, and a run forces what its theory proves. -/
noncomputable def model (hT : ParamFree T) (hCons : Consistent (Const := WithParams Const) T)
    (hPair : ∀ p N, ∃ n, N ≤ n ∧ S.pair n = p) (hBody : ∀ bd N, ∃ n, N ≤ n ∧ S.body n = bd) :
    BethHenkin.{u, v, max u v} Base (WithParams Const) where
  World := List (Move Const)
  le s t := s <+: t
  le_refl := List.prefix_refl
  le_trans h₁ h₂ := h₁.trans h₂
  Covers := Bar.IsBar
  covers_le h := h.1
  covers_self := Bar.isBar_self
  covers_mono h hsub hle := Bar.IsBar.mono h hsub hle
  covers_restrict h hst := Bar.IsBar.restrict h hst
  covers_local h hB := Bar.IsBar.trans h hB
  forces s φ := Provable (Const := WithParams Const) (theory T S s) φ
  forces_mono h hφ := provable_mono (theory_mono S h) hφ
  forces_local hB h := provable_of_bar S _ hT hB h
  forces_top := provable_top _
  forces_bot := consistent_theory hT hCons S _
  forces_and := ⟨fun h => ⟨provable_and_left h, provable_and_right h⟩,
    fun h => provable_and_intro h.1 h.2⟩
  forces_or := provable_or_iff_bar S hT hPair _ _ _
  forces_imp := by
    intro s φ ψ
    constructor
    · intro h t hst hφ
      exact provable_mp (provable_mono (theory_mono S hst) h) hφ
    · intro h
      by_contra hImp
      have hNot : ¬ Provable (Const := WithParams Const) (insert φ (theory T S s)) ψ :=
        fun hψ => hImp (provable_imp_of_insert hψ)
      have hA : assumeStep T (added T S s) φ = φ :: added T S s :=
        assumeStep_of_consistent (consistent_of_not_provable hNot)
      have hNot₁ : ¬ Provable (Const := WithParams Const)
          (withList T (assumeStep T (added T S s) φ)) ψ := by
        rw [hA, withList_cons]
        exact hNot
      obtain ⟨b, k, hbk⟩ := exists_child_not_provable_of_assume hT S s.length φ hNot₁
      have hφ : Provable (Const := WithParams Const) (theory T S (s ++ [(φ, b, k)])) φ := by
        refine provable_of_mem ?_
        show φ ∈ withList T (added T S (s ++ [(φ, b, k)]))
        rw [added_append_singleton]
        refine Or.inr (mem_step_of_assume S ?_)
        rw [hA]
        exact List.mem_cons_self
      refine hbk ?_
      have := h (s ++ [(φ, b, k)]) (List.prefix_append _ _) hφ
      rw [theory, added_append_singleton] at this
      exact this
  forces_not := by
    intro s φ
    constructor
    · intro h t hst hφ
      exact consistent_theory hT hCons S t
        (provable_bot_of_not (provable_mono (theory_mono S hst) h) hφ)
    · intro h
      by_contra hNot
      have hCons₁ : Consistent (Const := WithParams Const) (insert φ (theory T S s)) :=
        fun hbot => hNot (provable_not_of_insert_bot hbot)
      have hA : assumeStep T (added T S s) φ = φ :: added T S s :=
        assumeStep_of_consistent hCons₁
      refine h (s ++ [(φ, false, 0)]) (List.prefix_append _ _) (provable_of_mem ?_)
      show φ ∈ withList T (added T S (s ++ [(φ, false, 0)]))
      rw [added_append_singleton]
      refine Or.inr (mem_step_of_assume S ?_)
      rw [hA]
      exact List.mem_cons_self
  forces_all := by
    intro s σ φ
    constructor
    · intro h r
      exact provable_all_elim r h
    · intro h
      set k := max (supp (added T S s)) (maxParam φ)
      exact provable_all_intro_fresh (param σ k) (fresh_withList hT (le_max_left _ _))
        (noConstOccurrence_param_of_ge k φ (le_max_right _ _)) (h (.const (param σ k)))
  forces_ex := provable_ex_iff_bar S hT hBody _ _
  forces_eq_refl := fun {s} {_} t =>
    cut ((nodeLindenbaum S hT s).val_eq_refl t) (provable_top _)
  forces_eq_symm := fun {s} {_} {_ _} h => cut ((nodeLindenbaum S hT s).val_eq_symm _ _) h
  forces_eq_trans := fun {s} {_} {_ _ _} h₁ h₂ =>
    cut ((nodeLindenbaum S hT s).val_eq_trans _ _ _) (provable_and_intro h₁ h₂)
  forces_eq_app := fun {s} {_ _} {_ _} t h => cut ((nodeLindenbaum S hT s).val_eq_app _ _ t) h
  forces_eq_appArg := fun {s} {_ _} f {t u} h =>
    cut ((nodeLindenbaum S hT s).val_eq_appArg f t u) h
  forces_eq_propI := fun {s} {_ _} h₁ h₂ =>
    cut ((nodeLindenbaum S hT s).val_eq_propI _ _) (provable_and_intro h₁ h₂)
  forces_eq_propEL := fun {s} {_ _} h => cut ((nodeLindenbaum S hT s).val_eq_propEL _ _) h
  forces_eq_propER := fun {s} {_ _} h => cut ((nodeLindenbaum S hT s).val_eq_propER _ _) h
  forces_eq_lam := fun {s} {_ _} {t u} h =>
    cut ((nodeLindenbaum S hT s).val_eq_lam t u .top
      fun r => provable_mono (fun hφ => Set.mem_insert_of_mem _ hφ) (h r)) (provable_top _)
  forces_funExt := fun {s} {_ _} {f g} h => cut ((nodeLindenbaum S hT s).val_funExt f g) h
  forces_eq_beta := fun {s} {_ _} t u =>
    cut ((nodeLindenbaum S hT s).val_beta t u) (provable_top _)
  forces_eq_eta := fun {s} {_ _} f => cut ((nodeLindenbaum S hT s).val_eta f) (provable_top _)

end Model

end BethTree

/-! ## Tree Beth structures and completeness -/

/-- A Beth structure is a tree with bars over the alphabet `α` when its worlds
are the finite sequences over `α`, ordered by prefix, and its covers are the
bars. -/
structure BethHenkin.IsTree {Base : Type u} {K : Ty Base → Type v}
    (B : BethHenkin.{u, v, w} Base K) (α : Type w) where
  node : B.World ≃ List α
  le_iff : ∀ U V, B.le U V ↔ node U <+: node V
  covers_iff : ∀ W C, B.Covers W C ↔ BethHenkin.Bar.IsBar (node W) (node '' C)

/-- Consequence over the Beth structures that are trees with bars. -/
def TreeBethConsequence {Base : Type u} {K : Ty Base → Type v}
    (T : ClosedTheorySet K) (θ : ClosedFormula K) : Prop :=
  ∀ (α : Type (max u v)) (B : BethHenkin.{u, v, max u v} Base K), Nonempty (B.IsTree α) →
    ∀ W : B.World, (∀ ψ ∈ T, B.forces W ψ) → B.forces W θ

namespace BethTree

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams ClosedTheorySet BethHenkin

/-- The canonical structure is a tree with bars over the moves. -/
def isTree_model {T : ClosedTheorySet (WithParams Const)} (S : Schedules Const)
    (hT : ParamFree T) (hCons : Consistent (Const := WithParams Const) T)
    (hPair : ∀ p N, ∃ n, N ≤ n ∧ S.pair n = p) (hBody : ∀ bd N, ∃ n, N ≤ n ∧ S.body n = bd) :
    (model S hT hCons hPair hBody).IsTree (Move Const) where
  node := Equiv.refl (List (Move Const))
  le_iff _ _ := Iff.rfl
  covers_iff W C := by
    have hC : ((Equiv.refl (List (Move Const))) '' (C : Set (List (Move Const))) :
        Set (List (Move Const))) = C :=
      Set.ext fun x => ⟨fun ⟨_, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    exact Iff.of_eq (congrArg (Bar.IsBar (W : List (Move Const))) hC.symm)

/-- Tree Beth soundness. -/
theorem treeBethConsequence_of_provable {K : Ty Base → Type v} {T : ClosedTheorySet K}
    {θ : ClosedFormula K} (h : Provable (Const := K) T θ) : TreeBethConsequence T θ :=
  fun _ B _ _ hW => B.forces_of_provable h hW

/-- **Completeness for tree Beth structures from fair schedules.**  The pair
schedule must serve every disjunction pair infinitely often and the body
schedule every existential body; then a parameter-free theory proves every
formula forced at the root of every tree Beth structure that forces it. -/
theorem provable_of_treeBethConsequence {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)} (hT : ParamFree T) (S : Schedules Const)
    (hPair : ∀ p N, ∃ n, N ≤ n ∧ S.pair n = p) (hBody : ∀ bd N, ∃ n, N ≤ n ∧ S.body n = bd)
    (h : TreeBethConsequence T θ) : Provable (Const := WithParams Const) T θ := by
  classical
  by_cases hCons : Consistent (Const := WithParams Const) T
  · have hRoot := h (Move Const) (model S hT hCons hPair hBody)
      ⟨isTree_model S hT hCons hPair hBody⟩ ([] : List (Move Const))
      (fun ψ hψ => provable_of_mem (show ψ ∈ theory T S [] by rw [theory_nil]; exact hψ))
    change Provable (Const := WithParams Const) (theory T S []) θ at hRoot
    rwa [theory_nil] at hRoot
  · exact provable_of_bot (not_not.mp hCons)

/-- **Completeness from fair services**: the schedules are the services of
disjunction pairs and existential bodies with constantly true eligibility. -/
theorem provable_of_treeBethConsequence_of_services {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)} (hT : ParamFree T)
    (PS : EligibleService (fun _ (_ : ClosedFormulaPair Const) => True))
    (BS : EligibleService (fun _ (_ : Body Const) => True))
    (h : TreeBethConsequence T θ) : Provable (Const := WithParams Const) T θ :=
  provable_of_treeBethConsequence hT ⟨PS.serve, BS.serve⟩ PS.always_fair BS.always_fair h

/-- Soundness and completeness for tree Beth structures, from fair services. -/
theorem provable_iff_treeBethConsequence_of_services {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)} (hT : ParamFree T)
    (PS : EligibleService (fun _ (_ : ClosedFormulaPair Const) => True))
    (BS : EligibleService (fun _ (_ : Body Const) => True)) :
    Provable (Const := WithParams Const) T θ ↔ TreeBethConsequence T θ :=
  ⟨treeBethConsequence_of_provable, provable_of_treeBethConsequence_of_services hT PS BS⟩

/-- The fair service of an enumeration with constantly true eligibility. -/
def serviceOfEnumeration {α : Type w} (e : ℕ → α) (he : Function.Surjective e) (a : α) :
    EligibleService (fun _ (_ : α) => True) :=
  EligibleService.ofEnumeration (fun _ _ => true) (fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩)
    e he a fun _ => trivial

/-- **Soundness and completeness for tree Beth structures over countable
signatures**: the schedules come from enumerations of pairs and bodies. -/
theorem provable_iff_treeBethConsequence_of_countable [Countable Base]
    [∀ τ, Countable (Const τ)] {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)} (hT : ParamFree T) :
    Provable (Const := WithParams Const) T θ ↔ TreeBethConsequence T θ := by
  obtain ⟨⟨e, he⟩, ⟨q, hq⟩⟩ :=
    KripkeHenkin.SupportedCanonicalFrame.exists_enumerations_of_countable (Base := Base)
      (Const := Const)
  exact provable_iff_treeBethConsequence_of_services hT
    (serviceOfEnumeration q hq (.top, .top)) (serviceOfEnumeration e he ⟨.prop, .top⟩)

/-! ## Positive controls over the one-point signature -/

section PointControls

open KripkeVarying.Canonical

/-- `∃ x, x = o` over the one-point signature, read in the parameter
language. -/
abbrev pointExistsEqOParam : ClosedFormula (WithParams PointConst) :=
  mapConst (fun c => (inj c : WithParams PointConst _)) pointExistsEqO

/-- Semantic side: `∃ x, x = o` is forced at every world of every tree Beth
structure, by the single-world cover and the witness `o`. -/
theorem pointExistsEqO_treeBethConsequence :
    TreeBethConsequence (∅ : ClosedTheorySet (WithParams PointConst)) pointExistsEqOParam := by
  intro α B _ W _
  show B.forces W (.ex (.eq (.var .vz) (.const (inj .o))))
  refine B.forces_ex.mpr ⟨{W}, B.covers_self W, fun V _ => ⟨.const (inj .o), ?_⟩⟩
  show B.forces V (.eq (.const (inj .o)) (.const (inj .o)))
  exact B.forces_eq_refl _

/-- The enumerations of pairs and bodies chosen for the one-point signature. -/
noncomputable abbrev pointEnumerations :=
  KripkeHenkin.SupportedCanonicalFrame.exists_enumerations_of_countable (Base := Unit)
    (Const := PointConst)

/-- The fair pair service of the one-point signature. -/
noncomputable def pointPairService :
    EligibleService (fun _ (_ : ClosedFormulaPair PointConst) => True) :=
  serviceOfEnumeration (Classical.choose pointEnumerations.2)
    (Classical.choose_spec pointEnumerations.2) (.top, .top)

/-- The fair body service of the one-point signature. -/
noncomputable def pointBodyService : EligibleService (fun _ (_ : Body PointConst) => True) :=
  serviceOfEnumeration (Classical.choose pointEnumerations.1)
    (Classical.choose_spec pointEnumerations.1) ⟨.prop, .top⟩

theorem paramFree_empty {Base : Type u} {Const : Ty Base → Type v} :
    ParamFree (∅ : ClosedTheorySet (WithParams Const)) := fun _ h => h.elim

/-- Completeness side: tree Beth completeness from the fair services returns a
derivation of `∃ x, x = o`. -/
theorem pointExistsEqO_provable_of_treeBeth :
    Provable (Const := WithParams PointConst) ∅ pointExistsEqOParam :=
  provable_of_treeBethConsequence_of_services paramFree_empty pointPairService pointBodyService
    pointExistsEqO_treeBethConsequence

/-- The same through the countable corollary. -/
theorem pointExistsEqO_provable_of_countable_treeBeth :
    Provable (Const := WithParams PointConst) ∅ pointExistsEqOParam :=
  (provable_iff_treeBethConsequence_of_countable (Base := Unit) (Const := PointConst)
    paramFree_empty).mpr pointExistsEqO_treeBethConsequence

/-- The disjunction clause at the root of the canonical tree of fair services:
`⊤ ∨ ⊤` is decided on a bar. -/
theorem point_root_or_bar :
    ∃ B, Bar.IsBar ([] : List (Move PointConst)) B ∧ ∀ t ∈ B,
      Provable (Const := WithParams PointConst)
          (theory ∅ ⟨pointPairService.serve, pointBodyService.serve⟩ t) .top ∨
        Provable (Const := WithParams PointConst)
          (theory ∅ ⟨pointPairService.serve, pointBodyService.serve⟩ t) .top :=
  (provable_or_iff_bar ⟨pointPairService.serve, pointBodyService.serve⟩ paramFree_empty
    pointPairService.always_fair [] .top .top).mp (provable_or_intro_left (provable_top _))

/-- Soundness and completeness from the fair services of the one-point
signature, at `∃ x, x = o`. -/
theorem pointExistsEqO_provable_iff_treeBeth :
    Provable (Const := WithParams PointConst) ∅ pointExistsEqOParam ↔
      TreeBethConsequence (∅ : ClosedTheorySet (WithParams PointConst)) pointExistsEqOParam :=
  provable_iff_treeBethConsequence_of_services paramFree_empty pointPairService pointBodyService

/-- The disjunction clause in the bar-to-root direction: a disjunction decided
on a bar is proved at the root. -/
theorem point_root_or_provable :
    Provable (Const := WithParams PointConst)
      (theory ∅ ⟨pointPairService.serve, pointBodyService.serve⟩ []) (.or .top .top) :=
  (provable_or_iff_bar ⟨pointPairService.serve, pointBodyService.serve⟩ paramFree_empty
    pointPairService.always_fair [] .top .top).mpr point_root_or_bar

/-- Local character at the root of the canonical tree of fair services, on the
bar of nodes past a depth serving `(⊤, ⊤)`. -/
theorem point_root_top_of_bar :
    Provable (Const := WithParams PointConst)
      (theory ∅ ⟨pointPairService.serve, pointBodyService.serve⟩ []) .top :=
  provable_of_bar ⟨pointPairService.serve, pointBodyService.serve⟩ .top paramFree_empty
    (isBar_pairBar ⟨pointPairService.serve, pointBodyService.serve⟩
      (pointPairService.always_fair (.top, .top)) [])
    fun _ _ => provable_top _

/-- The existential clause at the root of the canonical tree of fair services:
`∃ x : prop, ⊤` is witnessed on a bar. -/
theorem point_root_ex_bar :
    ∃ B, Bar.IsBar ([] : List (Move PointConst)) B ∧ ∀ t ∈ B,
      ∃ r : ClosedTerm (WithParams PointConst) .prop,
        Provable (Const := WithParams PointConst)
          (theory ∅ ⟨pointPairService.serve, pointBodyService.serve⟩ t)
          (instantiate (Base := Unit) r (.top : Formula (WithParams PointConst) [.prop])) :=
  (provable_ex_iff_bar ⟨pointPairService.serve, pointBodyService.serve⟩ paramFree_empty
    pointBodyService.always_fair [] (.top : Formula (WithParams PointConst) [.prop])).mp
    (provable_ex_intro (.top) (provable_top _))

end PointControls

end BethTree

end Mettapedia.Logic.HOL
