import Mettapedia.Logic.ReverseMathematics.LeftmostPath
import Mettapedia.GSLT.OpenEnded.SufficientBubbles

/-!
# Least sufficient subsystems: reverse mathematics as a bubble question

Reverse mathematics asks for the weakest subsystem proving a theorem. In the
language of `Mettapedia.GSLT.OpenEnded.SufficientBubbles`, the generators are
the principles of a catalogue, a bubble is a set of principles, and a bubble
is *sufficient* for a target statement when every ω-model of the base theory
satisfying the bubble's principles satisfies the target (`OmegaSufficient`).
ω-sufficiency is monotone (`omegaSufficient_upClosed`), so every theorem of
`SufficientBubbles` about monotone sufficiency applies: a least sufficient
bubble exists exactly when the deletion core is sufficient.

There are two orders on bubbles.

* **Presentations.** Bubbles ordered by inclusion of their principles. Two
  incomparable routes to the target kill the least bubble
  (`no_least_of_two_routes`), as two incomparable derivation supports do in
  `SufficientBubbles.no_least_of_incomparable_supports`.
* **Theories.** Bubbles closed under ω-consequence inside the catalogue
  (`omegaClosure`). If the target is itself a catalogue principle, its
  closure is the least closed sufficient bubble (`isLeast_closure_of_target`):
  the least *theory* always exists once the statement may be added as an
  axiom. Without that, two routes that are incomparable in strength again
  leave no least closed bubble (`no_least_closed_of_two_routes`).

## Instances

* **Unconditional, presentation level.** Over Turing ideals, the existence
  of a diagonally noncomputable function (`HasDNR`) follows from weak König's
  lemma (through the Kleene tree) and from arithmetical comprehension (through
  a `Δ⁰₂` definition), and fails in the recursive sets. So the catalogue
  `{WKL, ACA}` has no least bubble sufficient for `HasDNR`
  (`dnr_no_least_route_bubble`); its deletion core is empty
  (`dnr_route_core_eq_empty`).
* **Unconditional, theory level.** ACA implies WKL over Turing ideals
  (`IsTuringIdeal.WKL_of_models_ACA0`, the ω-model form of Simpson §III.7),
  so in strength the two routes are comparable, and the closure of `{WKL}` is
  the least closed bubble (`dnr_least_closed_route_bubble`). The same
  catalogue has no least presentation and a least theory.
* **Conditional, theory level.** The genuinely incomparable shape is
  `{WKL, RT²₂}`:
  `dnr_no_least_closed_WKL_RT22` derives the absence of a least closed bubble
  from three published theorems taken as hypotheses (RT²₂ ⊢ DNR,
  Hirschfeldt–Jockusch–Kjos-Hanssen–Lempp–Slaman 2008; an ω-model of RT²₂
  without WKL, Liu 2012; an ω-model of WKL without RT²₂, from Jockusch 1972
  and Jockusch–Soare 1972). Its conclusion is a statement about bubbles that
  none of the hypotheses mentions.

## References

* S. G. Simpson, *Subsystems of Second Order Arithmetic*, 2nd ed., Cambridge
  University Press / ASL, 2009.
* D. R. Hirschfeldt, C. G. Jockusch Jr., B. Kjos-Hanssen, S. Lempp,
  T. A. Slaman, *The strength of some combinatorial principles related to
  Ramsey's theorem for pairs*, in Computational Prospects of Infinity II,
  World Scientific, 2008.
* J. Liu, *RT²₂ does not imply WKL₀*, J. Symbolic Logic 77 (2012) 609–620.
* C. G. Jockusch Jr., *Ramsey's theorem and recursion theory*, J. Symbolic
  Logic 37 (1972) 268–280.
* C. G. Jockusch Jr., R. I. Soare, *Π⁰₁ classes and degrees of theories*,
  Trans. AMS 173 (1972) 33–56.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Mettapedia.GSLT.OpenEnded.SufficientBubbles

section General

variable {P : Type*} (base : Set (Set ℕ) → Prop) (meaning : P → Set (Set ℕ) → Prop)

/-- `S` is an ω-model of the base theory and of every principle in `B`. -/
def ModelOf (B : Set P) (S : Set (Set ℕ)) : Prop :=
  base S ∧ ∀ p ∈ B, meaning p S

/-- Every ω-model of the bubble satisfies the target. -/
def OmegaSufficient (target : Set (Set ℕ) → Prop) (B : Set P) : Prop :=
  ∀ S, ModelOf base meaning B S → target S

variable {base meaning}

/-- **ω-sufficiency is monotone**: more principles, fewer models. -/
theorem omegaSufficient_upClosed (target : Set (Set ℕ) → Prop) :
    UpClosed (OmegaSufficient base meaning target) := by
  intro B C sub sufficient S ⟨hbase, hC⟩
  exact sufficient S ⟨hbase, fun p hp => hC p (sub hp)⟩

/-- A least sufficient bubble exists exactly when the deletion core is
sufficient. -/
theorem omega_exists_least_iff_core (target : Set (Set ℕ) → Prop) :
    (∃ least, IsLeast {B | OmegaSufficient base meaning target B} least) ↔
      OmegaSufficient base meaning target (core (OmegaSufficient base meaning target)) :=
  exists_least_iff_core_sufficient (omegaSufficient_upClosed target)

variable (base meaning)

/-- The principles of the catalogue that hold in every ω-model of `B`. -/
def omegaClosure (B : Set P) : Set P :=
  {p | ∀ S, ModelOf base meaning B S → meaning p S}

/-- A bubble closed under ω-consequence inside the catalogue: a theory. -/
def IsOmegaClosed (B : Set P) : Prop :=
  omegaClosure base meaning B ⊆ B

variable {base meaning}

theorem subset_omegaClosure (B : Set P) : B ⊆ omegaClosure base meaning B :=
  fun _ hp _ ⟨_, hB⟩ => hB _ hp

theorem modelOf_omegaClosure_iff (B : Set P) (S : Set (Set ℕ)) :
    ModelOf base meaning (omegaClosure base meaning B) S ↔ ModelOf base meaning B S := by
  constructor
  · rintro ⟨hbase, hcl⟩
    exact ⟨hbase, fun p hp => hcl p (subset_omegaClosure B hp)⟩
  · intro model
    exact ⟨model.1, fun _ hp => hp S model⟩

theorem omegaClosure_isOmegaClosed (B : Set P) :
    IsOmegaClosed base meaning (omegaClosure base meaning B) :=
  fun _ hp S model => hp S ((modelOf_omegaClosure_iff B S).mpr model)

theorem omegaClosure_mono {B C : Set P} (sub : B ⊆ C) :
    omegaClosure base meaning B ⊆ omegaClosure base meaning C :=
  fun _ hp S ⟨hbase, hC⟩ => hp S ⟨hbase, fun q hq => hC q (sub hq)⟩

theorem omegaSufficient_omegaClosure_iff (target : Set (Set ℕ) → Prop) (B : Set P) :
    OmegaSufficient base meaning target (omegaClosure base meaning B) ↔
      OmegaSufficient base meaning target B := by
  simp only [OmegaSufficient, modelOf_omegaClosure_iff]

/-- **The least theory exists once the target is a principle.** If the
target is the meaning of a catalogue principle `p` over the base, the closure
of `{p}` is the least closed sufficient bubble. -/
theorem isLeast_closure_of_target {target : Set (Set ℕ) → Prop} (p : P)
    (hp : ∀ S, base S → (meaning p S ↔ target S)) :
    IsLeast {B | IsOmegaClosed base meaning B ∧ OmegaSufficient base meaning target B}
      (omegaClosure base meaning {p}) := by
  refine ⟨⟨omegaClosure_isOmegaClosed _, fun S model => ?_⟩, ?_⟩
  · obtain ⟨hbase, hcl⟩ := (modelOf_omegaClosure_iff {p} S).mpr
      ((modelOf_omegaClosure_iff {p} S).mp model)
    exact (hp S hbase).mp (hcl p (subset_omegaClosure {p} rfl))
  · rintro B ⟨closed, sufficient⟩
    have member : p ∈ B :=
      closed fun S model => (hp S model.1).mpr (sufficient S model)
    exact (omegaClosure_mono (Set.singleton_subset_iff.mpr member)).trans closed

/-- On a two-principle catalogue with two sufficient routes and an
insufficient empty bubble, sufficiency is "contains one of the routes". -/
theorem omegaSufficient_iff_route {target : Set (Set ℕ) → Prop} {p q : P}
    (only : ∀ r : P, r = p ∨ r = q)
    (hp : OmegaSufficient base meaning target {p}) (hq : OmegaSufficient base meaning target {q})
    (h0 : ¬ OmegaSufficient base meaning target ∅) (B : Set P) :
    OmegaSufficient base meaning target B ↔ SupportedBy {{p}, {q}} B := by
  constructor
  · intro sufficient
    by_cases hpB : p ∈ B
    · exact ⟨{p}, Or.inl rfl, Set.singleton_subset_iff.mpr hpB⟩
    by_cases hqB : q ∈ B
    · exact ⟨{q}, Or.inr rfl, Set.singleton_subset_iff.mpr hqB⟩
    have empty : B = ∅ := by
      ext r
      simp only [Set.mem_empty_iff_false, iff_false]
      rcases only r with rfl | rfl
      · exact hpB
      · exact hqB
    exact absurd (empty ▸ sufficient) h0
  · rintro ⟨A, hA, sub⟩
    rcases hA with rfl | rfl
    · exact omegaSufficient_upClosed target sub hp
    · exact omegaSufficient_upClosed target sub hq

/-- **Two routes, no least bubble.** -/
theorem no_least_of_two_routes {target : Set (Set ℕ) → Prop} {p q : P} (hpq : p ≠ q)
    (only : ∀ r : P, r = p ∨ r = q)
    (hp : OmegaSufficient base meaning target {p}) (hq : OmegaSufficient base meaning target {q})
    (h0 : ¬ OmegaSufficient base meaning target ∅) :
    ¬ ∃ least, IsLeast {B | OmegaSufficient base meaning target B} least := by
  have same : {B | OmegaSufficient base meaning target B} = {B | SupportedBy {{p}, {q}} B} := by
    ext B
    exact omegaSufficient_iff_route only hp hq h0 B
  rw [same]
  exact no_least_of_incomparable_supports
    (fun sub => hpq (Set.singleton_subset_singleton.mp sub))
    (fun sub => hpq (Set.singleton_subset_singleton.mp sub).symm)

/-- With two sufficient routes, the deletion core is empty. -/
theorem core_eq_empty_of_two_routes {target : Set (Set ℕ) → Prop} {p q : P} (hpq : p ≠ q)
    (only : ∀ r : P, r = p ∨ r = q)
    (hp : OmegaSufficient base meaning target {p}) (hq : OmegaSufficient base meaning target {q}) :
    core (OmegaSufficient base meaning target) = ∅ := by
  ext r
  simp only [core, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  rcases only r with rfl | rfl
  · refine omegaSufficient_upClosed target (fun x hx => ?_) hq
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fun same => hpq same.symm
  · refine omegaSufficient_upClosed target (fun x hx => ?_) hp
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hpq

/-- **Two routes incomparable in strength: no least theory either.** -/
theorem no_least_closed_of_two_routes {target : Set (Set ℕ) → Prop} {p q : P}
    (only : ∀ r : P, r = p ∨ r = q)
    (hp : OmegaSufficient base meaning target {p}) (hq : OmegaSufficient base meaning target {q})
    (h0 : ∃ S, base S ∧ ¬ target S)
    (pNotQ : ∃ S, base S ∧ meaning p S ∧ ¬ meaning q S)
    (qNotP : ∃ S, base S ∧ meaning q S ∧ ¬ meaning p S) :
    ¬ ∃ least, IsLeast {B | IsOmegaClosed base meaning B ∧ OmegaSufficient base meaning target B}
      least := by
  rintro ⟨L, ⟨_, sufficientL⟩, lower⟩
  have closureP : omegaClosure base meaning {p} ⊆ {p} := by
    intro r hr
    rcases only r with rfl | rfl
    · rfl
    · obtain ⟨S, hbase, hpS, hqS⟩ := pNotQ
      exact absurd (hr S ⟨hbase, fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hpS⟩) hqS
  have closureQ : omegaClosure base meaning {q} ⊆ {q} := by
    intro r hr
    rcases only r with rfl | rfl
    · obtain ⟨S, hbase, hqS, hpS⟩ := qNotP
      exact absurd (hr S ⟨hbase, fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hqS⟩) hpS
    · rfl
  have inP : L ⊆ {p} := lower ⟨closureP, hp⟩
  have inQ : L ⊆ {q} := lower ⟨closureQ, hq⟩
  obtain ⟨S, hbase, notTarget⟩ := h0
  refine notTarget (sufficientL S ⟨hbase, fun r hr => ?_⟩)
  have rp := Set.mem_singleton_iff.mp (inP hr)
  have rq := Set.mem_singleton_iff.mp (inQ hr)
  subst rp
  obtain ⟨S', _, hpS', hqS'⟩ := pNotQ
  exact absurd (rq ▸ hpS') hqS'

end General

/-! ## Two routes to a diagonally noncomputable function -/

/-- Two principles that each yield a diagonally noncomputable function. -/
inductive DNRRoute
  | wkl
  | aca
  deriving DecidableEq

/-- The ω-model meaning of each route. -/
def DNRRoute.meaning : DNRRoute → Set (Set ℕ) → Prop
  | .wkl => WKL
  | .aca => fun S => Models S (ACA0 : Set (Formula Signature.primrec))

theorem DNRRoute.only (r : DNRRoute) : r = .wkl ∨ r = .aca := by
  cases r
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem dnr_sufficient_wkl : OmegaSufficient IsTuringIdeal DNRRoute.meaning HasDNR {.wkl} :=
  fun _ ⟨hS, h⟩ => hS.hasDNR_of_WKL (h .wkl rfl)

theorem dnr_sufficient_aca : OmegaSufficient IsTuringIdeal DNRRoute.meaning HasDNR {.aca} :=
  fun _ ⟨_, h⟩ => Models.hasDNR (h .aca rfl)

/-- The base alone is not sufficient: the recursive sets. -/
theorem dnr_not_sufficient_empty :
    ¬ OmegaSufficient IsTuringIdeal DNRRoute.meaning HasDNR ∅ :=
  fun h => not_hasDNR_recursiveSets (h _ ⟨recursiveSets_isTuringIdeal, fun _ absurd => absurd.elim⟩)

/-- **No least bubble of `{WKL, ACA}` suffices for a DNR function.** -/
theorem dnr_no_least_route_bubble :
    ¬ ∃ least, IsLeast {B | OmegaSufficient IsTuringIdeal DNRRoute.meaning HasDNR B} least :=
  no_least_of_two_routes (by decide) DNRRoute.only dnr_sufficient_wkl dnr_sufficient_aca
    dnr_not_sufficient_empty

/-- The deletion test sees it: removing either route leaves the other. -/
theorem dnr_route_core_eq_empty :
    core (OmegaSufficient IsTuringIdeal DNRRoute.meaning HasDNR) = ∅ :=
  core_eq_empty_of_two_routes (by decide) DNRRoute.only dnr_sufficient_wkl dnr_sufficient_aca

/-- **In strength the two routes are comparable.** If arithmetical
comprehension implies weak König's lemma over Turing ideals (Simpson §III.7),
the closure of `{WKL}` is the least closed bubble sufficient for a DNR
function. -/
theorem dnr_least_closed_of_aca_implies_wkl
    (acaWkl : ∀ S, IsTuringIdeal S → DNRRoute.meaning .aca S → WKL S) :
    IsLeast {B | IsOmegaClosed IsTuringIdeal DNRRoute.meaning B ∧
        OmegaSufficient IsTuringIdeal DNRRoute.meaning HasDNR B}
      (omegaClosure IsTuringIdeal DNRRoute.meaning {.wkl}) := by
  refine ⟨⟨omegaClosure_isOmegaClosed _,
    (omegaSufficient_omegaClosure_iff HasDNR {DNRRoute.wkl}).mpr dnr_sufficient_wkl⟩, ?_⟩
  rintro B ⟨closed, sufficient⟩
  have wklMem : DNRRoute.wkl ∈ B := by
    rcases (omegaSufficient_iff_route DNRRoute.only dnr_sufficient_wkl dnr_sufficient_aca
        dnr_not_sufficient_empty B).mp sufficient with ⟨A, hA, sub⟩
    rcases hA with rfl | rfl
    · exact sub rfl
    · exact closed fun S ⟨hS, h⟩ => acaWkl S hS (h .aca (sub rfl))
  exact (omegaClosure_mono (Set.singleton_subset_iff.mpr wklMem)).trans closed

/-- **The least theory of `{WKL, ACA}` giving a DNR function is the closure
of `{WKL}`**: arithmetical comprehension implies weak König's lemma over
Turing ideals. -/
theorem dnr_least_closed_route_bubble :
    IsLeast {B | IsOmegaClosed IsTuringIdeal DNRRoute.meaning B ∧
        OmegaSufficient IsTuringIdeal DNRRoute.meaning HasDNR B}
      (omegaClosure IsTuringIdeal DNRRoute.meaning {.wkl}) :=
  dnr_least_closed_of_aca_implies_wkl fun _ hS h => hS.WKL_of_models_ACA0 h

/-- ACA is not a consequence of the base alone: the recursive sets form a
Turing ideal that is not an ω-model of ACA₀. Whether the closure of `{WKL}`
omits ACA is the question whether some Turing ideal satisfying WKL is not an
ω-model of ACA₀ (true by the low basis theorem of Jockusch and Soare, not
formalized here). -/
theorem aca_not_mem_closure_empty :
    DNRRoute.aca ∉ omegaClosure IsTuringIdeal DNRRoute.meaning ∅ :=
  fun h => recursiveSets_not_models_ACA0
    (h recursiveSets ⟨recursiveSets_isTuringIdeal, fun _ absurd => absurd.elim⟩)

/-! ## Ramsey's theorem for pairs, and the incomparable shape -/

/-- `H` is homogeneous for the 2-coloring of pairs coded by `C`: the pair
`x < y` gets the color `Nat.pair x y ∈ C`. -/
def IsHomogeneous (C H : Set ℕ) : Prop :=
  ∀ x₁ ∈ H, ∀ y₁ ∈ H, ∀ x₂ ∈ H, ∀ y₂ ∈ H, x₁ < y₁ → x₂ < y₂ →
    (Nat.pair x₁ y₁ ∈ C ↔ Nat.pair x₂ y₂ ∈ C)

/-- Ramsey's theorem for pairs and two colors in the ω-model `S`. -/
def RT22 (S : Set (Set ℕ)) : Prop :=
  ∀ C ∈ S, ∃ H ∈ S, H.Infinite ∧ IsHomogeneous C H

/-- **Ramsey's theorem for pairs and two colors**: every coloring has an
infinite homogeneous set. The proof thins an infinite set one element at a
time, keeping the color to the chosen element constant, then applies the
pigeonhole principle to the colors. -/
theorem exists_infinite_homogeneous (C : Set ℕ) : ∃ H : Set ℕ, H.Infinite ∧ IsHomogeneous C H := by
  classical
  have step : ∀ H : Set ℕ, H.Infinite → ∃ a ∈ H, ∃ b : Bool, ∃ H' ⊆ H, H'.Infinite ∧
      ∀ y ∈ H', a < y ∧ (Nat.pair a y ∈ C ↔ b = true) := by
    intro H hH
    obtain ⟨a, ha⟩ := hH.nonempty
    have above : {y | y ∈ H ∧ a < y}.Infinite := by
      have : {y | y ∈ H ∧ a < y} = H \ {y | y ≤ a} := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le]
      rw [this]
      exact hH.sdiff (Set.finite_le_nat a)
    have split : {y | y ∈ H ∧ a < y} =
        {y | (y ∈ H ∧ a < y) ∧ Nat.pair a y ∈ C} ∪ {y | (y ∈ H ∧ a < y) ∧ Nat.pair a y ∉ C} := by
      ext y
      by_cases hy : Nat.pair a y ∈ C <;> simp [hy]
    rw [split] at above
    rcases Set.infinite_union.mp above with one | zero
    · exact ⟨a, ha, true, _, fun y hy => hy.1.1, one, fun y hy => ⟨hy.1.2, by simp [hy.2]⟩⟩
    · exact ⟨a, ha, false, _, fun y hy => hy.1.1, zero, fun y hy => ⟨hy.1.2, by simp [hy.2]⟩⟩
  choose a _ b H' sub infinite spec using step
  let seq : ℕ → {H : Set ℕ // H.Infinite} := fun n =>
    Nat.rec ⟨Set.univ, Set.infinite_univ⟩ (fun _ S => ⟨H' S.1 S.2, infinite S.1 S.2⟩) n
  let x : ℕ → ℕ := fun n => a (seq n).1 (seq n).2
  let color : ℕ → Bool := fun n => b (seq n).1 (seq n).2
  have shrink : ∀ i j, i ≤ j → (seq j).1 ⊆ (seq i).1 := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact subset_rfl
    | succ j _ ih => exact (sub (seq j).1 (seq j).2).trans ih
  have mem : ∀ j, x j ∈ (seq j).1 := fun j => by
    rename_i hmem
    exact hmem (seq j).1 (seq j).2
  have key : ∀ i j, i < j → x i < x j ∧ (Nat.pair (x i) (x j) ∈ C ↔ color i = true) :=
    fun i j hij => spec (seq i).1 (seq i).2 (x j) (shrink (i + 1) j hij (mem j))
  have mono : StrictMono x := strictMono_nat_of_lt_succ fun n => (key n (n + 1) (lt_add_one n)).1
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, {i | color i = b₀}.Infinite := by
    by_contra none
    push Not at none
    have cover : (Set.univ : Set ℕ) = {i | color i = true} ∪ {i | color i = false} := by
      ext i
      cases color i <;> simp
    exact Set.infinite_univ (cover ▸ (none true).union (none false))
  refine ⟨x '' {i | color i = b₀}, hb₀.image mono.injective.injOn, ?_⟩
  rintro _ ⟨i₁, hi₁, rfl⟩ _ ⟨j₁, _, rfl⟩ _ ⟨i₂, hi₂, rfl⟩ _ ⟨j₂, _, rfl⟩ lt₁ lt₂
  rw [(key _ _ (mono.lt_iff_lt.mp lt₁)).2, (key _ _ (mono.lt_iff_lt.mp lt₂)).2]
  simp only [Set.mem_ofPred_eq] at hi₁ hi₂
  rw [hi₁, hi₂]

/-- **The full power set satisfies RT²₂.** -/
theorem univ_RT22 : RT22 (Set.univ : Set (Set ℕ)) := fun C _ =>
  let ⟨H, infinite, homogeneous⟩ := exists_infinite_homogeneous C
  ⟨H, trivial, infinite, homogeneous⟩

/-- Positive example: everything is homogeneous for a constant coloring, so
`{∅, ℕ}` satisfies RT²₂. -/
example : RT22 {∅, Set.univ} := by
  intro C hC
  refine ⟨Set.univ, Or.inr rfl, Set.infinite_univ, ?_⟩
  rcases hC with rfl | rfl <;> simp [IsHomogeneous]

/-- Negative example: `{{0}}` fails RT²₂, since its only member is finite. -/
example : ¬ RT22 {{0}} := by
  intro h
  obtain ⟨H, hH, infinite, _⟩ := h {0} rfl
  rw [Set.mem_singleton_iff] at hH
  subst hH
  exact infinite (Set.finite_singleton 0)

/-- Negative example of homogeneity: `ℕ` is not homogeneous for the coloring
that marks only the pair `(0, 1)`. -/
example : ¬ IsHomogeneous {Nat.pair 0 1} Set.univ := by
  intro h
  have := (h 0 trivial 1 trivial 0 trivial 2 trivial Nat.zero_lt_one Nat.two_pos).mp rfl
  rw [Set.mem_singleton_iff] at this
  have := congrArg (fun m => (Nat.unpair m).2) this
  simp at this

/-- The catalogue `{WKL, RT²₂}`. -/
inductive DNRPrinciple
  | wkl
  | rt22
  deriving DecidableEq

def DNRPrinciple.meaning : DNRPrinciple → Set (Set ℕ) → Prop
  | .wkl => WKL
  | .rt22 => RT22

theorem DNRPrinciple.only (r : DNRPrinciple) : r = .wkl ∨ r = .rt22 := by
  cases r
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **No least theory of `{WKL, RT²₂}` gives a DNR function**, from three
published separations and implications taken as hypotheses:
`rt22Dnr` (Hirschfeldt–Jockusch–Kjos-Hanssen–Lempp–Slaman 2008),
`liu` (Liu 2012), `jockusch` (Jockusch 1972 with Jockusch–Soare 1972). -/
theorem dnr_no_least_closed_WKL_RT22
    (rt22Dnr : ∀ S, IsTuringIdeal S → RT22 S → HasDNR S)
    (liu : ∃ S, IsTuringIdeal S ∧ RT22 S ∧ ¬ WKL S)
    (jockusch : ∃ S, IsTuringIdeal S ∧ WKL S ∧ ¬ RT22 S) :
    ¬ ∃ least, IsLeast {B | IsOmegaClosed IsTuringIdeal DNRPrinciple.meaning B ∧
        OmegaSufficient IsTuringIdeal DNRPrinciple.meaning HasDNR B} least :=
  no_least_closed_of_two_routes DNRPrinciple.only
    (fun _ ⟨hS, h⟩ => hS.hasDNR_of_WKL (h .wkl rfl))
    (fun S ⟨hS, h⟩ => rt22Dnr S hS (h .rt22 rfl))
    ⟨recursiveSets, recursiveSets_isTuringIdeal, not_hasDNR_recursiveSets⟩
    jockusch liu

/-- With DNR in the catalogue the least theory exists: it is the closure of
`{DNR}`. -/
theorem dnr_least_theory_with_dnr {P : Type*} (meaning : P → Set (Set ℕ) → Prop) (dnr : P)
    (hdnr : ∀ S, meaning dnr S ↔ HasDNR S) :
    IsLeast {B | IsOmegaClosed IsTuringIdeal meaning B ∧
        OmegaSufficient IsTuringIdeal meaning HasDNR B}
      (omegaClosure IsTuringIdeal meaning {dnr}) :=
  isLeast_closure_of_target dnr fun S _ => hdnr S

#print axioms omegaSufficient_upClosed
#print axioms no_least_of_two_routes
#print axioms no_least_closed_of_two_routes
#print axioms isLeast_closure_of_target
#print axioms dnr_no_least_route_bubble
#print axioms dnr_route_core_eq_empty
#print axioms dnr_least_closed_of_aca_implies_wkl
#print axioms dnr_least_closed_route_bubble
#print axioms dnr_no_least_closed_WKL_RT22
#print axioms exists_infinite_homogeneous

end Mettapedia.Logic.ReverseMathematics
