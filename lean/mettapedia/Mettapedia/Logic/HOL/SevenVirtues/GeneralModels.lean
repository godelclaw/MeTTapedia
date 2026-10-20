import Mettapedia.Logic.HOL.SevenVirtues.Completeness
import Mettapedia.Logic.HOL.SevenVirtues.Peano
import Mettapedia.Logic.HOL.SevenVirtues.OrderedField
import Mathlib.Analysis.Real.Cardinality

/-!
# Virtue 6: general models carry first-order model theory and separate
# standard from nonstandard models

Henkin's general models are the extensional Henkin models of
`Completeness.lean`; the standard ones are those with full domains.

* `compactness`: a theory over a countable signature with closed inhabitants,
  each of whose finite parts has an extensional Henkin model, has one.
* `exists_countable_model`: downward Löwenheim–Skolem. A consistent theory has
  an extensional Henkin model whose base carriers are countable and whose
  domain at every type is countable up to extensional equality
  (`CountableModEqv`).
* `Nonstandard.exists_nonstandard_model`: Peano's axioms have an extensional
  Henkin model with an individual that is no numeral; it is not full and not
  isomorphic to the natural numbers (`Nonstandard.not_categorical`), although
  all full models are (`Peano.categorical`).
* `Nonstandard.standard_not_compact`: the theory "Peano's axioms plus a new
  constant different from every numeral" has a full model for each finite part
  but none for the whole theory. Compactness, true for general models, fails
  for standard ones, so standard and general consequence differ
  (`Nonstandard.consequence_differs`), and no finitary calculus is strongly
  complete for standard semantics
  (`Nonstandard.no_strongly_complete_finitary_calculus`).
* `Nonstandard.exists_countable_peano_model`: Peano's axioms have a general
  model with countably many predicates up to extensional equality, while
  every full model with an infinite base has uncountably many
  (`not_countableModEqv_pred_of_full`).
* `exists_countable_real_model`: the theory of the complete ordered field has
  an extensional Henkin model with countably many individuals (Farmer's
  Corollary 10), so it is not full: every full model is the real numbers
  (`OrderedField.full_model_is_real`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues

open ClosedTheorySet WithParams

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Compactness -/

/-- **Compactness for general models.** If every finite part of a theory has
an extensional Henkin model, at any universe level, the theory has one. -/
theorem compactness [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b)) {T : ClosedTheorySet Const}
    (hFin : ∀ Γ : List (ClosedFormula Const), (∀ ψ ∈ Γ, ψ ∈ T) →
      ∃ M : HenkinModel.{u, v, w} Base Const, M.FunctionsRespectEqv ∧ ∀ ψ ∈ Γ, M.models ψ) :
    ∃ M : HenkinModel.{u, v, v} Base Const, M.FunctionsRespectEqv ∧ ∀ ψ ∈ T, M.models ψ := by
  classical
  refine (consistent_iff_satisfiable inh T).mp ?_
  rintro ⟨Γ, hΓ, d⟩
  obtain ⟨M, hExt, hM⟩ := hFin (Γ.filter (fun ψ => decide (ψ ∈ T))) (by
    intro ψ hψ
    simpa using (List.mem_filter.mp hψ).2)
  refine HenkinModel.models_bot M (Soundness.extDerivation_sound d (M := M)
    (ρ := fun v => nomatch v) hExt (by intro _ v; nomatch v) ?_)
  intro ψ hψ
  by_cases hT : ψ ∈ T
  · exact hM ψ (List.mem_filter.mpr ⟨hψ, by simpa using hT⟩)
  · rcases hΓ ψ hψ with rfl | hψT
    · exact models_excludedMiddle M
    · exact absurd hψT hT

/-! ## Downward Löwenheim–Skolem -/

/-- The admissible values at `τ` are countable up to extensional equality. -/
def CountableModEqv (M : HenkinModel.{u, v, w} Base Const) (τ : Ty Base) : Prop :=
  ∃ f : ℕ → Ty.denote M.Carrier τ, (∀ n, M.adm τ (f n)) ∧
    ∀ x, M.adm τ x → ∃ n, M.Eqv τ x (f n)

/-- **Downward Löwenheim–Skolem for general models** (Henkin; Farmer's
Theorem 9 for countable signatures). A consistent theory over a countable
signature with closed inhabitants has an extensional Henkin model with
countable base carriers whose domains are countable up to extensional
equality at every type. -/
theorem exists_countable_model [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b)) {T : ClosedTheorySet Const}
    (hCons : Consistent (Const := Const) (insert excludedMiddle T)) :
    ∃ M : HenkinModel.{u, v, v} Base Const, M.FunctionsRespectEqv ∧ (∀ ψ ∈ T, M.models ψ) ∧
      (∀ b, Countable (M.Carrier b)) ∧ ∀ τ, CountableModEqv M τ := by
  obtain ⟨enum, henum⟩ := exists_body_enumeration (Const := Const)
  have hImage := consistent_image_of_consistent inh hCons
  have hWitness := witnessLimit_consistent (paramImage (insert excludedMiddle T)) enum hImage
    (paramImage_paramFree _)
  have hLem : (excludedMiddle : ClosedFormula (WithParams Const)) ∈
      witnessLimit (paramImage (insert excludedMiddle T)) enum :=
    subset_witnessLimit _ enum ⟨excludedMiddle, Set.mem_insert _ _, rfl⟩
  obtain ⟨W, hW, hC⟩ := exists_classical_world enum henum
    (consistent_union_emSchema hLem hWitness)
  let N := termHenkinModel W hC
  refine ⟨HenkinModel.constantSubstitutionReduct (fun {_} c => .const (inj c)) N,
    (HenkinModel.constantSubstitutionReduct_functionsRespectEqv_iff _ N).mpr
      (termHenkinModel_functionsRespectEqv W hC), ?_, ?_, ?_⟩
  · intro ψ hψ
    rw [← HenkinModel.models_substConst, substConst_constant_images]
    rw [termHenkinModel_models_iff]
    exact hW _ (Set.mem_union_left _
      (subset_witnessLimit _ enum ⟨ψ, Set.mem_insert_of_mem _ hψ, rfl⟩))
  · intro b
    change Countable (ULift (TermDom W (.base b)))
    refine Function.Surjective.countable
      (f := fun t : ClosedTerm (WithParams Const) (.base b) =>
        (ULift.up (TermDom.mk W t) : ULift (TermDom W (.base b)))) ?_
    rintro ⟨q⟩
    obtain ⟨t, rfl⟩ := Quotient.exists_rep q
    exact ⟨t, rfl⟩
  · intro τ
    have : Nonempty (ClosedTerm (WithParams Const) τ) := ⟨.const (param τ 0)⟩
    obtain ⟨enumTerm, surjective⟩ := exists_surjective_nat (ClosedTerm (WithParams Const) τ)
    refine ⟨fun n => tval W τ (enumTerm n), fun n => ⟨enumTerm n, rep_tval W hC _⟩, ?_⟩
    rintro x ⟨t, ht⟩
    obtain ⟨n, rfl⟩ := surjective t
    refine ⟨n, ?_⟩
    have hEqv := (eqv_rep_iff W hC τ ht (rep_tval W hC (enumTerm n))).mpr
      (World.eq_refl_mem (enumTerm n))
    exact (HenkinModel.eqv_constantSubstitutionReduct _ N τ _ _).mpr hEqv

/-- In a full model whose base type `b` is infinite, the predicates on `b`
are not countable up to extensional equality (Cantor). -/
theorem not_countableModEqv_pred_of_full (M : HenkinModel.{u, v, w} Base Const)
    (full : M.FullDomains) (b : Base) [Infinite (M.Carrier b)] :
    ¬ CountableModEqv M (.base b ⇒ .prop) := by
  rintro ⟨f, _, hf⟩
  let F : ℕ → M.Carrier b → ULift.{max (u + 1) w} Prop := f
  let g := Infinite.natEmbedding (M.Carrier b)
  apply Function.cantor_surjective (fun n => {m : ℕ | (F n (g m)).down})
  intro S
  obtain ⟨n, hn⟩ := hf (fun x : M.Carrier b => ULift.up (∃ m, g m = x ∧ m ∈ S)) (full _ _)
  have heq : (fun x : M.Carrier b => ULift.up (∃ m, g m = x ∧ m ∈ S)) = F n :=
    M.eq_of_eqv_of_fullDomains full hn
  refine ⟨n, ?_⟩
  ext m
  change (F n (g m)).down ↔ m ∈ S
  rw [← heq]
  constructor
  · rintro ⟨m', hm', hS⟩
    rw [g.injective hm'] at hS
    exact hS
  · intro hS
    exact ⟨m, rfl, hS⟩

/-! ## A nonstandard model of Peano's axioms -/

namespace Nonstandard

open Peano

/-- Peano's constants and one new individual constant. -/
inductive WithNew : Ty Unit → Type
  | old {τ : Ty Unit} : PeanoConst τ → WithNew τ
  | new : WithNew ι
  deriving DecidableEq, Countable

/-- Zero in the extended signature. -/
abbrev zero : WithNew ι := .old .zero

/-- Successor in the extended signature. -/
abbrev succ : WithNew (ι ⇒ ι) := .old .succ

/-- "The new constant is not the numeral `n`." -/
def avoids (n : ℕ) : ClosedFormula WithNew :=
  .not (.eq (.const .new) (numeral zero succ n))

/-- Peano's axioms, and the new constant different from every numeral. -/
def theory : ClosedTheorySet WithNew :=
  axioms zero succ ∪ Set.range avoids

theorem numeral_injective {Const : Ty Unit → Type} (z : Const ι) (s : Const (ι ⇒ ι)) :
    Function.Injective (numeral z s) := by
  intro m
  induction m with
  | zero => intro n h; cases n with
    | zero => rfl
    | succ n => cases h
  | succ m ih => intro n h; cases n with
    | zero => cases h
    | succ n =>
        simp only [numeral, Term.app.injEq, heq_eq_eq, true_and] at h
        exact congrArg Nat.succ (ih h)

theorem avoids_injective : Function.Injective avoids := by
  intro m n h
  simp only [avoids, Term.not.injEq, Term.eq.injEq, true_and, heq_eq_eq] at h
  exact numeral_injective zero succ h

theorem exists_bound (Γ : List (ClosedFormula WithNew)) :
    ∃ N : ℕ, ∀ n, avoids n ∈ Γ → n < N := by
  induction Γ with
  | nil => exact ⟨0, fun n h => absurd h List.not_mem_nil⟩
  | cons ψ Γ ih =>
      obtain ⟨N, hN⟩ := ih
      by_cases h : ∃ n, ψ = avoids n
      · obtain ⟨n, rfl⟩ := h
        refine ⟨max N (n + 1), fun m hm => ?_⟩
        rcases List.mem_cons.mp hm with hm | hm
        · rw [avoids_injective hm]
          exact lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
        · exact lt_of_lt_of_le (hN m hm) (le_max_left _ _)
      · refine ⟨N, fun m hm => ?_⟩
        rcases List.mem_cons.mp hm with hm | hm
        · exact absurd ⟨m, hm.symm⟩ h
        · exact hN m hm

/-- The new constant in a model, as an individual. -/
def newOf (M : HenkinModel.{0, 0, w} Unit WithNew) : M.Carrier () := M.constDen .new

/-- The natural numbers, with the new constant read as `k`. -/
def natConstDen (k : ℕ) : {τ : Ty Unit} → WithNew τ → Ty.denote.{0, 0} (fun _ => ULift.{1} ℕ) τ
  | _, .old .zero => (⟨0⟩ : ULift.{1} ℕ)
  | _, .old .succ => fun n : ULift.{1} ℕ => (⟨n.down + 1⟩ : ULift.{1} ℕ)
  | _, .new => (⟨k⟩ : ULift.{1} ℕ)

/-- The standard model of the natural numbers with the new constant at `k`. -/
def natModelAt (k : ℕ) : HenkinModel.{0, 0, 0} Unit WithNew :=
  HenkinModel.standard (fun _ => ULift.{1} ℕ) (natConstDen k)

theorem natModelAt_iterate (k n : ℕ) :
    (succOf succ (natModelAt k))^[n] (zeroOf zero (natModelAt k)) = (⟨n⟩ : ULift.{1} ℕ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem natModelAt_axioms (k : ℕ) : ∀ ψ ∈ axioms zero succ, (natModelAt k).models ψ := by
  rw [models_axioms_iff]
  refine ⟨(models_zeroNotSucc _ _ _).mpr ?_, (models_succInjective _ _).mpr ?_,
    (models_induction _ _ _).mpr ?_⟩
  · intro x h
    exact Nat.succ_ne_zero x.down (congrArg ULift.down h)
  · intro x y h
    exact ULift.ext _ _ (Nat.succ_injective (congrArg ULift.down h))
  · intro p _ hzero hstep x
    obtain ⟨n⟩ := x
    induction n with
    | zero => exact hzero
    | succ n ih => exact hstep ⟨n⟩ ih

/-- A model satisfies `avoids n` exactly when the new constant is not the
`n`-th successor of zero. -/
theorem models_avoids (M : HenkinModel.{0, 0, w} Unit WithNew) (n : ℕ) :
    M.models (avoids n) ↔ newOf M ≠ (succOf succ M)^[n] (zeroOf zero M) := by
  change ¬ (newOf M = M.denote (numeral zero succ n) _) ↔ _
  rw [denote_numeral]

theorem natModelAt_avoids {k n : ℕ} (h : n ≠ k) : (natModelAt k).models (avoids n) := by
  rw [models_avoids, natModelAt_iterate]
  intro hEq
  exact h (congrArg ULift.down hEq).symm

theorem natModelAt_fullDomains (k : ℕ) : (natModelAt k).FullDomains :=
  HenkinModel.fullDomains_standard _ _

/-- Every finite part of the theory has a full model. -/
theorem finite_parts_have_full_models (Γ : List (ClosedFormula WithNew))
    (hΓ : ∀ ψ ∈ Γ, ψ ∈ theory) :
    ∃ M : HenkinModel.{0, 0, 0} Unit WithNew, M.FullDomains ∧ ∀ ψ ∈ Γ, M.models ψ := by
  obtain ⟨N, hN⟩ := exists_bound Γ
  refine ⟨natModelAt N, natModelAt_fullDomains N, fun ψ hψ => ?_⟩
  rcases hΓ ψ hψ with hAx | ⟨n, rfl⟩
  · exact natModelAt_axioms N ψ hAx
  · exact natModelAt_avoids (Nat.ne_of_lt (hN n hψ))

/-- A full model of the theory would interpret the new constant by a numeral,
since every individual of a full model of Peano's axioms is one. -/
theorem no_full_model (M : HenkinModel.{0, 0, w} Unit WithNew) (full : M.FullDomains) :
    ¬ ∀ ψ ∈ theory, M.models ψ := by
  intro hM
  let P := peanoStructure zero succ M full (fun ψ hψ => hM ψ (Set.mem_union_left _ hψ))
  obtain ⟨n, hn⟩ := P.fromNat_surjective (newOf M)
  have hIter : ∀ m : ℕ, P.fromNat m = (succOf succ M)^[m] (zeroOf zero M) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply', ← ih]
        rfl
  apply (models_avoids M n).mp (hM (avoids n) (Set.mem_union_right _ ⟨n, rfl⟩))
  rw [← hIter, hn]

/-- **Standard semantics is not compact.** Every finite part of the theory has
a full model; the theory has none. -/
theorem standard_not_compact :
    (∀ Γ : List (ClosedFormula WithNew), (∀ ψ ∈ Γ, ψ ∈ theory) →
      ∃ M : HenkinModel.{0, 0, 0} Unit WithNew, M.FullDomains ∧ ∀ ψ ∈ Γ, M.models ψ) ∧
    ¬ ∃ M : HenkinModel.{0, 0, 0} Unit WithNew, M.FullDomains ∧ ∀ ψ ∈ theory, M.models ψ :=
  ⟨finite_parts_have_full_models, fun ⟨M, full, hM⟩ => no_full_model M full hM⟩

/-- The theory has an extensional Henkin model, by compactness. -/
theorem exists_general_model :
    ∃ M : HenkinModel.{0, 0, 0} Unit WithNew, M.FunctionsRespectEqv ∧ ∀ ψ ∈ theory, M.models ψ := by
  refine compactness.{0, 0, 0} (fun _ => .const zero) (fun Γ hΓ => ?_)
  obtain ⟨M, full, hM⟩ := finite_parts_have_full_models Γ hΓ
  exact ⟨M, M.functionsRespectEqv_of_fullDomains full, hM⟩

/-- **Standard and general consequence differ.** The theory has no full model,
so it entails falsity in the standard sense; it has an extensional Henkin
model, so it does not in the general sense. -/
theorem consequence_differs :
    (∀ M : HenkinModel.{0, 0, 0} Unit WithNew, M.FullDomains → (∀ ψ ∈ theory, M.models ψ) →
      M.models .bot) ∧
    ¬ (∀ M : HenkinModel.{0, 0, 0} Unit WithNew, M.FunctionsRespectEqv →
      (∀ ψ ∈ theory, M.models ψ) → M.models .bot) := by
  refine ⟨fun M full hM => absurd hM (no_full_model M full), ?_⟩
  intro h
  obtain ⟨M, hExt, hM⟩ := exists_general_model
  exact HenkinModel.models_bot M (h M hExt hM)

/-- **No finitary calculus is strongly complete for standard semantics.**
Whatever relation `Der` between finite lists of sentences and sentences one
takes, "some finite part of `T` derives `φ`" cannot coincide with "`φ` holds in
every full model of `T`": the theory above would derive falsity from a finite
part, and that part has a full model. (Farmer's Theorem 4 is the weak form of
this, for one finite theory; it needs Gödel's incompleteness theorem.) -/
theorem no_strongly_complete_finitary_calculus
    (Der : List (ClosedFormula WithNew) → ClosedFormula WithNew → Prop) :
    ¬ ∀ (T : ClosedTheorySet WithNew) (φ : ClosedFormula WithNew),
      (∃ Γ : List (ClosedFormula WithNew), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Der Γ φ) ↔
        ∀ M : HenkinModel.{0, 0, 0} Unit WithNew, M.FullDomains →
          (∀ ψ ∈ T, M.models ψ) → M.models φ := by
  intro h
  obtain ⟨Γ, hΓ, hDer⟩ := (h theory .bot).mpr fun M full hM => absurd hM (no_full_model M full)
  have hΓbot := (h {ψ | ψ ∈ Γ} .bot).mp ⟨Γ, fun ψ hψ => hψ, hDer⟩
  obtain ⟨M, full, hM⟩ := finite_parts_have_full_models Γ hΓ
  exact HenkinModel.models_bot M (hΓbot M full fun ψ hψ => hM ψ hψ)

/-- Forget the new constant. -/
def forgetNew (M : HenkinModel.{0, 0, w} Unit WithNew) : HenkinModel.{0, 0, w} Unit PeanoConst :=
  HenkinModel.constantSubstitutionReduct (fun {_} c => .const (WithNew.old c)) M

theorem forgetNew_models (M : HenkinModel.{0, 0, w} Unit WithNew) (φ : ClosedFormula PeanoConst) :
    (forgetNew M).models φ ↔ M.models (mapConst (fun {_} c => WithNew.old c) φ) := by
  rw [forgetNew, ← HenkinModel.models_substConst, substConst_constant_images]

/-- **A nonstandard general model of Peano's axioms.** It is extensional,
satisfies the three axioms, has an individual that is no numeral, and is not
full. -/
theorem exists_nonstandard_model :
    ∃ M : HenkinModel.{0, 0, 0} Unit PeanoConst, M.FunctionsRespectEqv ∧
      (∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, M.models ψ) ∧
      (∃ x : M.Carrier (), ∀ n : ℕ,
        x ≠ (succOf PeanoConst.succ M)^[n] (zeroOf PeanoConst.zero M)) ∧
      ¬ M.FullDomains := by
  obtain ⟨M, hExt, hM⟩ := exists_general_model
  have hAx : ∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, (forgetNew M).models ψ := by
    intro ψ hψ
    rw [forgetNew_models]
    simp only [axioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
    rcases hψ with rfl | rfl | rfl
    · exact hM _ (Set.mem_union_left _ (Or.inl rfl))
    · exact hM _ (Set.mem_union_left _ (Or.inr (Or.inl rfl)))
    · exact hM _ (Set.mem_union_left _ (Or.inr (Or.inr rfl)))
  have hNew : ∀ n : ℕ, newOf M ≠ (succOf succ M)^[n] (zeroOf zero M) := fun n =>
    (models_avoids M n).mp (hM (avoids n) (Set.mem_union_right _ ⟨n, rfl⟩))
  refine ⟨forgetNew M, (HenkinModel.constantSubstitutionReduct_functionsRespectEqv_iff _ M).mpr hExt,
    hAx, ⟨newOf M, hNew⟩, ?_⟩
  intro full
  have hFull : M.FullDomains :=
    (HenkinModel.constantSubstitutionReduct_fullDomains_iff _ M).mp full
  exact no_full_model M hFull hM

/-- **General semantics is not categorical for Peano's axioms.** Some
extensional Henkin model of the axioms is not isomorphic to the natural
numbers, unlike every full model (`Peano.categorical`). -/
theorem not_categorical :
    ∃ M : HenkinModel.{0, 0, 0} Unit PeanoConst, M.FunctionsRespectEqv ∧
      (∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, M.models ψ) ∧
      ¬ ∃ e : M.Carrier () ≃ natModel.{0}.Carrier (),
        e (zeroOf PeanoConst.zero M) = zeroOf PeanoConst.zero natModel.{0} ∧
          ∀ x, e (succOf PeanoConst.succ M x) = succOf PeanoConst.succ natModel.{0} (e x) := by
  obtain ⟨M, hExt, hAx, ⟨x, hx⟩, _⟩ := exists_nonstandard_model
  refine ⟨M, hExt, hAx, ?_⟩
  rintro ⟨e, hzero, hsucc⟩
  have hIter : ∀ n : ℕ, e ((succOf PeanoConst.succ M)^[n] (zeroOf PeanoConst.zero M)) =
      (⟨n⟩ : ULift.{1} ℕ) := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
        rw [Function.iterate_succ_apply', hsucc, ih]
        rfl
  apply hx (e x).down
  apply e.injective
  rw [hIter]
  rfl

/-- **Skolem's paradox in simple type theory.** Peano's axioms have an
extensional Henkin model with countably many predicates up to extensional
equality; no full model of them has. -/
theorem exists_countable_peano_model :
    ∃ M : HenkinModel.{0, 0, 0} Unit PeanoConst, M.FunctionsRespectEqv ∧
      (∀ ψ ∈ axioms PeanoConst.zero PeanoConst.succ, M.models ψ) ∧
      CountableModEqv M (ι ⇒ .prop) ∧ ¬ M.FullDomains := by
  obtain ⟨M, hExt, hAx, _, hCount⟩ := exists_countable_model (T := axioms PeanoConst.zero PeanoConst.succ)
    (fun _ => .const PeanoConst.zero) ((consistent_iff_satisfiable (fun _ => .const PeanoConst.zero)
      _).mpr ⟨natModel.{0}, natModel.{0}.functionsRespectEqv_of_fullDomains
        (standardOf_fullDomains _), natModel_models⟩)
  refine ⟨M, hExt, hAx, hCount _, fun full => ?_⟩
  have : Infinite (M.Carrier ()) := infinite_of_models PeanoConst.zero PeanoConst.succ M
    (hAx _ (by simp [axioms])) (hAx _ (by simp [axioms]))
  exact not_countableModEqv_pred_of_full M full () (hCount _)

end Nonstandard

/-! ## A countable model of the complete ordered field -/

/-- **Farmer's Corollary 10.** The theory of the complete ordered field has an
extensional Henkin model with countably many individuals; it is not full,
since every full model is isomorphic to the real numbers. -/
theorem exists_countable_real_model :
    ∃ M : HenkinModel.{0, 0, 0} Unit OrderedField.FieldConst, M.FunctionsRespectEqv ∧
      (∀ ψ ∈ OrderedField.axioms, M.models ψ) ∧ Countable (M.Carrier ()) ∧ ¬ M.FullDomains := by
  have hCons : Consistent (Const := OrderedField.FieldConst)
      (insert excludedMiddle OrderedField.axioms) :=
    (consistent_iff_satisfiable (fun _ => .const OrderedField.FieldConst.zero) _).mpr
      ⟨OrderedField.realModel, OrderedField.realModel.functionsRespectEqv_of_fullDomains
        OrderedField.realModel_fullDomains, OrderedField.realModel_models⟩
  obtain ⟨M, hExt, hM, hCount, _⟩ :=
    exists_countable_model (fun _ => .const OrderedField.FieldConst.zero) hCons
  refine ⟨M, hExt, hM, hCount (), fun full => ?_⟩
  obtain ⟨e, -⟩ := OrderedField.full_model_is_real M full hM
  have : Countable (ULift.{1} ℝ) := by
    have := hCount ()
    exact Function.Surjective.countable (f := e) e.surjective
  have hReal : Countable ℝ := Function.Injective.countable (f := fun r : ℝ => (⟨r⟩ : ULift.{1} ℝ))
    (fun _ _ h => congrArg ULift.down h)
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hReal)

#print axioms compactness
#print axioms exists_countable_model
#print axioms not_countableModEqv_pred_of_full
#print axioms Nonstandard.standard_not_compact
#print axioms Nonstandard.consequence_differs
#print axioms Nonstandard.no_strongly_complete_finitary_calculus
#print axioms Nonstandard.exists_nonstandard_model
#print axioms Nonstandard.not_categorical
#print axioms Nonstandard.exists_countable_peano_model
#print axioms exists_countable_real_model

end Mettapedia.Logic.HOL.SevenVirtues
