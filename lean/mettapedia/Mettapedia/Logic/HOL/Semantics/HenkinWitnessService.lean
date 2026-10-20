import Mettapedia.Logic.HOL.Semantics.KripkeVaryingCanonical
import Mettapedia.GSLT.Dynamics.PriorityFairness

/-!
# Fair services of Henkin witness obligations

The canonical varying-domain Kripke model (`KripkeVarying.Canonical.model`) is
driven, at every parameter layer `ℓ`, by a `RawAlternatingStageScheduler ℓ`.
This file reads that scheduler as a fair *service* of two kinds of obligation,
and separates the effective part of the construction from the classical part.

## The service interface

`EligibleService eligible` is a schedule `serve : ℕ → α` with

* safety: the obligation served at time `t` is eligible at `t`;
* weak fairness relative to eligibility: an obligation that is eligible at
  every time from `start` on is served at some time `≥ start`.

The liveness clause is `PriorityFairness.Controls.WeaklyFair`, with the pending
sets of a run as eligibility (`EligibleService.ofWeaklyFair`,
`EligibleService.weaklyFair_of_serve_eq`).  With eligibility constantly true it
says that every obligation is served infinitely often (`always_fair`), the
fairness hypothesis of chaotic iteration.  When eligibility persists, weak
fairness yields service infinitely often (`served_infinitely_often`).

A service is a selection discipline.  Each service of a Henkin obligation is
one step of the stage construction, and that step decides provability; it is
not a budgeted computation.

## Henkin obligations

At layer `ℓ` there are two kinds of obligation.

* Existential bodies `⟨σ, φ⟩ : Body Const`.  At stage `s` a body is eligible
  when its parameters lie below layer `ℓ + 1` and, inside layer `ℓ`, below
  stage `s + 1` (`BodyEligible`).  The step at stage `s` witnesses the served
  existentials with fresh parameters of that stage.
* Disjunction pairs `ClosedFormulaPair Const`.  At time `n` a pair is eligible
  when its parameters lie below layer `ℓ + 1` and below stage `n`
  (`PairEligible`).  This eligibility persists, and every pair below layer
  `ℓ + 1` becomes eligible (`PairEligible.eventually`).

`WitnessService ℓ` packages one service of bodies per stage and one service of
pairs.  It is interconvertible with `RawAlternatingStageScheduler ℓ`
(`WitnessService.toScheduler`, `witnessServiceOfScheduler`, and the round trip
`toScheduler_witnessServiceOfScheduler`): the scheduler hypothesis of the
canonical construction is exactly a fair service of the Henkin obligations.

## Results

* `WitnessService.saturates`: a fair service at layer `ℓ` extends a theory
  below layer `ℓ + 1` that does not prove `θ` to a consistent world at level
  `ℓ + 1` that omits `θ` and is disjunction-prime and existentially witnessed
  for every formula below layer `ℓ + 1`.
* `provable_of_consequence_of_services`: varying-domain completeness from fair
  services at every layer, with no countability hypothesis.
* `witnessServiceOfEnumerations`, `schedulerProviderOfEnumerations`: fair
  services from enumerations of bodies and pairs.  Eligibility is decided by
  the structural parameter test `paramsAll` (`bodyEligible_iff`,
  `pairEligible_iff`).  The schedules `bodySchedule` and `pairSchedule` are
  computable from the enumerations and use no axioms; choice appears only in
  proofs of the service properties.
* `provable_of_consequence_of_enumerations`: completeness from such
  enumerations.

## Where classical reasoning enters

* Choosing the enumerations.  A countable signature has surjections from `ℕ`
  onto bodies and pairs (`exists_enumerations_of_countable`), and
  `schedulerProviderOfCountable` picks them with `Classical.choose`.  Given the
  enumerations, the schedule is computable.
* The stage construction (`rawAlternatingScheduledStageApprox`) decides at
  every step whether the current theory proves the served disjunction, and
  picks the extension with `Classical.choose`.  Provability is not decidable in
  general, so this part is classical for every schedule.
* The completeness theorems are proved by contradiction.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

/-! ## The service interface -/

/-- A schedule of obligations that serves only eligible obligations and is
weakly fair relative to eligibility. -/
structure EligibleService {α : Type w} (eligible : ℕ → α → Prop) where
  serve : ℕ → α
  safe : ∀ t, eligible t (serve t)
  live : ∀ x start, (∀ t, start ≤ t → eligible t x) → ∃ t, start ≤ t ∧ serve t = x

namespace EligibleService

open Mettapedia.GSLT.Dynamics.PriorityFairness

variable {α : Type w} {eligible : ℕ → α → Prop}

/-- When eligibility persists, an eligible obligation is served infinitely
often. -/
theorem served_infinitely_often (S : EligibleService eligible)
    (persist : ∀ {x : α} {s t : ℕ}, s ≤ t → eligible s x → eligible t x)
    {x : α} {s : ℕ} (hx : eligible s x) (N : ℕ) : ∃ n, N ≤ n ∧ S.serve n = x := by
  obtain ⟨t, ht, hserve⟩ := S.live x (max s N) fun t ht => persist (le_of_max_le_left ht) hx
  exact ⟨t, le_of_max_le_right ht, hserve⟩

/-- With eligibility constantly true, every obligation is served infinitely
often: the fairness hypothesis of chaotic iteration. -/
theorem always_fair (S : EligibleService (fun _ (_ : α) => True)) (x : α) (N : ℕ) :
    ∃ n, N ≤ n ∧ S.serve n = x :=
  S.served_infinitely_often (fun _ h => h) (s := 0) trivial N

/-- A schedule serving every obligation infinitely often is a service for
constantly true eligibility. -/
def ofFair (serve : ℕ → α) (fair : ∀ x N, ∃ n, N ≤ n ∧ serve n = x) :
    EligibleService (fun _ (_ : α) => True) where
  serve := serve
  safe _ := trivial
  live x start _ := fair x start

/-- A weakly fair run of a least-first scheduler is a service of its pending
items. -/
def ofWeaklyFair {β : Type w} [LinearOrder β] (run : Run β) (fair : Controls.WeaklyFair run) :
    EligibleService (fun t (x : β) => x ∈ run.pending t) where
  serve := run.fired
  safe := run.fired_mem
  live := fair

/-- Conversely, a run whose firing sequence is a service of its pending items is
weakly fair. -/
theorem weaklyFair_of_serve_eq {β : Type w} [LinearOrder β] (run : Run β)
    (S : EligibleService (fun t (x : β) => x ∈ run.pending t)) (h : S.serve = run.fired) :
    Controls.WeaklyFair run := by
  intro x start hx
  obtain ⟨t, ht, hs⟩ := S.live x start hx
  exact ⟨t, ht, h ▸ hs⟩

/-- Negative instance: the starving least-first run is not a service of its
pending items. -/
theorem starvingRun_not_service
    (S : EligibleService (fun t (x : ℕ) => x ∈ Controls.starvingRun.pending t)) :
    S.serve ≠ Controls.starvingRun.fired := fun h =>
  Controls.priority_not_weakly_fair (weaklyFair_of_serve_eq _ S h)

/-- Negative instance: a constant schedule over `Bool` is not fair. -/
theorem const_not_service (S : EligibleService (fun _ (_ : Bool) => True)) :
    S.serve ≠ fun _ => true := by
  intro h
  obtain ⟨n, -, hn⟩ := S.always_fair false 0
  rw [h] at hn
  exact Bool.noConfusion hn

/-- The schedule that visits an enumeration along the Cantor pairing and
serves `default` when the visited obligation fails the test at that time. -/
def enumSchedule (test : ℕ → α → Bool) (e : ℕ → α) (default : α) (n : ℕ) : α :=
  bif test n (e n.unpair.1) then e n.unpair.1 else default

/-- A service from an enumeration and a Boolean eligibility test, given an
obligation that is eligible at every time.  The schedule is `enumSchedule`. -/
def ofEnumeration (test : ℕ → α → Bool) (htest : ∀ t x, test t x = true ↔ eligible t x)
    (e : ℕ → α) (he : Function.Surjective e) (default : α)
    (hdefault : ∀ t, eligible t default) : EligibleService eligible where
  serve := enumSchedule test e default
  safe n := by
    unfold enumSchedule
    cases h : test n (e n.unpair.1) with
    | false => exact hdefault n
    | true => exact (htest _ _).mp h
  live x start hx := by
    obtain ⟨k, hk⟩ := he x
    refine ⟨Nat.pair k start, Nat.right_le_pair k start, ?_⟩
    have hu : e (Nat.pair k start).unpair.1 = x := by rw [Nat.unpair_pair, hk]
    have ht : test (Nat.pair k start) x = true :=
      (htest _ _).mpr (hx _ (Nat.right_le_pair k start))
    unfold enumSchedule
    rw [hu, ht]
    rfl

/-- Positive instance: round-robin over `Fin (k + 1)` through `ofEnumeration`
with constantly true eligibility. -/
example (k : ℕ) : EligibleService (fun _ (_ : Fin (k + 1)) => True) :=
  ofEnumeration (fun _ _ => true) (fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩)
    (fun n => (⟨n % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩ : Fin (k + 1)))
    (fun i => ⟨i.val, Fin.ext (Nat.mod_eq_of_lt i.isLt)⟩) 0 fun _ => trivial

end EligibleService

/-! ## A structural test for parameter occurrences -/

section ParamTest

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

/-- Whether every parameter index occurring in a term passes the test `good`. -/
def paramsAll (good : ℕ → Bool) {Γ : Ctx Base} {τ : Ty Base} :
    Term (WithParams Const) Γ τ → Bool
  | .var _ => true
  | .const d => Sum.elim (fun _ => true) good d
  | .app f t => paramsAll good f && paramsAll good t
  | .lam t => paramsAll good t
  | .top => true
  | .bot => true
  | .and a b => paramsAll good a && paramsAll good b
  | .or a b => paramsAll good a && paramsAll good b
  | .imp a b => paramsAll good a && paramsAll good b
  | .not a => paramsAll good a
  | .eq a b => paramsAll good a && paramsAll good b
  | .all a => paramsAll good a
  | .ex a => paramsAll good a

/-- Absence of every parameter whose index fails `good`. -/
def ParamsAvoid (good : ℕ → Bool) {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (WithParams Const) Γ τ) : Prop :=
  ∀ (σ : Ty Base) (k : ℕ), good k = false → NoConstOccurrence (param σ k) t

section Inversion

variable {K : Ty Base → Type v} {σ : Ty Base} {c : K σ} {Γ : Ctx Base}

theorem noConstOccurrence_app_iff {ρ τ : Ty Base} {f : Term K Γ (ρ ⇒ τ)} {t : Term K Γ ρ} :
    NoConstOccurrence c (.app f t) ↔ NoConstOccurrence c f ∧ NoConstOccurrence c t :=
  ⟨fun h => by cases h with | app hf ht => exact ⟨hf, ht⟩, fun h => .app h.1 h.2⟩

theorem noConstOccurrence_lam_iff {ρ τ : Ty Base} {t : Term K (ρ :: Γ) τ} :
    NoConstOccurrence c (.lam t) ↔ NoConstOccurrence c t :=
  ⟨fun h => by cases h with | lam ht => exact ht, fun h => .lam h⟩

theorem noConstOccurrence_and_iff {a b : Term K Γ propTy} :
    NoConstOccurrence c (.and a b) ↔ NoConstOccurrence c a ∧ NoConstOccurrence c b :=
  ⟨fun h => by cases h with | and ha hb => exact ⟨ha, hb⟩, fun h => .and h.1 h.2⟩

theorem noConstOccurrence_or_iff {a b : Term K Γ propTy} :
    NoConstOccurrence c (.or a b) ↔ NoConstOccurrence c a ∧ NoConstOccurrence c b :=
  ⟨fun h => by cases h with | or ha hb => exact ⟨ha, hb⟩, fun h => .or h.1 h.2⟩

theorem noConstOccurrence_imp_iff {a b : Term K Γ propTy} :
    NoConstOccurrence c (.imp a b) ↔ NoConstOccurrence c a ∧ NoConstOccurrence c b :=
  ⟨fun h => by cases h with | imp ha hb => exact ⟨ha, hb⟩, fun h => .imp h.1 h.2⟩

theorem noConstOccurrence_not_iff {a : Term K Γ propTy} :
    NoConstOccurrence c (.not a) ↔ NoConstOccurrence c a :=
  ⟨fun h => by cases h with | not ha => exact ha, fun h => .not h⟩

theorem noConstOccurrence_eq_iff {τ : Ty Base} {a b : Term K Γ τ} :
    NoConstOccurrence c (.eq a b) ↔ NoConstOccurrence c a ∧ NoConstOccurrence c b :=
  ⟨fun h => by cases h with | eq ha hb => exact ⟨ha, hb⟩, fun h => .eq h.1 h.2⟩

theorem noConstOccurrence_all_iff {ρ : Ty Base} {a : Term K (ρ :: Γ) propTy} :
    NoConstOccurrence c (.all a) ↔ NoConstOccurrence c a :=
  ⟨fun h => by cases h with | all ha => exact ha, fun h => .all h⟩

theorem noConstOccurrence_ex_iff {ρ : Ty Base} {a : Term K (ρ :: Γ) propTy} :
    NoConstOccurrence c (.ex a) ↔ NoConstOccurrence c a :=
  ⟨fun h => by cases h with | ex ha => exact ha, fun h => .ex h⟩

end Inversion

/-- The structural test decides parameter avoidance. -/
theorem paramsAll_eq_true_iff (good : ℕ → Bool) {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (WithParams Const) Γ τ) :
    paramsAll good t = true ↔ ParamsAvoid good t := by
  induction t with
  | var v => exact ⟨fun _ _ _ _ => .var, fun _ => rfl⟩
  | @const τ₁ Γ₁ d =>
      cases d with
      | inl c =>
          refine ⟨fun _ σ k _ => ?_, fun _ => rfl⟩
          by_cases hσ : σ = τ₁
          · subst hσ
            exact .const_same_ne (inj c) (inj_ne_param c k)
          · exact .const_diff_type hσ _
      | inr j =>
          show good j = true ↔ _
          constructor
          · intro hj σ k hk
            by_cases hσ : σ = τ₁
            · subst hσ
              refine .const_same_ne (param σ j) fun he => ?_
              rw [param_inj he] at hj
              rw [hj] at hk
              exact Bool.noConfusion hk
            · exact .const_diff_type hσ _
          · intro h
            cases hj : good j with
            | true => rfl
            | false =>
                have hno := h τ₁ j hj
                cases hno with
                | const_diff_type hne => exact absurd rfl hne
                | const_same_ne _ hne => exact absurd rfl hne
  | app f t ihf iht =>
      simp only [paramsAll, Bool.and_eq_true, ihf, iht, ParamsAvoid, noConstOccurrence_app_iff]
      exact ⟨fun h σ k hk => ⟨h.1 σ k hk, h.2 σ k hk⟩,
        fun h => ⟨fun σ k hk => (h σ k hk).1, fun σ k hk => (h σ k hk).2⟩⟩
  | lam t ih =>
      simp only [paramsAll, ih, ParamsAvoid, noConstOccurrence_lam_iff]
  | top => exact ⟨fun _ _ _ _ => .top, fun _ => rfl⟩
  | bot => exact ⟨fun _ _ _ _ => .bot, fun _ => rfl⟩
  | and a b iha ihb =>
      simp only [paramsAll, Bool.and_eq_true, iha, ihb, ParamsAvoid, noConstOccurrence_and_iff]
      exact ⟨fun h σ k hk => ⟨h.1 σ k hk, h.2 σ k hk⟩,
        fun h => ⟨fun σ k hk => (h σ k hk).1, fun σ k hk => (h σ k hk).2⟩⟩
  | or a b iha ihb =>
      simp only [paramsAll, Bool.and_eq_true, iha, ihb, ParamsAvoid, noConstOccurrence_or_iff]
      exact ⟨fun h σ k hk => ⟨h.1 σ k hk, h.2 σ k hk⟩,
        fun h => ⟨fun σ k hk => (h σ k hk).1, fun σ k hk => (h σ k hk).2⟩⟩
  | imp a b iha ihb =>
      simp only [paramsAll, Bool.and_eq_true, iha, ihb, ParamsAvoid, noConstOccurrence_imp_iff]
      exact ⟨fun h σ k hk => ⟨h.1 σ k hk, h.2 σ k hk⟩,
        fun h => ⟨fun σ k hk => (h σ k hk).1, fun σ k hk => (h σ k hk).2⟩⟩
  | not a ih =>
      simp only [paramsAll, ih, ParamsAvoid, noConstOccurrence_not_iff]
  | eq a b iha ihb =>
      simp only [paramsAll, Bool.and_eq_true, iha, ihb, ParamsAvoid, noConstOccurrence_eq_iff]
      exact ⟨fun h σ k hk => ⟨h.1 σ k hk, h.2 σ k hk⟩,
        fun h => ⟨fun σ k hk => (h σ k hk).1, fun σ k hk => (h σ k hk).2⟩⟩
  | all a ih =>
      simp only [paramsAll, ih, ParamsAvoid, noConstOccurrence_all_iff]
  | ex a ih =>
      simp only [paramsAll, ih, ParamsAvoid, noConstOccurrence_ex_iff]

end ParamTest

/-! ## Henkin obligations -/

namespace KripkeHenkin

namespace SupportedCanonicalFrame

open ClosedTheorySet Mettapedia.Logic.HOL.WithParams

variable {Base : Type u} {Const : Ty Base → Type v}

/-- An existential body is eligible at stage `s` of layer `ℓ` when its
parameters lie below layer `ℓ + 1` and, inside layer `ℓ`, below stage
`s + 1`. -/
def BodyEligible (ℓ s : ℕ) (b : Body Const) : Prop :=
  BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) b ∧
    BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1) b

/-- A disjunction pair is eligible at time `n` of layer `ℓ` when its parameters
lie below layer `ℓ + 1` and, inside layer `ℓ`, below stage `n`. -/
def PairEligible (ℓ n : ℕ) (p : ClosedFormulaPair Const) : Prop :=
  FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) p ∧
    FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ n p

theorem PairEligible.mono {ℓ n m : ℕ} {p : ClosedFormulaPair Const} (h : n ≤ m)
    (hp : PairEligible (Base := Base) ℓ n p) : PairEligible (Base := Base) ℓ m p :=
  ⟨hp.1, FormulaPairAvoidsParamStagesFromAt.mono h hp.2⟩

/-- Every pair below layer `ℓ + 1` becomes eligible: its stage support is
finite. -/
theorem PairEligible.eventually {ℓ : ℕ} {p : ClosedFormulaPair Const}
    (h : FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) p) :
    ∃ n, PairEligible (Base := Base) ℓ n p :=
  ⟨_, h, FormulaPairAvoidsParamStagesFromAt.of_maxParam ℓ p⟩

/-- A fair service of the Henkin obligations at layer `ℓ`: for every stage, a
service of the bodies eligible at that stage, and one service of disjunction
pairs with time-dependent eligibility. -/
structure WitnessService (ℓ : ℕ) where
  bodies : ∀ s : ℕ, EligibleService (fun _ (b : Body Const) => BodyEligible (Base := Base) ℓ s b)
  pairs : EligibleService (PairEligible (Base := Base) (Const := Const) ℓ)

/-- A fair service of the Henkin obligations is a raw alternating scheduler. -/
def WitnessService.toScheduler {ℓ : ℕ} (S : WitnessService (Base := Base) (Const := Const) ℓ) :
    RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ where
  body s := (S.bodies s).serve
  pair := S.pairs.serve
  body_fair s b hLayer hStage N :=
    (S.bodies s).served_infinitely_often (fun _ h => h) (s := 0) ⟨hLayer, hStage⟩ N
  body_layer s n := ((S.bodies s).safe n).1
  body_stage s n := ((S.bodies s).safe n).2
  pair_layer n := (S.pairs.safe n).1
  pair_stage n := (S.pairs.safe n).2
  pair_fair p hLayer N := by
    obtain ⟨_, h₀⟩ := PairEligible.eventually hLayer
    exact S.pairs.served_infinitely_often (fun hle h => PairEligible.mono hle h) h₀ N

/-- A raw alternating scheduler is a fair service of the Henkin obligations. -/
def witnessServiceOfScheduler {ℓ : ℕ}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ) :
    WitnessService (Base := Base) (Const := Const) ℓ where
  bodies s :=
    { serve := S.body s
      safe := fun n => ⟨S.body_layer s n, S.body_stage s n⟩
      live := fun b start hb => S.body_fair s b (hb start le_rfl).1 (hb start le_rfl).2 start }
  pairs :=
    { serve := S.pair
      safe := fun n => ⟨S.pair_layer n, S.pair_stage n⟩
      live := fun p start hp => S.pair_fair p (hp start le_rfl).1 start }

/-- The scheduler hypothesis is exactly a fair service: the round trip is the
identity. -/
theorem toScheduler_witnessServiceOfScheduler {ℓ : ℕ}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ) :
    (witnessServiceOfScheduler S).toScheduler = S := rfl

/-- A scheduler provider from fair services at every layer. -/
def schedulerProviderOfServices (S : ∀ ℓ, WitnessService (Base := Base) (Const := Const) ℓ) :
    SchedulerProvider (Base := Base) Const :=
  ⟨fun ℓ => (S ℓ).toScheduler⟩

theorem nonempty_schedulerProvider_iff_services :
    Nonempty (SchedulerProvider (Base := Base) Const) ↔
      Nonempty (∀ ℓ, WitnessService (Base := Base) (Const := Const) ℓ) :=
  ⟨fun ⟨P⟩ => ⟨fun ℓ => witnessServiceOfScheduler (P.scheduler ℓ)⟩,
    fun ⟨S⟩ => ⟨schedulerProviderOfServices S⟩⟩

/-! ## Saturation and completeness from a service -/

/-- **Saturation from a fair service.**  A theory below layer `ℓ + 1` that does
not prove `θ` extends to a consistent world at level `ℓ + 1` that omits `θ`
and is disjunction-prime and existentially witnessed for every formula below
layer `ℓ + 1`. -/
theorem WitnessService.saturates {ℓ : ℕ} (S : WitnessService (Base := Base) (Const := Const) ℓ)
    {T : ClosedTheorySet (WithParams Const)} {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ W : SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      W.level = ℓ + 1 ∧
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
      θ ∉ W.carrier ∧
      Consistent (Const := WithParams Const) W.carrier ∧
      (∀ {φ ψ : ClosedFormula (WithParams Const)},
        FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) (φ, ψ) →
        (.or φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier →
          φ ∈ W.carrier ∨ ψ ∈ W.carrier) ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
          (⟨σ, φ⟩ : Body Const) →
        (.ex φ : ClosedFormula (WithParams Const)) ∈ W.carrier →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t φ ∈ W.carrier) := by
  obtain ⟨W, hlev, hT, hθ⟩ :=
    exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) S.toScheduler hLayer hStage hθStage hNot
  refine ⟨W, hlev, hT, hθ, W.consistent, ?_, ?_⟩
  · intro φ ψ hp hor
    exact W.supported_prime_or (by rw [hlev]; exact hp) hor
  · intro σ φ hb hex
    exact W.supported_exists_witness (by rw [hlev]; exact hb) hex

/-- **Varying-domain completeness from fair services**, for a signature with a
closed term at every base type.  No countability hypothesis. -/
theorem provable_of_consequence_of_services
    (S : ∀ ℓ, WitnessService (Base := Base) (Const := Const) ℓ)
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : KripkeVarying.Consequence.{u, v, max u v} T θ) :
    ClosedTheorySet.Provable (Const := Const) T θ :=
  KripkeVarying.Canonical.provable_of_consequence_of_provider
    (schedulerProviderOfServices S) inhBase h

/-! ## Effective services from enumerations -/

/-- Parameter indices allowed for a body at stage `s` of layer `ℓ`. -/
def bodyGood (ℓ s k : ℕ) : Bool :=
  decide (k.unpair.1 ≤ ℓ ∧ (k.unpair.1 = ℓ → k.unpair.2.unpair.1 ≤ s))

/-- Parameter indices allowed for a pair at time `n` of layer `ℓ`. -/
def pairGood (ℓ n k : ℕ) : Bool :=
  decide (k.unpair.1 ≤ ℓ ∧ (k.unpair.1 = ℓ → k.unpair.2.unpair.1 < n))

/-- An index fails a support bound exactly when it lies in a forbidden layer or,
inside layer `ℓ`, in a forbidden stage. -/
theorem bad_index_cases (ℓ : ℕ) (P : ℕ → Prop) {k : ℕ}
    (hk : ¬ (k.unpair.1 ≤ ℓ ∧ (k.unpair.1 = ℓ → P k.unpair.2.unpair.1))) :
    (∃ m j, ℓ + 1 ≤ m ∧ k = Nat.pair m j) ∨
      ∃ r j, ¬ P r ∧ k = Nat.pair ℓ (Nat.pair r j) := by
  by_cases hm : k.unpair.1 ≤ ℓ
  · right
    have hmeq : k.unpair.1 = ℓ := by
      by_contra hne
      exact hk ⟨hm, fun h => absurd h hne⟩
    refine ⟨k.unpair.2.unpair.1, k.unpair.2.unpair.2, fun hP => hk ⟨hm, fun _ => hP⟩, ?_⟩
    rw [Nat.pair_unpair, ← hmeq, Nat.pair_unpair]
  · left
    exact ⟨k.unpair.1, k.unpair.2, by omega, (Nat.pair_unpair k).symm⟩

/-- Body eligibility is the structural parameter test. -/
theorem bodyEligible_iff (ℓ s : ℕ) (b : Body Const) :
    BodyEligible (Base := Base) ℓ s b ↔ paramsAll (bodyGood ℓ s) b.2 = true := by
  rw [paramsAll_eq_true_iff]
  constructor
  · rintro ⟨hL, hS⟩ σ k hk
    have hk' : ¬ (k.unpair.1 ≤ ℓ ∧ (k.unpair.1 = ℓ → k.unpair.2.unpair.1 ≤ s)) := by
      simpa [bodyGood] using hk
    rcases bad_index_cases ℓ (· ≤ s) hk' with ⟨m, j, hm, rfl⟩ | ⟨r, j, hr, rfl⟩
    · exact hL σ m j hm
    · exact hS σ r j (Nat.lt_of_not_le hr)
  · intro h
    refine ⟨fun σ m j hm => h σ _ ?_, fun σ r j hr => h σ _ ?_⟩
    · simp [bodyGood, Nat.unpair_pair]
      omega
    · simp [bodyGood, Nat.unpair_pair]
      omega

/-- Pair eligibility is the structural parameter test on both components. -/
theorem pairEligible_iff (ℓ n : ℕ) (p : ClosedFormulaPair Const) :
    PairEligible (Base := Base) ℓ n p ↔
      (paramsAll (pairGood ℓ n) p.1 && paramsAll (pairGood ℓ n) p.2) = true := by
  rw [Bool.and_eq_true, paramsAll_eq_true_iff, paramsAll_eq_true_iff]
  constructor
  · rintro ⟨hL, hS⟩
    have key : ∀ σ k, pairGood ℓ n k = false →
        NoConstOccurrence (param σ k) p.1 ∧ NoConstOccurrence (param σ k) p.2 := by
      intro σ k hk
      have hk' : ¬ (k.unpair.1 ≤ ℓ ∧ (k.unpair.1 = ℓ → k.unpair.2.unpair.1 < n)) := by
        simpa [pairGood] using hk
      rcases bad_index_cases ℓ (· < n) hk' with ⟨m, j, hm, rfl⟩ | ⟨r, j, hr, rfl⟩
      · exact hL σ m j hm
      · exact hS σ r j (Nat.le_of_not_lt hr)
    exact ⟨fun σ k hk => (key σ k hk).1, fun σ k hk => (key σ k hk).2⟩
  · rintro ⟨h₁, h₂⟩
    have hLayer : ∀ m j, ℓ + 1 ≤ m → pairGood ℓ n (Nat.pair m j) = false := by
      intro m j hm
      simp [pairGood, Nat.unpair_pair]
      omega
    have hStage : ∀ r j, n ≤ r → pairGood ℓ n (Nat.pair ℓ (Nat.pair r j)) = false := by
      intro r j hr
      simp [pairGood, Nat.unpair_pair]
      omega
    exact ⟨fun σ m j hm => ⟨h₁ σ _ (hLayer m j hm), h₂ σ _ (hLayer m j hm)⟩,
      fun σ r j hr => ⟨h₁ σ _ (hStage r j hr), h₂ σ _ (hStage r j hr)⟩⟩

/-- The Boolean test for body eligibility at stage `s` of layer `ℓ`. -/
def bodyTest (ℓ s : ℕ) (_ : ℕ) (b : Body Const) : Bool :=
  paramsAll (bodyGood ℓ s) b.2

/-- The Boolean test for pair eligibility at time `n` of layer `ℓ`. -/
def pairTest (ℓ n : ℕ) (p : ClosedFormulaPair Const) : Bool :=
  paramsAll (pairGood ℓ n) p.1 && paramsAll (pairGood ℓ n) p.2

/-- The body schedule at stage `s` of layer `ℓ`, computed from an enumeration of
all bodies. -/
def bodySchedule (e : ℕ → Body Const) (ℓ s : ℕ) : ℕ → Body Const :=
  EligibleService.enumSchedule (bodyTest ℓ s) e defaultBody

/-- The pair schedule of layer `ℓ`, computed from an enumeration of all pairs. -/
def pairSchedule (q : ℕ → ClosedFormulaPair Const) (ℓ : ℕ) : ℕ → ClosedFormulaPair Const :=
  EligibleService.enumSchedule (pairTest ℓ) q defaultPair

/-- The service of the bodies eligible at stage `s`, from an enumeration of
all bodies.  Its schedule is `bodySchedule`. -/
def bodyServiceOfEnumeration (e : ℕ → Body Const) (he : Function.Surjective e) (ℓ s : ℕ) :
    EligibleService (fun _ (b : Body Const) => BodyEligible (Base := Base) ℓ s b) :=
  EligibleService.ofEnumeration (bodyTest ℓ s) (fun _ b => (bodyEligible_iff ℓ s b).symm)
    e he defaultBody fun _ => ⟨defaultBody_layers _, defaultBody_stages _ _⟩

/-- The service of disjunction pairs, from an enumeration of all pairs.  Its
schedule is `pairSchedule`. -/
def pairServiceOfEnumeration (q : ℕ → ClosedFormulaPair Const) (hq : Function.Surjective q)
    (ℓ : ℕ) : EligibleService (PairEligible (Base := Base) (Const := Const) ℓ) :=
  EligibleService.ofEnumeration (pairTest ℓ) (fun n p => (pairEligible_iff ℓ n p).symm)
    q hq defaultPair fun _ => ⟨defaultPair_layers _, defaultPair_stages _ _⟩

theorem bodyServiceOfEnumeration_serve (e : ℕ → Body Const) (he : Function.Surjective e)
    (ℓ s : ℕ) : (bodyServiceOfEnumeration e he ℓ s).serve = bodySchedule e ℓ s := rfl

theorem pairServiceOfEnumeration_serve (q : ℕ → ClosedFormulaPair Const)
    (hq : Function.Surjective q) (ℓ : ℕ) :
    (pairServiceOfEnumeration q hq ℓ).serve = pairSchedule q ℓ := rfl

/-- **Effective fair service of the Henkin obligations** from enumerations of
bodies and pairs. -/
def witnessServiceOfEnumerations (e : ℕ → Body Const) (he : Function.Surjective e)
    (q : ℕ → ClosedFormulaPair Const) (hq : Function.Surjective q) (ℓ : ℕ) :
    WitnessService (Base := Base) (Const := Const) ℓ :=
  ⟨bodyServiceOfEnumeration e he ℓ, pairServiceOfEnumeration q hq ℓ⟩

/-- A scheduler provider computed from enumerations of bodies and pairs. -/
def schedulerProviderOfEnumerations (e : ℕ → Body Const) (he : Function.Surjective e)
    (q : ℕ → ClosedFormulaPair Const) (hq : Function.Surjective q) :
    SchedulerProvider (Base := Base) Const :=
  schedulerProviderOfServices (witnessServiceOfEnumerations e he q hq)

/-- **Varying-domain completeness from enumerations** of bodies and pairs, for
a signature with a closed term at every base type. -/
theorem provable_of_consequence_of_enumerations
    (e : ℕ → Body Const) (he : Function.Surjective e)
    (q : ℕ → ClosedFormulaPair Const) (hq : Function.Surjective q)
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : KripkeVarying.Consequence.{u, v, max u v} T θ) :
    ClosedTheorySet.Provable (Const := Const) T θ :=
  provable_of_consequence_of_services (witnessServiceOfEnumerations e he q hq) inhBase h

/-- Enumerations exist for countable signatures; choosing them is the only
use of choice on the scheduling side. -/
theorem exists_enumerations_of_countable [Countable Base] [∀ τ, Countable (Const τ)] :
    (∃ e : ℕ → Body Const, Function.Surjective e) ∧
      ∃ q : ℕ → ClosedFormulaPair Const, Function.Surjective q :=
  have : Nonempty (Body Const) := ⟨defaultBody⟩
  have : Nonempty (ClosedFormulaPair Const) := ⟨defaultPair⟩
  ⟨exists_surjective_nat _, exists_surjective_nat _⟩

/-- Enumerations of bodies and pairs exist exactly for countable signatures. -/
theorem nonempty_enumerations_iff :
    ((∃ e : ℕ → Body Const, Function.Surjective e) ∧
      ∃ q : ℕ → ClosedFormulaPair Const, Function.Surjective q) ↔
      Countable Base ∧ ∀ σ, Countable (Const σ) := by
  constructor
  · rintro ⟨⟨e, he⟩, ⟨q, hq⟩⟩
    exact (nonempty_schedulerProvider_iff (Base := Base) (Const := Const)).mp
      ⟨schedulerProviderOfEnumerations e he q hq⟩
  · rintro ⟨_, _⟩
    exact exists_enumerations_of_countable

/-- Positive instance: the countable signature `EmptySig` has fair services. -/
theorem emptySig_witnessServices :
    Nonempty (∀ ℓ, WitnessService (Base := Unit) (Const := EmptySig) ℓ) :=
  nonempty_schedulerProvider_iff_services.mp emptySig_schedulerProvider

/-- Negative instance: the uncountable signature `RealSig` has no fair service
of its Henkin obligations. -/
theorem isEmpty_witnessServices_realSig :
    IsEmpty (∀ ℓ, WitnessService (Base := Unit) (Const := RealSig) ℓ) :=
  ⟨fun S => realSig_no_schedulerProvider.false (schedulerProviderOfServices S)⟩

/-- Positive instance: completeness from fair services for the one-point
signature, whose services come from enumerations. -/
theorem pointConst_provable_of_consequence
    {T : ClosedTheorySet KripkeVarying.Canonical.PointConst}
    {θ : ClosedFormula KripkeVarying.Canonical.PointConst}
    (h : KripkeVarying.Consequence.{0, 0, 0} T θ) :
    ClosedTheorySet.Provable (Const := KripkeVarying.Canonical.PointConst) T θ := by
  obtain ⟨⟨e, he⟩, ⟨q, hq⟩⟩ :=
    exists_enumerations_of_countable (Base := Unit) (Const := KripkeVarying.Canonical.PointConst)
  exact provable_of_consequence_of_enumerations e he q hq
    KripkeVarying.Canonical.pointInhabitant h

open KripkeVarying.Canonical in
/-- Positive control: completeness from fair services, with the services read
off the scheduler provider of the countable one-point signature. -/
theorem pointExistsEqO_provable_of_services :
    ClosedTheorySet.Provable (Const := PointConst) ∅ pointExistsEqO :=
  provable_of_consequence_of_services
    (fun ℓ => witnessServiceOfScheduler
      ((schedulerProviderOfCountable (Base := Unit) (Const := PointConst)).scheduler ℓ))
    pointInhabitant pointExistsEqO_consequence

open KripkeVarying.Canonical in
/-- Positive control: completeness from enumerations, chosen for the countable
one-point signature. -/
theorem pointExistsEqO_provable_of_enumerations :
    ClosedTheorySet.Provable (Const := PointConst) ∅ pointExistsEqO :=
  provable_of_consequence_of_enumerations
    (Classical.choose (exists_enumerations_of_countable (Base := Unit) (Const := PointConst)).1)
    (Classical.choose_spec
      (exists_enumerations_of_countable (Base := Unit) (Const := PointConst)).1)
    (Classical.choose (exists_enumerations_of_countable (Base := Unit) (Const := PointConst)).2)
    (Classical.choose_spec
      (exists_enumerations_of_countable (Base := Unit) (Const := PointConst)).2)
    pointInhabitant pointExistsEqO_consequence

open KripkeVarying.Canonical in
/-- Positive control: a fair service saturates the empty theory into a world at
level `1` that omits the constant-domain sentence. -/
theorem pointConst_saturated_world_omits_constantDomain :
    ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Unit) PointConst,
      W.level = 1 ∧
        (constantDomain (.base ()) : ClosedFormula (WithParams PointConst)) ∉ W.carrier := by
  obtain ⟨W, hlev, -, hθ, -⟩ :=
    WitnessService.saturates
      (witnessServiceOfScheduler
        ((schedulerProviderOfCountable (Base := Unit) (Const := PointConst)).scheduler 0))
      (T := ∅) (θ := constantDomain (.base ()))
      (fun _ h => h.elim) (fun _ h => h.elim)
      (fun _ _ _ _ => noConstOccurrence_constantDomain _ _)
      (constantDomain_not_provable (Const := WithParams PointConst) ())
  exact ⟨W, hlev, hθ⟩

end SupportedCanonicalFrame

end KripkeHenkin

end Mettapedia.Logic.HOL
