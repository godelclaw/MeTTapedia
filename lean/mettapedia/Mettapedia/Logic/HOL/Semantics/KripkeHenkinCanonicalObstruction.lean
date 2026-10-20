import Mathlib.Analysis.Real.Cardinality
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonical
import Mettapedia.Logic.HOL.Semantics.ConstantDomain
import Mettapedia.Logic.HOL.SevenVirtues.Completeness

/-!
# The hypotheses of the conditional Kripke completeness theorems

`KripkeHenkinCanonical` once derived Kripke-Henkin completeness from two
hypothesis packages: a `SchedulerProvider` (fair enumerations driving the raw
prime extension) and local membership clauses for disjunction and the
existential (`LocalMembershipClauses`, `LevelLocalMembershipClauses`, or a
`FullPresentedUpgrade`).  This file settles both packages.

* A scheduler provider exists exactly when the base types and the constants
  are countable (`nonempty_schedulerProvider_iff`).
* Over any signature with a base type, a scheduler provider and local
  membership clauses never coexist.  Together they would make the supported
  presented worlds a constant-domain `KripkeHenkin` structure, which forces the
  constant-domain sentence at every world (`ConstantDomain`), while some
  supported presented world omits it (`exists_world_not_mem_constantDomain`).
  So for countable signatures with a base type there are no local membership
  clauses and no full-presented upgrade, and for uncountable signatures there
  is no scheduler provider.

Consequently every theorem that assumed both packages had hypotheses that no
signature with a base type satisfies.  Those theorems were removed from
`KripkeHenkinCanonical` on 2026-10-20; that module's docstring lists them.
The supported-membership theorems that assume only a scheduler provider are
not affected; they are about deductively closed theories, not about a model
class.
-/

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin

namespace SupportedCanonicalFrame

open ClosedTheorySet

/-! ## Scheduler providers for countable signatures -/

/-- The body `⊤`, which mentions no parameter. -/
def defaultBody : Body Const := ⟨.prop, .top⟩

/-- The pair `(⊤, ⊤)`, which mentions no parameter. -/
def defaultPair : ClosedFormulaPair Const := (.top, .top)

theorem defaultBody_layers (ℓ : Nat) :
    BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) ℓ defaultBody :=
  fun _ _ _ _ => .top

theorem defaultBody_stages (ℓ s : Nat) :
    BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s defaultBody :=
  fun _ _ _ _ => .top

theorem defaultPair_layers (ℓ : Nat) :
    FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) ℓ defaultPair :=
  fun _ _ _ _ => ⟨.top, .top⟩

theorem defaultPair_stages (ℓ s : Nat) :
    FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s defaultPair :=
  fun _ _ _ _ => ⟨.top, .top⟩

open Classical in
/-- Stage `s` body enumeration: the `n.unpair.1`-th body of a surjection when
its support fits the stage, and `⊤` otherwise. -/
noncomputable def stageBody (e : Nat → Body Const) (ℓ s n : Nat) : Body Const :=
  if BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) (e n.unpair.1) ∧
      BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1) (e n.unpair.1)
  then e n.unpair.1 else defaultBody

open Classical in
/-- Pair schedule: the `n.unpair.1`-th pair of a surjection when its support
fits stage `n`, and `(⊤, ⊤)` otherwise. -/
noncomputable def stagePair (q : Nat → ClosedFormulaPair Const) (ℓ n : Nat) :
    ClosedFormulaPair Const :=
  if FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) (q n.unpair.1) ∧
      FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ n (q n.unpair.1)
  then q n.unpair.1 else defaultPair

/-- A raw alternating scheduler built from surjections onto bodies and pairs. -/
noncomputable def schedulerOfSurjective (e : Nat → Body Const) (he : Function.Surjective e)
    (q : Nat → ClosedFormulaPair Const) (hq : Function.Surjective q) (ℓ : Nat) :
    RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ where
  body := stageBody e ℓ
  pair := stagePair q ℓ
  body_fair := by
    intro s b hLayer hStage N
    obtain ⟨k, hk⟩ := he b
    refine ⟨Nat.pair k N, Nat.right_le_pair k N, ?_⟩
    have hu : e (Nat.pair k N).unpair.1 = b := by rw [Nat.unpair_pair, hk]
    unfold stageBody
    rw [hu]
    exact if_pos ⟨hLayer, hStage⟩
  body_layer := by
    intro s n
    show BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) (stageBody e ℓ s n)
    unfold stageBody
    split_ifs with h
    · exact h.1
    · exact defaultBody_layers _
  body_stage := by
    intro s n
    show BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1)
      (stageBody e ℓ s n)
    unfold stageBody
    split_ifs with h
    · exact h.2
    · exact defaultBody_stages _ _
  pair_layer := by
    intro n
    show FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
      (stagePair q ℓ n)
    unfold stagePair
    split_ifs with h
    · exact h.1
    · exact defaultPair_layers _
  pair_stage := by
    intro n
    show FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ n
      (stagePair q ℓ n)
    unfold stagePair
    split_ifs with h
    · exact h.2
    · exact defaultPair_stages _ _
  pair_fair := by
    intro p hLayer N
    obtain ⟨k, hk⟩ := hq p
    let s₀ := max (maxParam p.1) (maxParam p.2)
    refine ⟨Nat.pair k (max N s₀), Nat.le_trans (le_max_left N s₀) (Nat.right_le_pair _ _), ?_⟩
    have hStage : FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ
        (Nat.pair k (max N s₀)) p :=
      FormulaPairAvoidsParamStagesFromAt.mono
        (Nat.le_trans (le_max_right N s₀) (Nat.right_le_pair _ _))
        (FormulaPairAvoidsParamStagesFromAt.of_maxParam ℓ p)
    have hu : q (Nat.pair k (max N s₀)).unpair.1 = p := by rw [Nat.unpair_pair, hk]
    unfold stagePair
    rw [hu]
    exact if_pos ⟨hLayer, hStage⟩

/-- **A scheduler provider exists for every countable signature.** -/
noncomputable def schedulerProviderOfCountable [Countable Base] [∀ τ, Countable (Const τ)] :
    SchedulerProvider (Base := Base) Const :=
  have hBody : ∃ e : Nat → Body Const, Function.Surjective e :=
    have : Nonempty (Body Const) := ⟨defaultBody⟩
    exists_surjective_nat _
  have hPair : ∃ q : Nat → ClosedFormulaPair Const, Function.Surjective q :=
    have : Nonempty (ClosedFormulaPair Const) := ⟨defaultPair⟩
    exists_surjective_nat _
  { scheduler := schedulerOfSurjective (Classical.choose hBody) (Classical.choose_spec hBody)
      (Classical.choose hPair) (Classical.choose_spec hPair) }

/-! ## A scheduler provider forces countability -/

/-- A scheduler provider enumerates the pair `(c = c, ⊤)` for every constant
`c`, so every constant type is countable. -/
theorem SchedulerProvider.countable_const (P : SchedulerProvider (Base := Base) Const)
    (σ : Ty Base) : Countable (Const σ) := by
  classical
  let code : Const σ → ClosedFormulaPair Const := fun c =>
    ((.eq (.const (inj c)) (.const (inj c)) : ClosedFormula (WithParams Const)), .top)
  have hLayer : ∀ c, FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const)
      1 (code c) := fun c σ' m k _ =>
    ⟨noConstOccurrence_param_of_ge _ _ (Nat.zero_le _), .top⟩
  have hHit : ∀ c, ∃ n, (P.scheduler 0).pair n = code c := fun c => by
    obtain ⟨n, _, hn⟩ := (P.scheduler 0).pair_fair (code c) (hLayer c) 0
    exact ⟨n, hn⟩
  refine Function.Injective.countable (f := fun c => Nat.find (hHit c)) ?_
  intro c c' h
  have hc := Nat.find_spec (hHit c)
  have hc' := Nat.find_spec (hHit c')
  simp only at h
  rw [h] at hc
  have hcode : code c = code c' := hc.symm.trans hc'
  have hfst := congrArg Prod.fst hcode
  simp only [code, Term.eq.injEq, and_self] at hfst
  have hconst := eq_of_heq hfst.2
  simp only [Term.const.injEq, inj, Sum.inl.injEq] at hconst
  exact hconst

/-- A scheduler provider enumerates `(∀ x : b. ⊤, ⊤)` for every base type `b`,
so the base types are countable. -/
theorem SchedulerProvider.countable_base (P : SchedulerProvider (Base := Base) Const) :
    Countable Base := by
  classical
  let code : Base → ClosedFormulaPair Const := fun b =>
    ((.all (σ := .base b) .top : ClosedFormula (WithParams Const)), .top)
  have hLayer : ∀ b, FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const)
      1 (code b) := fun _ _ _ _ _ => ⟨.all .top, .top⟩
  have hHit : ∀ b, ∃ n, (P.scheduler 0).pair n = code b := fun b => by
    obtain ⟨n, _, hn⟩ := (P.scheduler 0).pair_fair (code b) (hLayer b) 0
    exact ⟨n, hn⟩
  refine Function.Injective.countable (f := fun b => Nat.find (hHit b)) ?_
  intro b b' h
  have hb := Nat.find_spec (hHit b)
  have hb' := Nat.find_spec (hHit b')
  simp only at h
  rw [h] at hb
  have hcode : code b = code b' := hb.symm.trans hb'
  simp only [code, Prod.mk.injEq, and_true] at hcode
  injection hcode with hσ
  injection hσ

/-- **Scheduler providers exist exactly for countable signatures.** -/
theorem nonempty_schedulerProvider_iff :
    Nonempty (SchedulerProvider (Base := Base) Const) ↔
      Countable Base ∧ ∀ σ, Countable (Const σ) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.countable_base, P.countable_const⟩
  · rintro ⟨hB, hC⟩
    exact ⟨schedulerProviderOfCountable⟩

/-! ## Local membership clauses contradict a scheduler provider -/

/-- Some supported presented world omits the constant-domain sentence, which is
not derivable. -/
theorem exists_world_not_mem_constantDomain (P : SchedulerProvider (Base := Base) Const)
    (b : Base) :
    ∃ W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      (constantDomain (.base b) : ClosedFormula (WithParams Const)) ∉ W.carrier := by
  obtain ⟨W, -, -, hW⟩ :=
    exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := 0) (T := ∅)
      (θ := (constantDomain (.base b) : ClosedFormula (WithParams Const)))
      (P.scheduler 0) (fun _ h => h.elim) (fun _ h => h.elim)
      (fun _ _ _ _ => noConstOccurrence_constantDomain _ _)
      (constantDomain_not_provable (Const := WithParams Const) b)
  exact ⟨W, hW⟩

/-- With a scheduler provider, local membership clauses would make the
supported presented worlds a constant-domain `KripkeHenkin` structure, which
forces the constant-domain sentence everywhere; some world omits it. -/
theorem isEmpty_localMembershipClauses (P : SchedulerProvider (Base := Base) Const)
    (b : Base) : IsEmpty (LocalMembershipClauses (Base := Base) Const) := by
  refine ⟨fun L => ?_⟩
  let K : KripkeHenkin Base (WithParams Const) :=
    { World := ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const
      le := Le (Base := Base) (Const := Const)
      le_refl := le_refl (Base := Base) (Const := Const)
      le_trans := fun hUV hVW => le_trans (Base := Base) (Const := Const) hUV hVW
      atom := Atom (Base := Base) (Const := Const)
      atom_mono := fun hWV hφ => atom_mono (Base := Base) (Const := Const) hWV hφ
      eqVal := fun W s t => EqVal (Base := Base) (Const := Const) W s t
      eq_mono := fun hWV hst => eqVal_mono (Base := Base) (Const := Const) hWV hst
      eq_refl := fun W t => eq_refl (Base := Base) (Const := Const) W t
      eq_symm := fun hst => eq_symm (Base := Base) (Const := Const) hst
      eq_trans := fun hrs hst => eq_trans (Base := Base) (Const := Const) hrs hst
      eq_app_congr := fun hfg hst => eq_app_congr (Base := Base) (Const := Const) hfg hst
      eq_funext := fun hpoint => eq_funext (Base := Base) (Const := Const) hpoint
      eq_beta := fun t u => eq_beta (Base := Base) (Const := Const) _ t u
      eq_eta := fun f => eq_eta (Base := Base) (Const := Const) _ f
      forces := Forces (Base := Base) (Const := Const)
      forces_mono := fun hWV hφ => forces_mono (Base := Base) (Const := Const) hWV hφ
      forces_atom_const := fun c => forces_atom_const (Base := Base) (Const := Const) _ c
      forces_atom_app := fun f t => forces_atom_app (Base := Base) (Const := Const) _ f t
      forces_top := forces_top (Base := Base) (Const := Const) _
      forces_bot := forces_bot (Base := Base) (Const := Const) _
      forces_and := forces_and (Base := Base) (Const := Const)
      forces_or := L.or_clause
      forces_imp := forces_imp_provider (Base := Base) (Const := Const) P _
      forces_not := forces_not_provider (Base := Base) (Const := Const) P _
      forces_eq := forces_eq (Base := Base) (Const := Const)
      eq_prop_intro := fun hpq hqp =>
        SupportedCanonicalMembership.eq_prop_intro_mem (Base := Base) (Const := Const) hpq hqp
      eq_prop_elim_left := fun hpq =>
        SupportedCanonicalMembership.eq_prop_elim_left_mem (Base := Base) (Const := Const) hpq
      eq_prop_elim_right := fun hpq =>
        SupportedCanonicalMembership.eq_prop_elim_right_mem (Base := Base) (Const := Const) hpq
      forces_all := forces_all_provider (Base := Base) (Const := Const) P _
      forces_ex := L.ex_clause }
  obtain ⟨W, hW⟩ := exists_world_not_mem_constantDomain P b
  exact hW (KripkeHenkin.forces_constantDomain K W (.base b))

/-- The level-aware local membership clauses fail in the same way, with the
level-growing preorder. -/
theorem isEmpty_levelLocalMembershipClauses (P : SchedulerProvider (Base := Base) Const)
    (b : Base) : IsEmpty (LevelLocalMembershipClauses (Base := Base) Const) := by
  refine ⟨fun L => ?_⟩
  let K : KripkeHenkin Base (WithParams Const) :=
    { World := ClosedTheorySet.SupportedPresentedIntuitionisticWorld (Base := Base) Const
      le := LevelLe (Base := Base) (Const := Const)
      le_refl := levelLe_refl (Base := Base) (Const := Const)
      le_trans := fun hUV hVW => levelLe_trans (Base := Base) (Const := Const) hUV hVW
      atom := Atom (Base := Base) (Const := Const)
      atom_mono := fun hWV hφ => atom_mono (Base := Base) (Const := Const) hWV.2 hφ
      eqVal := fun W s t => EqVal (Base := Base) (Const := Const) W s t
      eq_mono := fun hWV hst => eqVal_mono (Base := Base) (Const := Const) hWV.2 hst
      eq_refl := fun W t => eq_refl (Base := Base) (Const := Const) W t
      eq_symm := fun hst => eq_symm (Base := Base) (Const := Const) hst
      eq_trans := fun hrs hst => eq_trans (Base := Base) (Const := Const) hrs hst
      eq_app_congr := fun hfg hst => eq_app_congr (Base := Base) (Const := Const) hfg hst
      eq_funext := fun hpoint => eq_funext (Base := Base) (Const := Const) hpoint
      eq_beta := fun t u => eq_beta (Base := Base) (Const := Const) _ t u
      eq_eta := fun f => eq_eta (Base := Base) (Const := Const) _ f
      forces := Forces (Base := Base) (Const := Const)
      forces_mono := fun hWV hφ => forces_mono (Base := Base) (Const := Const) hWV.2 hφ
      forces_atom_const := fun c => forces_atom_const (Base := Base) (Const := Const) _ c
      forces_atom_app := fun f t => forces_atom_app (Base := Base) (Const := Const) _ f t
      forces_top := forces_top (Base := Base) (Const := Const) _
      forces_bot := forces_bot (Base := Base) (Const := Const) _
      forces_and := forces_and (Base := Base) (Const := Const)
      forces_or := L.or_clause
      forces_imp := forces_imp_level_provider (Base := Base) (Const := Const) P _
      forces_not := forces_not_level_provider (Base := Base) (Const := Const) P _
      forces_eq := forces_eq (Base := Base) (Const := Const)
      eq_prop_intro := fun hpq hqp =>
        SupportedCanonicalMembership.eq_prop_intro_mem (Base := Base) (Const := Const) hpq hqp
      eq_prop_elim_left := fun hpq =>
        SupportedCanonicalMembership.eq_prop_elim_left_mem (Base := Base) (Const := Const) hpq
      eq_prop_elim_right := fun hpq =>
        SupportedCanonicalMembership.eq_prop_elim_right_mem (Base := Base) (Const := Const) hpq
      forces_all := forces_all_level_provider (Base := Base) (Const := Const) P _
      forces_ex := L.ex_clause }
  obtain ⟨W, hW⟩ := exists_world_not_mem_constantDomain P b
  exact hW (KripkeHenkin.forces_constantDomain K W (.base b))

/-- A full-presented upgrade fails in the same way. -/
theorem isEmpty_fullPresentedUpgrade (P : SchedulerProvider (Base := Base) Const)
    (b : Base) : IsEmpty (FullPresentedUpgrade (Base := Base) Const) :=
  ⟨fun U => (isEmpty_localMembershipClauses P b).false
    (U.toLocalMembershipClauses (Base := Base))⟩

/-- **The conditional Kripke completeness hypotheses are unsatisfiable** over
every signature with a base type: a scheduler provider and local membership
clauses never coexist. -/
theorem not_schedulerProvider_and_localMembershipClauses (b : Base) :
    ¬ (Nonempty (SchedulerProvider (Base := Base) Const) ∧
      Nonempty (LocalMembershipClauses (Base := Base) Const)) := by
  rintro ⟨⟨P⟩, ⟨L⟩⟩
  exact (isEmpty_localMembershipClauses P b).false L

/-- The level-aware form of the same unsatisfiability. -/
theorem not_schedulerProvider_and_levelLocalMembershipClauses (b : Base) :
    ¬ (Nonempty (SchedulerProvider (Base := Base) Const) ∧
      Nonempty (LevelLocalMembershipClauses (Base := Base) Const)) := by
  rintro ⟨⟨P⟩, ⟨L⟩⟩
  exact (isEmpty_levelLocalMembershipClauses P b).false L

/-- The upgrade form of the same unsatisfiability. -/
theorem not_schedulerProvider_and_fullPresentedUpgrade (b : Base) :
    ¬ (Nonempty (SchedulerProvider (Base := Base) Const) ∧
      Nonempty (FullPresentedUpgrade (Base := Base) Const)) := by
  rintro ⟨⟨P⟩, ⟨U⟩⟩
  exact (isEmpty_fullPresentedUpgrade P b).false U

/-- For a countable signature with a base type there is no full-presented
upgrade. -/
theorem isEmpty_fullPresentedUpgrade_of_countable [Countable Base]
    [∀ τ, Countable (Const τ)] (b : Base) :
    IsEmpty (FullPresentedUpgrade (Base := Base) Const) :=
  isEmpty_fullPresentedUpgrade schedulerProviderOfCountable b

/-- For an uncountable signature there is no scheduler provider. -/
theorem isEmpty_schedulerProvider_of_not_countable {σ : Ty Base}
    (h : ¬ Countable (Const σ)) : IsEmpty (SchedulerProvider (Base := Base) Const) :=
  ⟨fun P => h (P.countable_const σ)⟩

/-! ## Examples -/

/-- One base type and no constants. -/
abbrev EmptySig : Ty Unit → Type := fun _ => Empty

/-- Positive instance: the countable signature `EmptySig` has a scheduler
provider. -/
theorem emptySig_schedulerProvider :
    Nonempty (SchedulerProvider (Base := Unit) EmptySig) :=
  ⟨schedulerProviderOfCountable⟩

/-- ... and so it has no full-presented upgrade. -/
theorem emptySig_no_fullPresentedUpgrade :
    IsEmpty (FullPresentedUpgrade (Base := Unit) EmptySig) :=
  isEmpty_fullPresentedUpgrade_of_countable ()

/-- One base type and a real-number constant at every type. -/
abbrev RealSig : Ty Unit → Type := fun _ => ℝ

/-- Negative instance: the uncountable signature `RealSig` has no scheduler
provider. -/
theorem realSig_no_schedulerProvider :
    IsEmpty (SchedulerProvider (Base := Unit) RealSig) :=
  isEmpty_schedulerProvider_of_not_countable (σ := .prop)
    (fun h => Cardinal.not_countable_real (Set.countable_univ_iff.mpr h))

end SupportedCanonicalFrame

end KripkeHenkin

end Mettapedia.Logic.HOL
