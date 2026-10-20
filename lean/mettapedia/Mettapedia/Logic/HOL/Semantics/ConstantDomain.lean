import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mettapedia.Logic.HOL.Semantics.FrameValued
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinGeneral

/-!
# The constant-domain schema separates the intuitionistic semantics

The constant-domain schema at a type `σ` is the closed sentence

`CD σ := ∀ p : prop. ∀ Q : σ → prop. (∀ x : σ. p ∨ Q x) → p ∨ ∀ x : σ. Q x`.

* Every substitutional `KripkeHenkin` structure forces `CD σ` at every world
  and every type: its quantifiers range over the same closed terms at every
  world, so `∀ x. Q x` follows from the instances by monotonicity.
* Every `KripkeHenkinGeneral` model forces `CD (base b)`: base domains are the
  same at every world (`base_mem`).
* `CD (base b)` is not derivable in the EM-free calculus, over any signature:
  the frame of open subsets of `ℝ` gives a frame-valued model where its value
  is `ℝ ∖ {0}`.  This is DeMarco and Lipton's Example 4.3 (J. Logic Comput.
  15(6), 2005): with `a = ℝ ∖ {0}` and `bₙ = (-1/(n+1), 1/(n+1))`, every
  `a ∪ bₙ` is `ℝ`, but the interior of `⋂ bₙ` is empty.

Hence neither Kripke class is complete for the calculus, while the
Heyting-valued class is (`HeytingSem.provable_iff_heytingConsequence_param_free`);
`CD` separates the two consequence relations.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open TopologicalSpace

/-! ## The schema -/

/-- The body of the constant-domain sentence, in the context `[σ ⇒ prop, prop]`:
`(∀ x. p ∨ Q x) → p ∨ ∀ x. Q x` with `Q` the newest variable and `p` the other. -/
def constantDomainBody (σ : Ty Base) : Formula Const [σ ⇒ .prop, .prop] :=
  .imp (.all (σ := σ) (.or (.var (.vs (.vs .vz))) (.app (.var (.vs .vz)) (.var .vz))))
    (.or (.var (.vs .vz)) (.all (σ := σ) (.app (.var (.vs .vz)) (.var .vz))))

/-- The constant-domain sentence at type `σ`:
`∀ p : prop. ∀ Q : σ → prop. (∀ x : σ. p ∨ Q x) → p ∨ ∀ x : σ. Q x`. -/
def constantDomain (σ : Ty Base) : ClosedFormula Const :=
  .all (σ := .prop) (.all (σ := σ ⇒ .prop) (constantDomainBody σ))

/-- One instance of the constant-domain schema: a closed formula `φ` and a
predicate body `ψ`. -/
def constantDomainInstance {σ : Ty Base} (φ : ClosedFormula Const)
    (ψ : Formula Const [σ]) : ClosedFormula Const :=
  .imp (.all (.or (weaken φ) ψ)) (.or φ (.all ψ))

/-- Instantiating the two outer quantifiers of the sentence gives the
instance for `p` and the body `Q x`. -/
theorem instantiate_constantDomainBody {σ : Ty Base} (p : ClosedFormula Const)
    (Q : ClosedTerm Const (σ ⇒ .prop)) :
    instantiate Q (subst (Subst.lift (Subst.single p)) (constantDomainBody σ)) =
      constantDomainInstance p (.app (weaken Q) (.var .vz)) := by
  have hp : instantiate Q (weaken (σ := σ ⇒ .prop) p) = p := instantiate_weaken Q p
  have hpp : subst (Subst.lift (σ := σ) (Subst.single Q))
      (weaken (σ := σ) (weaken (σ := σ ⇒ .prop) p)) = weaken (σ := σ) p := by
    rw [subst_weaken]
    exact congrArg (weaken (σ := σ)) hp
  show Term.imp (Term.all (Term.or
        (subst (Subst.lift (σ := σ) (Subst.single Q))
          (weaken (σ := σ) (weaken (σ := σ ⇒ .prop) p)))
        (.app (weaken Q) (.var .vz))))
      (Term.or (instantiate Q (weaken (σ := σ ⇒ .prop) p))
        (.all (.app (weaken Q) (.var .vz)))) = _
  rw [hpp, hp]
  rfl

/-- The sentence uses no constant symbol. -/
theorem mapConst_constantDomain {Const' : Ty Base → Type w}
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ) (σ : Ty Base) :
    mapConst f (constantDomain (Const := Const) σ) = constantDomain σ := rfl

/-- The sentence mentions no constant, in particular no parameter. -/
theorem noConstOccurrence_constantDomain {ρ : Ty Base} (c : Const ρ) (σ : Ty Base) :
    NoConstOccurrence c (constantDomain (Const := Const) σ) :=
  .all (.all (.imp (.all (.or .var (.app .var .var))) (.or .var (.all (.app .var .var)))))

/-! ## Validity in the substitutional Kripke class -/

namespace KripkeHenkin

/-- Every substitutional Kripke-Henkin structure forces every instance of the
constant-domain schema. -/
theorem forces_constantDomainInstance (M : KripkeHenkin.{u, v, w} Base Const)
    (W : M.World) {σ : Ty Base} (φ : ClosedFormula Const) (ψ : Formula Const [σ]) :
    M.forces W (constantDomainInstance φ ψ) := by
  classical
  refine M.forces_imp.mpr fun V _ hV => M.forces_or.mpr ?_
  by_cases hφ : M.forces V φ
  · exact Or.inl hφ
  · refine Or.inr (M.forces_all.mpr fun V' hVV' t => ?_)
    have h := M.forces_all.mp hV V (M.le_refl V) t
    have hshape : instantiate t (.or (weaken φ) ψ : Formula Const [σ]) =
        .or φ (instantiate t ψ) := by
      show Term.or (instantiate t (weaken φ)) (instantiate t ψ) = _
      rw [instantiate_weaken]
    rw [hshape] at h
    rcases M.forces_or.mp h with h₁ | h₂
    · exact absurd h₁ hφ
    · exact M.forces_mono hVV' h₂

/-- Every substitutional Kripke-Henkin structure forces the constant-domain
sentence at every type and every world. -/
theorem forces_constantDomain (M : KripkeHenkin.{u, v, w} Base Const) (W : M.World)
    (σ : Ty Base) : M.forces W (constantDomain σ) := by
  refine M.forces_all.mpr fun V _ p => ?_
  show M.forces V (.all (subst (Subst.lift (Subst.single p)) (constantDomainBody σ)))
  refine M.forces_all.mpr fun V' _ Q => ?_
  rw [instantiate_constantDomainBody p Q]
  exact forces_constantDomainInstance M V' p _

/-- The constant-domain sentence is a consequence of the empty theory over the
substitutional Kripke class. -/
theorem consequence_constantDomain (σ : Ty Base) :
    Consequence.{u, v, w} (Base := Base) (Const := Const) ∅ (constantDomain σ) :=
  fun M W _ => forces_constantDomain M W σ

end KripkeHenkin

/-! ## Validity in the Kripke-Henkin general class at base types -/

namespace KripkeHenkinGeneral

/-- Every Kripke-Henkin general model denotes the constant-domain sentence at
every base type and every world: base domains do not grow. -/
theorem denote_constantDomain_base (M : KripkeHenkinGeneral Base Const) (b : Base)
    (W : M.World) : M.denote (constantDomain (.base b)) M.emptyVal W := by
  classical
  intro V _ p _ V' _ q hq V'' hV'V'' hA
  by_cases hp : p V''
  · exact Or.inl hp
  · refine Or.inr fun V₃ hV₃ x _ => ?_
    rcases hA V'' (M.le_refl V'') x (M.base_mem V'' b x) with h | h
    · exact absurd h hp
    · exact M.prop_adm_upset (M.app_mem (M.adm_mono hV'V'' hq) (M.base_mem V'' b x)) hV₃ h

end KripkeHenkinGeneral

/-! ## The countermodel: open subsets of the real line -/

namespace ConstantDomainCountermodel

/-- The open set `ℝ ∖ {0}`. -/
def puncture : Opens ℝ := ⟨{0}ᶜ, isOpen_compl_singleton⟩

/-- The open interval `(-1/(n+1), 1/(n+1))`. -/
def shrink (n : ℕ) : Opens ℝ := ⟨Metric.ball 0 (1 / ((n : ℝ) + 1)), Metric.isOpen_ball⟩

theorem puncture_sup_shrink (n : ℕ) : puncture ⊔ shrink n = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [Opens.mem_sup]
  by_cases hx : x = 0
  · right
    subst hx
    show (0 : ℝ) ∈ Metric.ball 0 (1 / ((n : ℝ) + 1))
    exact Metric.mem_ball_self (by positivity)
  · exact Or.inl hx

/-- Any open set below every `shrink n` is empty: it lies inside `{0}`, which
is not open. -/
theorem eq_bot_of_le_shrink {U : Opens ℝ} (hU : ∀ n, U ≤ shrink n) : U = ⊥ := by
  have hsub : (U : Set ℝ) ⊆ {0} := by
    intro x hx
    by_contra hne
    have hpos : 0 < |x| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    have hball : x ∈ Metric.ball (0 : ℝ) (1 / ((n : ℝ) + 1)) := hU n hx
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hball
    exact absurd (hball.trans hn) (lt_irrefl _)
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx0 : x = 0 := hsub hx
  subst hx0
  have hEq : (U : Set ℝ) = {0} :=
    Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hx)
  exact absurd (hEq ▸ U.isOpen) (not_isOpen_singleton (0 : ℝ))

/-- The value `ℝ ∖ {0}` of the conclusion is not `⊤`, though every instance of
the hypothesis has value `⊤`. -/
theorem puncture_sup_iInf_ne_top {ι : Sort*} (g : ι → ℕ) (hg : Function.Surjective g) :
    puncture ⊔ ⨅ i, shrink (g i) ≠ ⊤ := by
  intro htop
  have hbot : (⨅ i, shrink (g i)) = ⊥ := by
    refine eq_bot_of_le_shrink fun n => ?_
    obtain ⟨i, rfl⟩ := hg n
    exact iInf_le _ i
  rw [hbot, sup_bot_eq] at htop
  have h0 : (0 : ℝ) ∈ ((⊤ : Opens ℝ) : Set ℝ) := Set.mem_univ 0
  rw [← htop] at h0
  exact h0 (Set.mem_singleton 0)

/-- The frame of open subsets of `ℝ`, with the natural numbers at every base
type. -/
abbrev H := Opens ℝ

/-- Base carriers of the countermodel. -/
abbrev C (_ : Base) : Type := ℕ

open FrameValued

/-- The predicate `n ↦ shrink n` is admissible: crisp equality on `ℕ`. -/
theorem adm_shrink (b : Base) :
    Adm H C (.base b ⇒ .prop) (fun n : ℕ => shrink n) := by
  refine ⟨fun _ _ => trivial, fun d e _ _ => ?_⟩
  by_cases hde : d = e
  · subst hde
    exact le_top.trans (eqv_refl (H := H) (C := C) (τ := .prop) trivial).ge
  · exact (le_of_eq (eqv_base_of_ne H C hde)).trans bot_le

/-- The constant-domain sentence at a base type has value at most `ℝ ∖ {0}`. -/
theorem truth_constantDomain_le (b : Base) :
    truth (H := H) (C := C) (constantDomain (.base b)) (typeStructure H C).emptyVal ≤
      (⨅ x : {x // Adm H C (.base b) x}, puncture ⊔ shrink x.1) ⇨
        (puncture ⊔ ⨅ x : {x // Adm H C (.base b) x}, shrink x.1) := by
  refine iInf_le_of_le ⟨puncture, trivial⟩ ?_
  exact iInf_le_of_le ⟨fun n : ℕ => shrink n, adm_shrink b⟩ le_rfl

theorem truth_constantDomain_ne_top (b : Base) :
    truth (H := H) (C := C) (constantDomain (.base b)) (typeStructure H C).emptyVal ≠ ⊤ := by
  intro htop
  have hle := truth_constantDomain_le b
  rw [htop] at hle
  have hhyp : (⨅ x : {x // Adm H C (.base b) x}, puncture ⊔ shrink x.1) = ⊤ :=
    iInf_eq_top.mpr fun x => puncture_sup_shrink x.1
  rw [hhyp, top_himp] at hle
  exact puncture_sup_iInf_ne_top (fun x : {x // Adm H C (.base b) x} => x.1)
    (fun n => ⟨⟨n, trivial⟩, rfl⟩) (top_le_iff.mp hle)

end ConstantDomainCountermodel

open ConstantDomainCountermodel in
/-- **The constant-domain sentence is not derivable** in the EM-free calculus,
over any signature, at any base type. -/
theorem constantDomain_not_derivable (b : Base) :
    ¬ ExtDerivation Const [] (constantDomain (.base b)) := by
  intro d
  let f : ∀ {τ : Ty Base}, Const τ → FrameValued.Names H C τ :=
    fun {τ} _ => ⟨FrameValued.defaultElem H C τ, FrameValued.adm_defaultElem H C τ⟩
  have d' := ExtDerivation.mapConst f d
  rw [mapConst_constantDomain] at d'
  exact truth_constantDomain_ne_top b (FrameValued.truth_eq_top_of_derivation H C d')

/-- The constant-domain sentence is not provable from the empty theory. -/
theorem constantDomain_not_provable (b : Base) :
    ¬ ClosedTheorySet.Provable (Const := Const) ∅ (constantDomain (.base b)) := by
  rintro ⟨Γ, hΓ, d⟩
  have hnil : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr fun ψ hψ => hΓ ψ hψ
  subst hnil
  exact constantDomain_not_derivable b d

/-! ## Incompleteness of the two Kripke classes -/

/-- **The substitutional Kripke class is not complete.**  At every base type,
the constant-domain sentence is a consequence of the empty theory over every
universe of worlds, and is not provable. -/
theorem KripkeHenkin.not_complete (b : Base) :
    KripkeHenkin.Consequence.{u, v, w} (Base := Base) (Const := Const) ∅
        (constantDomain (.base b)) ∧
      ¬ ClosedTheorySet.Provable (Const := Const) ∅ (constantDomain (.base b)) :=
  ⟨KripkeHenkin.consequence_constantDomain _, constantDomain_not_provable b⟩

/-- **The Kripke-Henkin general class is not complete either**: its higher-type
domains may grow, but its base domains do not. -/
theorem KripkeHenkinGeneral.not_complete (b : Base) :
    (∀ (M : KripkeHenkinGeneral Base Const) (W : M.World),
        M.denote (constantDomain (.base b)) M.emptyVal W) ∧
      ¬ ClosedTheorySet.Provable (Const := Const) ∅ (constantDomain (.base b)) :=
  ⟨fun M W => KripkeHenkinGeneral.denote_constantDomain_base M b W,
    constantDomain_not_provable b⟩

open Mettapedia.Logic.HOL.WithParams in
/-- The constant-domain sentence separates the Kripke consequence relation from
the Heyting-valued one: it is a Kripke consequence of the empty theory and not
a Heyting consequence. -/
theorem constantDomain_separates_kripke_heyting (b : Base) :
    KripkeHenkin.Consequence.{u, v, w} (Base := Base) (Const := WithParams Const) ∅
        (constantDomain (.base b)) ∧
      ¬ HeytingSem.HeytingConsequence (Base := Base) (Const := WithParams Const) ∅
        (constantDomain (.base b)) := by
  refine ⟨KripkeHenkin.consequence_constantDomain _, fun hSem => ?_⟩
  exact constantDomain_not_provable (Const := WithParams Const) b
    (HeytingSem.provable_of_heytingConsequence_param_free (fun _ h => h.elim) hSem)

end Mettapedia.Logic.HOL
