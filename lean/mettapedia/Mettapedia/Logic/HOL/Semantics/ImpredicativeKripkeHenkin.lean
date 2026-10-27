import Mettapedia.Logic.HOL.Semantics.ProofSyntaxModuloKripkeHenkin
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# The impredicative connectives in Kripke–Henkin general models

The quantifier over propositions ranges over the admissible propositions only, but every formula denotes an admissible
proposition (`term_closed`), so each impredicative definition finds the witness it needs among them:

* `⊥ := ∀r. r` holds nowhere (`denote_falsity`), and `p → ⊥` holds where `p` fails at every later world
  (`denote_negation`);
* `p ∧ q := ∀r. (p → q → r) → r` holds where both hold (`denote_conjunctionFormula`);
* `p ∨ q := ∀r. (p → r) → (q → r) → r` holds where one of them holds (`denote_disjunctionFormula`);
* `∃x. φ := ∀r. (∀x. φ → r) → r` holds where some admissible element has `φ` (`denote_existentialInline`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.KripkeHenkinGeneral

open Mettapedia.Logic.HOL.ImpredicativeConnectives (falsity conjunctionFormula disjunctionFormula existentialInline)

universe u v x

variable {Base : Type u} {Const : Ty Base → Type v} (M : KripkeHenkinGeneral.{u, v, x} Base Const)
variable {Γ : Ctx Base}

theorem denote_weaken_prop (p : Formula Const Γ) (ρ : M.Valuation Γ) (r : Ty.denoteK M.Carrier M.World .prop)
    (W : M.World) : M.denote (weaken (σ := .prop) p) (M.extend ρ r) W ↔ M.denote p ρ W :=
  iff_of_eq (congrFun (M.toKripkePreModel.denote_weaken p ρ r) W)

theorem denote_falsity {ρ : M.Valuation Γ} {W : M.World} (admissible : M.ValuationAdm W ρ) :
    M.denote (falsity : Formula Const Γ) ρ W ↔ False :=
  ⟨fun everything => everything W (M.le_refl W) _ (M.term_closed (.bot : Formula Const Γ) W ρ admissible),
    False.elim⟩

theorem denote_negation (p : Formula Const Γ) {ρ : M.Valuation Γ} {W : M.World} (admissible : M.ValuationAdm W ρ) :
    M.denote (.imp p falsity) ρ W ↔ ∀ V, M.le W V → ¬ M.denote p ρ V :=
  ⟨fun refuted V later holds =>
      (M.denote_falsity (M.toKripkePreModel.valuationAdm_mono later admissible)).mp (refuted V later holds),
    fun never V later holds => (never V later holds).elim⟩

theorem denote_conjunctionFormula (p q : Formula Const Γ) {ρ : M.Valuation Γ} {W : M.World}
    (admissible : M.ValuationAdm W ρ) :
    M.denote (conjunctionFormula p q) ρ W ↔ M.denote p ρ W ∧ M.denote q ρ W := by
  constructor
  · intro both
    refine both W (M.le_refl W) _ (M.term_closed (.and p q) W ρ admissible) W (M.le_refl W) ?_
    intro U later held T later' held'
    exact ⟨M.denote_prop_mono p admissible later' ((M.denote_weaken_prop p ρ _ U).mp held),
      (M.denote_weaken_prop q ρ _ T).mp held'⟩
  · rintro ⟨held, held'⟩ V later r _ U later' elim
    exact elim U (M.le_refl U) ((M.denote_weaken_prop p ρ r U).mpr (M.denote_prop_mono p admissible
      (M.le_trans later later') held)) U (M.le_refl U) ((M.denote_weaken_prop q ρ r U).mpr
        (M.denote_prop_mono q admissible (M.le_trans later later') held'))

theorem denote_disjunctionFormula (p q : Formula Const Γ) {ρ : M.Valuation Γ} {W : M.World}
    (admissible : M.ValuationAdm W ρ) :
    M.denote (disjunctionFormula p q) ρ W ↔ M.denote p ρ W ∨ M.denote q ρ W := by
  constructor
  · intro either
    refine either W (M.le_refl W) _ (M.term_closed (.or p q) W ρ admissible) W (M.le_refl W)
      (fun U _ held => ?_) W (M.le_refl W) fun U _ held => ?_
    · exact Or.inl ((M.denote_weaken_prop p ρ _ U).mp held)
    · exact Or.inr ((M.denote_weaken_prop q ρ _ U).mp held)
  · rintro (held | held) V later r rAdmissible U later' left T later'' right
    · exact M.prop_adm_upset rAdmissible later''
        (left U (M.le_refl U) ((M.denote_weaken_prop p ρ r U).mpr
          (M.denote_prop_mono p admissible (M.le_trans later later') held)))
    · exact right T (M.le_refl T) ((M.denote_weaken_prop q ρ r T).mpr
        (M.denote_prop_mono q admissible (M.le_trans later (M.le_trans later' later'')) held))

theorem denote_existentialInline {σ : Ty Base} (φ : Formula Const (σ :: Γ)) {ρ : M.Valuation Γ} {W : M.World}
    (admissible : M.ValuationAdm W ρ) :
    M.denote (existentialInline φ) ρ W ↔ ∃ d, M.adm W σ d ∧ M.denote φ (M.extend ρ d) W := by
  have lifted : ∀ (r : Ty.denoteK M.Carrier M.World .prop) (d : Ty.denoteK M.Carrier M.World σ),
      M.denote (rename (Rename.lift Rename.weaken) φ) (M.extend (M.extend ρ r) d) =
        M.denote φ (M.extend ρ d) := by
    intro r d
    refine (M.toKripkePreModel.denote_rename φ _ _).trans (M.toKripkePreModel.denote_ext φ ?_)
    intro τ i
    cases i <;> rfl
  constructor
  · intro some
    refine some W (M.le_refl W) _ (M.term_closed (.ex φ) W ρ admissible) W (M.le_refl W) ?_
    intro V _ d dAdmissible V' later' held
    show M.denote (.ex φ) ρ V'
    exact (M.toKripkePreModel.denote_ex ρ φ V').mpr
      ⟨d, M.adm_mono later' dAdmissible, Eq.mp (congrFun (lifted (M.denote (.ex φ) ρ) d) V') held⟩
  · rintro ⟨d, dAdmissible, held⟩ V later r _ U later' elim
    have admissibleD : M.ValuationAdm W (M.extend ρ d) := M.toKripkePreModel.extend_adm admissible dAdmissible
    refine elim U (M.le_refl U) d (M.adm_mono (M.le_trans later later') dAdmissible) U (M.le_refl U) ?_
    exact Eq.mpr (congrFun (lifted r d) U) (M.denote_prop_mono φ admissibleD (M.le_trans later later') held)

end Mettapedia.Logic.HOL.KripkeHenkinGeneral
