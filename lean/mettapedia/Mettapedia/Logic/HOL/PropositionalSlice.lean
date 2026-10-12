import Mettapedia.Logic.HOL.Semantics.KripkeFrameModel
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.ClassicalExcludedMiddle
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Foundation.Propositional.Kripke.Logic.Cl
import Foundation.Propositional.ClassicalSemantics.Hilbert

/-!
# The propositional slice of HOL

A propositional formula is a closed HOL formula once its atoms are read as
propositional constants. This module proves that HOL, read this way, adds
nothing to propositional logic and loses nothing from it, in both of its
forms, and that its general models see exactly the propositional
semantics.

* **Without excluded middle.** The extensional calculus proves the image of
  a formula from no hypotheses exactly when intuitionistic propositional
  logic proves the formula (`provable_iff_int`), and exactly when the image
  holds at every world of every Kripke-Henkin general model
  (`provable_iff_kripkeHenkin`).
* **With excluded middle.** The extensional calculus proves the image from
  the excluded-middle schema exactly when classical propositional logic
  proves the formula (`provable_em_iff_cl`), and exactly when every
  extensional Henkin model satisfies it (`provable_em_iff_henkin`).

HOL quantifies over propositions and predicates, so a HOL proof of a
propositional formula may pass through impredicative formulas. The
direction from HOL to propositional logic is therefore semantic. Every
Kripke model of propositional logic extends to a Kripke-Henkin general model
of HOL (`kripkeModel`, an instance of `KripkeFrameModel.model`), and every
classical valuation to a standard Henkin model (`standardModel`); both
models evaluate the image of a formula as the formula. Soundness of HOL for
these models then carries a propositional countermodel to a HOL
countermodel, and the completeness theorems of propositional logic close the
circle.
-/

namespace Mettapedia.Logic.HOL

namespace PropositionalSlice

open LO LO.Propositional
open ClosedTheorySet

/-- Propositional formulas over numbered atoms. -/
abbrev PropFormula : Type := LO.Propositional.Formula ℕ

/-- No base types are needed. -/
abbrev AtomBase : Type := PEmpty

/-- One propositional constant per atom. -/
inductive Atom : Ty AtomBase → Type
  | atom : ℕ → Atom propTy

/-! ## Formulas as closed HOL formulas -/

section Embedding

variable {Const : Ty AtomBase → Type} (atom : ℕ → Const propTy)

/-- The image of a propositional formula, with the given constant for each
atom. -/
def embedWith : PropFormula → ClosedFormula Const
  | .atom a => .const (atom a)
  | .falsum => .bot
  | .and φ ψ => .and (embedWith φ) (embedWith ψ)
  | .or φ ψ => .or (embedWith φ) (embedWith ψ)
  | .imp φ ψ => .imp (embedWith φ) (embedWith ψ)

@[simp] theorem embedWith_atom (a : ℕ) :
    embedWith atom (.atom a) = .const (atom a) := rfl
@[simp] theorem embedWith_bot : embedWith atom (⊥ : PropFormula) = .bot := rfl
@[simp] theorem embedWith_top : embedWith atom (⊤ : PropFormula) = .imp .bot .bot := rfl
@[simp] theorem embedWith_and (φ ψ : PropFormula) :
    embedWith atom (φ ⋏ ψ) = .and (embedWith atom φ) (embedWith atom ψ) := rfl
@[simp] theorem embedWith_or (φ ψ : PropFormula) :
    embedWith atom (φ ⋎ ψ) = .or (embedWith atom φ) (embedWith atom ψ) := rfl
@[simp] theorem embedWith_imp (φ ψ : PropFormula) :
    embedWith atom (φ ➝ ψ) = .imp (embedWith atom φ) (embedWith atom ψ) := rfl
@[simp] theorem embedWith_neg (φ : PropFormula) :
    embedWith atom (∼φ) = .imp (embedWith atom φ) .bot := rfl

/-! ## Hilbert proofs are HOL proofs -/

variable {atom} {T : ClosedTheorySet Const}

theorem provable_of_derivation {φ : ClosedFormula Const}
    (d : ExtDerivation Const ([] : List (ClosedFormula Const)) φ) : Provable T φ :=
  ⟨[], ⟨fun _ member => by simp at member, d⟩⟩

/-- **Hilbert proofs translate.** If every instance of every axiom is
provable from a theory, every theorem of the Hilbert system is. Modus
ponens is implication elimination, and each scheme has a short natural
deduction. -/
theorem provable_of_hilbert {Ax : Axiom ℕ}
    (instances : ∀ ψ ∈ Ax, ∀ s : Substitution ℕ, Provable T (embedWith atom (ψ⟦s⟧)))
    {φ : PropFormula} (proof : Hilbert.Standard Ax φ) : Provable T (embedWith atom φ) := by
  induction proof with
  | axm s member => exact instances _ member s
  | mdp _ _ implication argument => exact provable_mp implication argument
  | verum => exact provable_of_derivation (φ := .imp .bot .bot) (.impI (.hyp (by simp)))
  | implyS φ ψ =>
      exact provable_of_derivation
        (φ := .imp (embedWith atom φ) (.imp (embedWith atom ψ) (embedWith atom φ)))
        (.impI (.impI (.hyp (by simp))))
  | implyK φ ψ χ =>
      exact provable_of_derivation
        (φ := .imp (.imp (embedWith atom φ) (.imp (embedWith atom ψ) (embedWith atom χ)))
          (.imp (.imp (embedWith atom φ) (embedWith atom ψ))
            (.imp (embedWith atom φ) (embedWith atom χ))))
        (.impI (.impI (.impI
          (.impE (φ := embedWith atom ψ)
            (.impE (φ := embedWith atom φ) (.hyp (by simp)) (.hyp (by simp)))
            (.impE (φ := embedWith atom φ) (.hyp (by simp)) (.hyp (by simp)))))))
  | andElimL φ ψ =>
      exact provable_of_derivation
        (φ := .imp (.and (embedWith atom φ) (embedWith atom ψ)) (embedWith atom φ))
        (.impI (.andEL (ψ := embedWith atom ψ) (.hyp (by simp))))
  | andElimR φ ψ =>
      exact provable_of_derivation
        (φ := .imp (.and (embedWith atom φ) (embedWith atom ψ)) (embedWith atom ψ))
        (.impI (.andER (φ := embedWith atom φ) (.hyp (by simp))))
  | andIntro φ ψ =>
      exact provable_of_derivation
        (φ := .imp (embedWith atom φ) (.imp (embedWith atom ψ)
          (.and (embedWith atom φ) (embedWith atom ψ))))
        (.impI (.impI (.andI (.hyp (by simp)) (.hyp (by simp)))))
  | orIntroL φ ψ =>
      exact provable_of_derivation
        (φ := .imp (embedWith atom φ) (.or (embedWith atom φ) (embedWith atom ψ)))
        (.impI (.orIL (.hyp (by simp))))
  | orIntroR φ ψ =>
      exact provable_of_derivation
        (φ := .imp (embedWith atom ψ) (.or (embedWith atom φ) (embedWith atom ψ)))
        (.impI (.orIR (.hyp (by simp))))
  | orElim φ ψ χ =>
      exact provable_of_derivation
        (φ := .imp (.imp (embedWith atom φ) (embedWith atom χ))
          (.imp (.imp (embedWith atom ψ) (embedWith atom χ))
            (.imp (.or (embedWith atom φ) (embedWith atom ψ)) (embedWith atom χ))))
        (.impI (.impI (.impI
          (.orE (φ := embedWith atom φ) (ψ := embedWith atom ψ) (.hyp (by simp))
            (.impE (φ := embedWith atom φ) (.hyp (by simp)) (.hyp (by simp)))
            (.impE (φ := embedWith atom ψ) (.hyp (by simp)) (.hyp (by simp)))))))

/-- Ex falso, for every instance. -/
theorem provable_efq (s : Substitution ℕ) :
    Provable T (embedWith atom ((Axioms.EFQ (.atom 0) : PropFormula)⟦s⟧)) :=
  provable_of_derivation (φ := .imp .bot (embedWith atom (s 0)))
    (.impI (.botE (.hyp (by simp))))

/-- Excluded middle in the shape of propositional logic, from the
excluded-middle formula of HOL. -/
theorem lem_derivation (ψ : ClosedFormula Const) :
    ExtDerivation Const [Term.or ψ (.not ψ)] (.or ψ (.imp ψ .bot)) :=
  .orE (φ := ψ) (ψ := .not ψ) (.hyp (by simp)) (.orIL (.hyp (by simp)))
    (.orIR (.impI (.notE (φ := ψ) (.hyp (by simp)) (.hyp (by simp)))))

end Embedding

/-! ## Kripke models of propositional logic as models of HOL -/

/-- The frame of a propositional Kripke model. -/
def kripkeFrame (M : Kripke.Model) : KripkeFrameModel.Frame.{0, 0} AtomBase where
  World := M.World
  le := fun w v => M.toFrame.Rel w v
  le_refl := fun _ => Kripke.Frame.refl
  le_trans := fun first second => Kripke.Frame.trans first second
  Carrier := fun b => b.elim

/-- An atom denotes the set of worlds where it holds. -/
def kripkeConst (M : Kripke.Model) : {τ : Ty AtomBase} → Atom τ → (kripkeFrame M).Val τ
  | _, .atom a => fun w => M.Val.Val a w

theorem kripkeConst_adm (M : Kripke.Model) :
    ∀ {τ : Ty AtomBase} (c : Atom τ), (kripkeFrame M).Adm τ (kripkeConst M c)
  | _, .atom _ => fun related holds => M.Val.hereditary related holds

/-- **The Kripke-Henkin general model of a propositional Kripke model.** -/
def kripkeModel (M : Kripke.Model) : KripkeHenkinGeneral AtomBase Atom :=
  KripkeFrameModel.model (kripkeFrame M) (kripkeConst M) (kripkeConst_adm M)

/-- The image of a formula with the atom constants. -/
abbrev embed : PropFormula → ClosedFormula Atom := embedWith Atom.atom

/-- The model evaluates the image of a formula as the formula. -/
theorem kripkeModel_denote (M : Kripke.Model) (ρ : (kripkeModel M).Valuation [])
    (w : M.World) : ∀ φ : PropFormula,
      (kripkeModel M).denote (embed φ) ρ w ↔ LO.Propositional.Formula.Kripke.Satisfies M w φ
  | .atom a => Iff.rfl
  | .falsum => Iff.rfl
  | .and φ ψ => and_congr (kripkeModel_denote M ρ w φ) (kripkeModel_denote M ρ w ψ)
  | .or φ ψ => or_congr (kripkeModel_denote M ρ w φ) (kripkeModel_denote M ρ w ψ)
  | .imp φ ψ => by
      constructor
      · intro holds v related satisfied
        exact (kripkeModel_denote M ρ v ψ).mp
          (holds v related ((kripkeModel_denote M ρ v φ).mpr satisfied))
      · intro satisfies v related denoted
        exact (kripkeModel_denote M ρ v ψ).mpr
          (satisfies related ((kripkeModel_denote M ρ v φ).mp denoted))

/-- A formula whose image holds everywhere in every model of this kind is
valid on every Kripke frame. -/
theorem kripke_valid_of_denote {φ : PropFormula}
    (denoted : ∀ (M : Kripke.Model) (w : M.World),
      (kripkeModel M).denote (embed φ) (kripkeModel M).emptyVal w) :
    Kripke.FrameClass.Int ⊧ φ := by
  intro F _
  refine LO.Propositional.Formula.Kripke.ValidOnFrame.models_iff.mpr fun V => ?_
  refine LO.Propositional.Formula.Kripke.ValidOnModel.iff_models.mpr fun w => ?_
  exact LO.Propositional.Formula.Kripke.Satisfies.iff_models.mpr
    ((kripkeModel_denote ⟨F, V⟩ _ w φ).mp (denoted ⟨F, V⟩ w))

/-! ## Without excluded middle -/

/-- **HOL without excluded middle proves exactly the intuitionistic
tautologies.** -/
theorem provable_iff_int {φ : PropFormula} :
    Provable (∅ : ClosedTheorySet Atom) (embed φ) ↔ Propositional.Int ⊢ φ := by
  constructor
  · intro provable
    exact Complete.complete (kripke_valid_of_denote fun M w =>
      (kripkeModel M).denote_of_provable_empty provable w)
  · intro proved
    refine provable_of_hilbert (Ax := Propositional.Int.axioms) ?_
      (Logic.iff_provable.mp proved)
    intro ψ member s
    rw [Set.mem_singleton_iff.mp member]
    exact provable_efq s

/-- **On propositional formulas, HOL without excluded middle is complete for
its Kripke-Henkin general models.** -/
theorem provable_iff_kripkeHenkin {φ : PropFormula} :
    Provable (∅ : ClosedTheorySet Atom) (embed φ) ↔
      ∀ (N : KripkeHenkinGeneral.{0, 0, 0} AtomBase Atom) (W : N.World),
        N.denote (embed φ) N.emptyVal W := by
  constructor
  · exact fun provable N W => N.denote_of_provable_empty provable W
  · intro denoted
    exact provable_iff_int.mpr
      (Complete.complete (kripke_valid_of_denote fun M w => denoted (kripkeModel M) w))

/-! ## With excluded middle -/

/-- The image of a formula in the signature with parameters, where the
excluded-middle schema of HOL lives. -/
abbrev embedP : PropFormula → ClosedFormula (WithParams Atom) :=
  embedWith fun a => WithParams.inj (Atom.atom a)

/-- The carriers of a standard model: there are no base types. -/
abbrev standardCarrier : AtomBase → Type 1 := fun b => b.elim

/-- A value of every type. -/
def defaultValue : (τ : Ty AtomBase) → Ty.denote.{0, 0} standardCarrier τ
  | .prop => ULift.up True
  | .base b => b.elim
  | .arr _ τ => fun _ => defaultValue τ

/-- Atoms denote their truth values; parameters denote default values. -/
def standardConst (v : ℕ → Prop) {τ : Ty AtomBase} :
    WithParams Atom τ → Ty.denote.{0, 0} standardCarrier τ
  | Sum.inl c => match τ, c with
    | _, .atom a => ULift.up (v a)
  | Sum.inr _ => defaultValue τ

/-- **The standard Henkin model of a classical valuation.** -/
def standardModel (v : ℕ → Prop) : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom) :=
  HenkinModel.standard standardCarrier (standardConst v)

theorem standardModel_extensional (v : ℕ → Prop) :
    (standardModel v).FunctionsRespectEqv :=
  (standardModel v).functionsRespectEqv_of_fullDomains
    (HenkinModel.fullDomains_standard _ _)

/-- The standard model evaluates the image of a formula as the formula. -/
theorem standardModel_denote (v : ℕ → Prop) (ρ : (standardModel v).Valuation []) :
    ∀ φ : PropFormula,
      ((standardModel v).denote (embedP φ) ρ).down ↔
        LO.Propositional.Formula.ClassicalSemantics.val v φ
  | .atom _ => Iff.rfl
  | .falsum => Iff.rfl
  | .and φ ψ => and_congr (standardModel_denote v ρ φ) (standardModel_denote v ρ ψ)
  | .or φ ψ => or_congr (standardModel_denote v ρ φ) (standardModel_denote v ρ ψ)
  | .imp φ ψ => imp_congr (standardModel_denote v ρ φ) (standardModel_denote v ρ ψ)

/-- Every instance of the excluded-middle schema holds in every Henkin model:
the metatheory is classical. -/
theorem emSchema_satisfied (N : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom))
    (ρ : N.Valuation []) {χ : ClosedFormula (WithParams Atom)} (member : χ ∈ EMSchema Atom) :
    (N.denote χ ρ).down := by
  rcases member with ⟨ψ, rfl⟩ | ⟨σ, φ, rfl⟩
  · exact Classical.em _
  · intro x _
    exact Classical.em _

/-- What HOL with excluded middle proves holds in every extensional Henkin
model. -/
theorem models_of_provable_em (N : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom))
    (extensional : N.FunctionsRespectEqv) {χ : ClosedFormula (WithParams Atom)}
    (provable : Provable (EMSchema Atom) χ) : N.models χ := by
  obtain ⟨Γ, within, derivation⟩ := provable
  exact Soundness.extDerivation_sound derivation extensional (fun v => nomatch v)
    (fun γ member => emSchema_satisfied N _ (within γ member))

/-- A formula whose image every extensional Henkin model satisfies is a
tautology. -/
theorem tautology_of_models {φ : PropFormula}
    (models : ∀ (N : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom)),
      N.FunctionsRespectEqv → N.models (embedP φ)) : φ.Tautology := by
  intro v
  exact LO.Propositional.Formula.ClassicalSemantics.models_iff_val.mpr
    ((standardModel_denote v _ φ).mp (models (standardModel v) (standardModel_extensional v)))

/-- **HOL with excluded middle proves exactly the classical tautologies.** -/
theorem provable_em_iff_cl {φ : PropFormula} :
    Provable (EMSchema Atom) (embedP φ) ↔ Propositional.Cl ⊢ φ := by
  constructor
  · intro provable
    exact Cl.completeness (tautology_of_models fun N extensional =>
      models_of_provable_em N extensional provable)
  · intro proved
    refine provable_of_hilbert (Ax := Propositional.Cl.axioms) ?_
      (Logic.iff_provable.mp proved)
    intro ψ member s
    rcases member with rfl | rfl
    · exact provable_efq s
    · let instanceFormula : ClosedFormula (WithParams Atom) := embedP (s 0)
      exact ⟨[Term.or instanceFormula (.not instanceFormula)],
        fun γ inList => by
          rw [List.mem_singleton.mp inList]
          exact emClosed_mem instanceFormula,
        lem_derivation instanceFormula⟩

/-- **On propositional formulas, HOL with excluded middle is complete for its
extensional Henkin models.** -/
theorem provable_em_iff_henkin {φ : PropFormula} :
    Provable (EMSchema Atom) (embedP φ) ↔
      ∀ (N : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom)),
        N.FunctionsRespectEqv → N.models (embedP φ) := by
  constructor
  · exact fun provable N extensional => models_of_provable_em N extensional provable
  · intro models
    exact provable_em_iff_cl.mpr (Cl.completeness (tautology_of_models models))

/-! ## Controls -/

/-- Two worlds, the first below the second; the atom `0` holds only at the
second world, and no other atom holds anywhere. -/
def twoWorlds : Kripke.Model where
  World := Bool
  Rel := fun x y => x ≤ y
  Val := ⟨fun a w => a = 0 ∧ w = true, fun {w₁ w₂} related {_} holds => by
    obtain ⟨zero, rfl⟩ := holds
    refine ⟨zero, ?_⟩
    cases w₂
    · exact absurd related (by decide)
    · rfl⟩

theorem twoWorlds_not_excludedMiddle :
    ¬ LO.Propositional.Formula.Kripke.Satisfies twoWorlds false (.atom 0 ⋎ ∼(.atom 0)) := by
  rintro (holds | refuted)
  · exact Bool.false_ne_true holds.2
  · exact refuted (w' := true) (show false ≤ true from by decide) ⟨rfl, rfl⟩

/-- Excluded middle for an atom is not provable without the schema. -/
theorem excludedMiddle_not_provable :
    ¬ Provable (∅ : ClosedTheorySet Atom) (embed (.atom 0 ⋎ ∼(.atom 0))) := fun provable =>
  twoWorlds_not_excludedMiddle ((kripkeModel_denote twoWorlds _ false _).mp
    ((kripkeModel twoWorlds).denote_of_provable_empty provable false))

/-- It is provable from the schema. -/
theorem excludedMiddle_provable_em :
    Provable (EMSchema Atom) (embedP (.atom 0 ⋎ ∼(.atom 0))) :=
  provable_em_iff_cl.mpr
    (Logic.iff_provable.mpr (Hilbert.Standard.axm' (by simp [Propositional.Cl.axioms])))

/-- So intuitionistic logic does not prove it either. -/
example : ¬ Propositional.Int ⊢ (.atom 0 ⋎ ∼(.atom 0) : PropFormula) :=
  fun proved => excludedMiddle_not_provable (provable_iff_int.mpr proved)

/-- Peirce's law. -/
abbrev peirce : PropFormula := ((.atom 0 ➝ .atom 1) ➝ .atom 0) ➝ .atom 0

/-- Peirce's law separates the two calculi: HOL with the schema proves it,
HOL without it does not. -/
theorem peirce_separates :
    Provable (EMSchema Atom) (embedP peirce) ∧
      ¬ Provable (∅ : ClosedTheorySet Atom) (embed peirce) := by
  constructor
  · refine provable_em_iff_cl.mpr (Cl.completeness fun v => ?_)
    simp only [peirce, LO.Propositional.Formula.ClassicalSemantics.models_iff_val, LO.Propositional.Formula.ClassicalSemantics.val]
    tauto
  · intro provable
    have holds : LO.Propositional.Formula.Kripke.Satisfies twoWorlds false peirce :=
      (kripkeModel_denote twoWorlds _ false _).mp
        ((kripkeModel twoWorlds).denote_of_provable_empty provable false)
    have noImplication : ∀ w : Bool,
        ¬ LO.Propositional.Formula.Kripke.Satisfies twoWorlds w (.atom 0 ➝ .atom 1) := by
      intro w implication
      have later : (1 : ℕ) = 0 ∧ true = true :=
        implication (w' := true) (show w ≤ true from by cases w <;> decide) ⟨rfl, rfl⟩
      exact absurd later.1 (by decide)
    have antecedent : LO.Propositional.Formula.Kripke.Satisfies twoWorlds false
        ((.atom 0 ➝ .atom 1) ➝ .atom 0) := by
      intro w _ implication
      exact (noImplication w (@implication)).elim
    exact Bool.false_ne_true
      (holds (w' := false) (show false ≤ false from le_refl false) antecedent).2

end PropositionalSlice

end Mettapedia.Logic.HOL
