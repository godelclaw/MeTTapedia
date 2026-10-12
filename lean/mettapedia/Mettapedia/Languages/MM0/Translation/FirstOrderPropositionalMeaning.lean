import Mettapedia.GSLT.LanguageDef.PropositionalHilbertMeaning
import Mettapedia.Languages.MM0.Translation.FirstOrderRules

/-!
# What MM0 acceptance means for propositional logic

The propositional rule presentations are admitted and compiled to MM0
theories: one sort, four term constructors, and one axiom for each rule. A
formula is a term over the variables of the context.

Three equivalences are composed. MM0 derives the term of a formula exactly
when the presentation derives the formula. The presentation derives it
exactly when the Hilbert system proves it. The Hilbert system proves it
exactly when it is valid in the semantics. So the MM0 checker accepts a
proof of a formula in the intuitionistic theory exactly when the formula
is valid on every Kripke frame, and in the classical theory exactly when it
is a tautology. Some formula has an accepted proof in the classical theory
and none in the intuitionistic one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderPropositionalMeaning

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.PropositionalHilbert
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules
open LO LO.Propositional

/-! ## The generated theories -/

theorem admitted (classical : Bool) :
    (Presentation.admit? language ["wff"] (rules classical)).isSome = true := by
  cases classical <;> decide +kernel

/-- The admitted presentation: intuitionistic, or classical. -/
def presentation (classical : Bool) : Presentation :=
  (Presentation.admit? language ["wff"] (rules classical)).get (admitted classical)

theorem presentation_retains (classical : Bool) :
    (presentation classical).syntaxSignature.language = language ∧
      (presentation classical).judgmentSorts = ["wff"] ∧
      (presentation classical).rules = rules classical :=
  Presentation.admit?_retains (Option.some_get (admitted classical)).symm

/-- The MM0 term of a formula. An atom is a variable of the context. -/
def encodeTerm : Formula ℕ → Preterm
  | .atom a => .var a
  | .falsum => .term 0
  | .and φ ψ => .app (.app (.term 1) (encodeTerm φ)) (encodeTerm ψ)
  | .or φ ψ => .app (.app (.term 2) (encodeTerm φ)) (encodeTerm ψ)
  | .imp φ ψ => .app (.app (.term 3) (encodeTerm φ)) (encodeTerm ψ)

theorem encodes : ∀ φ : Formula ℕ,
    Encodes (constructorNames language) (encode φ) (encodeTerm φ)
  | .atom a => .boundVariable a
  | .falsum => Encodes.constructor (name := "falsum") (index := 0) (by decide) .nil
  | .and φ ψ =>
      Encodes.constructor (name := "and") (index := 1) (by decide)
        (.cons (encodes φ) (.cons (encodes ψ) .nil))
  | .or φ ψ =>
      Encodes.constructor (name := "or") (index := 2) (by decide)
        (.cons (encodes φ) (.cons (encodes ψ) .nil))
  | .imp φ ψ =>
      Encodes.constructor (name := "imp") (index := 3) (by decide)
        (.cons (encodes φ) (.cons (encodes ψ) .nil))

/-- The MM0 context of `count` formula variables. -/
def targetContext (count : ℕ) : Context := List.replicate count (.regular 0 ∅)

theorem contexts : ∀ count : ℕ,
    ContextEncodes (sortNames language) (PropositionalHilbert.context count) (targetContext count)
  | 0 => .nil
  | count + 1 => .cons ⟨0, by decide, rfl⟩ (contexts count)

/-! ## MM0 derivability is provability -/

/-- **MM0 derives the term of a formula exactly when the Hilbert system
proves the formula.** -/
theorem mm0_derives_iff_hilbert {classical : Bool} {count : ℕ} {φ : Formula ℕ}
    (below : AtomsBelow count φ) :
    Kernel.Derives (presentation classical).theory.termSignature
        (presentation classical).theory.definitionSignature
        (presentation classical).theory.theoremSignature
        (targetContext count) [] (encodeTerm φ) ↔
      Hilbert.Standard (axioms classical) φ := by
  obtain ⟨sameLanguage, -, sameRules⟩ := presentation_retains classical
  have transported := Presentation.derivability_iff_of_equationFree
    (presentation := presentation classical) (by rw [sameLanguage]; rfl)
    (bound := PropositionalHilbert.context count) (context := targetContext count)
    (hypotheses := []) (targetHypotheses := []) (pattern := encode φ)
    (expression := encodeTerm φ)
    (by rw [Signature.sorts, sameLanguage]; exact contexts count) .nil
    (by rw [Signature.names, sameLanguage]; exact encodes φ)
  rw [sameLanguage, sameRules] at transported
  exact transported.symm.trans (derives_iff_hilbert below)

/-- The same, for proofs the MM0 checker accepts. -/
theorem mm0_checks_iff_hilbert {classical : Bool} {count : ℕ} {φ : Formula ℕ}
    (below : AtomsBelow count φ) :
    (∃ witness, ProofWitness.check (presentation classical).theory.termSignature
        (presentation classical).theory.definitionSignature
        (presentation classical).theory.theoremSignature
        (targetContext count) [] witness (encodeTerm φ) = true) ↔
      Hilbert.Standard (axioms classical) φ :=
  (Kernel.derives_iff_checked _ _ _ _ _ _).symm.trans (mm0_derives_iff_hilbert below)

/-! ## MM0 acceptance is validity -/

/-- **Intuitionistic logic.** The MM0 checker accepts a proof of a formula
in the intuitionistic theory exactly when the formula is valid on every
Kripke frame. -/
theorem mm0_checks_iff_kripke {count : ℕ} {φ : Formula ℕ} (below : AtomsBelow count φ) :
    (∃ witness, ProofWitness.check (presentation false).theory.termSignature
        (presentation false).theory.definitionSignature
        (presentation false).theory.theoremSignature
        (targetContext count) [] witness (encodeTerm φ) = true) ↔
      Kripke.FrameClass.Int ⊧ φ :=
  (mm0_checks_iff_hilbert below).trans
    ((derives_iff_hilbert below).symm.trans (derives_iff_kripke below))

/-- **Classical logic.** The MM0 checker accepts a proof of a formula in
the classical theory exactly when the formula is a tautology. -/
theorem mm0_checks_iff_tautology {count : ℕ} {φ : Formula ℕ} (below : AtomsBelow count φ) :
    (∃ witness, ProofWitness.check (presentation true).theory.termSignature
        (presentation true).theory.definitionSignature
        (presentation true).theory.theoremSignature
        (targetContext count) [] witness (encodeTerm φ) = true) ↔
      φ.Tautology :=
  (mm0_checks_iff_hilbert below).trans
    ((derives_iff_hilbert below).symm.trans (derives_iff_tautology below))

/-- **The two theories differ.** Some formula has an accepted MM0 proof in
the classical theory, and no MM0 proof of it in the intuitionistic theory
is accepted. -/
theorem mm0_excludedMiddle_adds :
    ∃ (count : ℕ) (φ : Formula ℕ),
      (∃ witness, ProofWitness.check (presentation true).theory.termSignature
        (presentation true).theory.definitionSignature
        (presentation true).theory.theoremSignature
        (targetContext count) [] witness (encodeTerm φ) = true) ∧
      ¬ ∃ witness, ProofWitness.check (presentation false).theory.termSignature
        (presentation false).theory.definitionSignature
        (presentation false).theory.theoremSignature
        (targetContext count) [] witness (encodeTerm φ) = true := by
  obtain ⟨count, φ, below, classical, intuitionistic⟩ := excludedMiddle_adds
  exact ⟨count, φ,
    (mm0_checks_iff_hilbert below).mpr ((derives_iff_hilbert below).mp classical),
    fun accepted => intuitionistic
      ((derives_iff_hilbert below).mpr ((mm0_checks_iff_hilbert below).mp accepted))⟩

/-! ## Controls -/

/-- Each theory has four term constructors and no definition. -/
example : (presentation false).theory.terms.length = 4 ∧
    (presentation false).theory.definitions = [] := by decide +kernel

/-- The classical theory has one axiom more. -/
example : (presentation false).theory.theorems.length = 10 ∧
    (presentation true).theory.theorems.length = 11 := by decide +kernel

/-- Excluded middle for an atom is accepted in the classical theory. -/
example : ∃ witness, ProofWitness.check (presentation true).theory.termSignature
    (presentation true).theory.definitionSignature (presentation true).theory.theoremSignature
    (targetContext 1) [] witness (encodeTerm (.atom 0 ⋎ ∼(.atom 0))) = true :=
  (mm0_checks_iff_hilbert (count := 1) (φ := .atom 0 ⋎ ∼(.atom 0))
    ⟨Nat.zero_lt_one, Nat.zero_lt_one, trivial⟩).mpr
    (Hilbert.Standard.axm' (by simp [axioms]))

/-- Falsity has no accepted proof in either theory. -/
example (classical : Bool) : ¬ ∃ witness,
    ProofWitness.check (presentation classical).theory.termSignature
      (presentation classical).theory.definitionSignature
      (presentation classical).theory.theoremSignature
      (targetContext 0) [] witness (encodeTerm ⊥) = true := by
  intro accepted
  have proved : Hilbert.Standard (axioms classical) (⊥ : Formula ℕ) :=
    (mm0_checks_iff_hilbert (count := 0) (φ := ⊥) trivial).mp accepted
  have derived : Derives language (rules classical) (PropositionalHilbert.context 0) []
      (encode ⊥) := (derives_iff_hilbert (count := 0) (φ := ⊥) trivial).mpr proved
  have classicalDerived : Derives language (rules true) (PropositionalHilbert.context 0) []
      (encode ⊥) := by
    cases classical
    · exact classical_of_intuitionistic (count := 0) (φ := ⊥) trivial derived
    · exact derived
  have tautology := (derives_iff_tautology (count := 0) (φ := ⊥) trivial).mp classicalDerived
  exact absurd (tautology (fun _ => True)) (by simp)

end Mettapedia.Languages.MM0.Translation.FirstOrderPropositionalMeaning
