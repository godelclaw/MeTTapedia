import Mettapedia.GSLT.LanguageDef.ModalHilbertPresentations
import Mettapedia.Languages.MM0.Translation.FirstOrderRules
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhoodCompleteness
import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Modal.Neighborhood.Logic.EN

/-!
# What MM0 acceptance means for classical modal logics

A classical modal logic, given by its extra axioms, is a presentation of the
first-order class; its generated MM0 theory has three term constructors and
one axiom per rule. The MM0 checker accepts a proof of a formula exactly when
the Hilbert system with the RE rule proves it (`accepted_iff_hilbert`).

For the logics `E`, `EM`, `EN`, `EMN` and `EMT` the `Foundation` library
proves soundness and completeness for classes of neighborhood frames. So the
checker accepts a proof exactly when the formula is valid on the frame class
(`accepted_iff_neighborhood`).

The world-model calculus reads neighborhood semantics as evidence: a state
is a multiset of pointed neighborhood models, and the evidence for a formula
counts the points that satisfy it and those that refute it. The checker
accepts a proof of an implication exactly when, on every single point of
the frame class, the evidence strength of the antecedent is at most that of
the consequent (`accepted_imp_iff_evidence`), and an accepted implication
orders the evidence strengths on every multiset state of the class
(`evidence_le_of_accepted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderModalMeaning

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.ModalHilbert
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules
open LO LO.Modal
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhoodCompleteness
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open Mettapedia.PLN.WorldModel

/-- A classical modal logic given by its extra axioms, with the admission of
its presentation. -/
structure ModalLogic where
  extra : List ModalFormula
  admitted : (Presentation.admit? language ["wff"] (rules extra)).isSome = true

namespace ModalLogic

/-- The admitted presentation. -/
def presentation (L : ModalLogic) : Presentation :=
  (Presentation.admit? language ["wff"] (rules L.extra)).get L.admitted

theorem presentation_retains (L : ModalLogic) :
    L.presentation.syntaxSignature.language = language ∧
      L.presentation.judgmentSorts = ["wff"] ∧ L.presentation.rules = rules L.extra :=
  Presentation.admit?_retains (Option.some_get L.admitted).symm

end ModalLogic

/-- The MM0 term of a formula. An atom is a variable of the context. -/
def encodeTerm : ModalFormula → Preterm
  | .atom a => .var a
  | .falsum => .term 0
  | .imp φ ψ => .app (.app (.term 1) (encodeTerm φ)) (encodeTerm ψ)
  | .box φ => .app (.term 2) (encodeTerm φ)

theorem encodes : ∀ φ : ModalFormula,
    Encodes (constructorNames language) (encode φ) (encodeTerm φ)
  | .atom a => .boundVariable a
  | .falsum => Encodes.constructor (name := "falsum") (index := 0) (by decide) .nil
  | .imp φ ψ =>
      Encodes.constructor (name := "imp") (index := 1) (by decide)
        (.cons (encodes φ) (.cons (encodes ψ) .nil))
  | .box φ =>
      Encodes.constructor (name := "box") (index := 2) (by decide) (.cons (encodes φ) .nil)

/-- The MM0 context of `count` formula variables. -/
def targetContext (count : ℕ) : Context := List.replicate count (.regular 0 ∅)

theorem contexts : ∀ count : ℕ,
    ContextEncodes (sortNames language) (ModalHilbert.context count) (targetContext count)
  | 0 => .nil
  | count + 1 => .cons ⟨0, by decide, rfl⟩ (contexts count)

/-- The MM0 checker accepts some proof of the term of the formula. -/
abbrev Accepted (L : ModalLogic) (count : ℕ) (φ : ModalFormula) : Prop :=
  ∃ witness, ProofWitness.check L.presentation.theory.termSignature
    L.presentation.theory.definitionSignature L.presentation.theory.theoremSignature
    (targetContext count) [] witness (encodeTerm φ) = true

/-- **MM0 accepts exactly the theorems of the Hilbert system.** -/
theorem accepted_iff_hilbert (L : ModalLogic) {count : ℕ} {φ : ModalFormula}
    (below : AtomsBelow count φ) :
    Accepted L count φ ↔ Hilbert.WithRE (axioms L.extra) φ := by
  obtain ⟨sameLanguage, -, sameRules⟩ := L.presentation_retains
  have transported := Presentation.derivability_iff_of_equationFree
    (presentation := L.presentation) (by rw [sameLanguage]; rfl)
    (bound := ModalHilbert.context count) (context := targetContext count)
    (hypotheses := []) (targetHypotheses := []) (pattern := encode φ)
    (expression := encodeTerm φ)
    (by rw [Signature.sorts, sameLanguage]; exact contexts count) .nil
    (by rw [Signature.names, sameLanguage]; exact encodes φ)
  rw [sameLanguage, sameRules] at transported
  exact (Kernel.derives_iff_checked _ _ _ _ _ _).symm.trans
    (transported.symm.trans (derives_iff_hilbert below))

/-- The same, against a Hilbert system with the same axioms. -/
theorem accepted_iff_provable (L : ModalLogic) {A : Axiom ℕ} (same : axioms L.extra = A)
    {count : ℕ} {φ : ModalFormula} (below : AtomsBelow count φ) :
    Accepted L count φ ↔ Hilbert.WithRE A ⊢ φ := by
  rw [← same]
  exact (accepted_iff_hilbert L below).trans Logic.iff_provable.symm

/-- **MM0 accepts exactly the formulas valid on the frame class.** -/
theorem accepted_iff_neighborhood (L : ModalLogic) {A : Axiom ℕ} (same : axioms L.extra = A)
    (C : Neighborhood.FrameClass) [Sound (Hilbert.WithRE A) C] [Complete (Hilbert.WithRE A) C]
    {count : ℕ} {φ : ModalFormula} (below : AtomsBelow count φ) :
    Accepted L count φ ↔ C ⊧ φ :=
  (accepted_iff_provable L same below).trans ⟨Sound.sound, Complete.complete⟩

/-- **MM0 accepts an implication exactly when it orders the evidence.** On
every pointed neighborhood model of the class, as a single-point state, the
evidence strength of the antecedent is at most that of the consequent. -/
theorem accepted_imp_iff_evidence (L : ModalLogic) {A : Axiom ℕ} (same : axioms L.extra = A)
    (C : Neighborhood.FrameClass) [Sound (Hilbert.WithRE A) C] [Complete (Hilbert.WithRE A) C]
    {count : ℕ} {φ ψ : ModalFormula} (below : AtomsBelow count (φ ➝ ψ)) :
    Accepted L count (φ ➝ ψ) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) φ ψ :=
  (accepted_iff_provable L same below).trans
    (provable_imp_iff_singletonStrengthLEOn (S := LO.Modal.Logic ℕ) (𝓢 := Hilbert.WithRE A))

/-- An accepted implication orders the evidence strengths on every multiset
state of pointed models of the class. -/
theorem evidence_le_of_accepted (L : ModalLogic) {A : Axiom ℕ} (same : axioms L.extra = A)
    (C : Neighborhood.FrameClass) [Sound (Hilbert.WithRE A) C]
    {count : ℕ} {φ ψ : ModalFormula} (below : AtomsBelow count (φ ➝ ψ))
    (accepted : Accepted L count (φ ➝ ψ))
    {W : Multiset PointedNeighborhood} (inClass : ∀ pn ∈ W, pn.model.toFrame ∈ C) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood)
        (Query := LO.Modal.Formula ℕ) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood)
        (Query := LO.Modal.Formula ℕ) W ψ :=
  multiset_strength_le_of_provable_imp (S := LO.Modal.Logic ℕ) (𝓢 := Hilbert.WithRE A) inClass
    ((accepted_iff_provable L same below).mp accepted)

/-! ## The neighborhood logics -/

/-- The minimal classical modal logic. -/
def E : ModalLogic := ⟨[], by decide +kernel⟩

/-- With monotonicity. -/
def EM : ModalLogic := ⟨[Axioms.M (.atom 0) (.atom 1)], by decide +kernel⟩

/-- With necessitation of truth. -/
def EN : ModalLogic := ⟨[Axioms.N], by decide +kernel⟩

/-- With both. -/
def EMN : ModalLogic := ⟨[Axioms.M (.atom 0) (.atom 1), Axioms.N], by decide +kernel⟩

/-- Monotonicity and reflexivity. -/
def EMT : ModalLogic := ⟨[Axioms.M (.atom 0) (.atom 1), Axioms.T (.atom 0)], by decide +kernel⟩

theorem axioms_E : axioms E.extra = (∅ : Axiom ℕ) := by
  ext χ
  simp [axioms, E]

theorem axioms_EM : axioms EM.extra = Modal.EM.axioms := by
  ext χ
  simp [axioms, EM]

theorem axioms_EN : axioms EN.extra = Modal.EN.axioms := by
  ext χ
  simp [axioms, EN]

theorem axioms_EMN : axioms EMN.extra = Modal.EMN.axioms := by
  ext χ
  simp [axioms, EMN]

theorem axioms_EMT : axioms EMT.extra = Modal.EMT.axioms := by
  ext χ
  simp [axioms, EMT]

/-- `E`: accepted exactly when valid on every neighborhood frame. -/
theorem accepted_iff_E {count : ℕ} {φ : ModalFormula} (below : AtomsBelow count φ) :
    Accepted E count φ ↔ Neighborhood.FrameClass.E ⊧ φ :=
  accepted_iff_neighborhood E axioms_E Neighborhood.FrameClass.E below

/-- `EMN`: accepted exactly when valid on every frame of its class. -/
theorem accepted_iff_EMN {count : ℕ} {φ : ModalFormula} (below : AtomsBelow count φ) :
    Accepted EMN count φ ↔ Neighborhood.FrameClass.EMN ⊧ φ :=
  accepted_iff_neighborhood EMN axioms_EMN Neighborhood.FrameClass.EMN below

/-- `E`, read as evidence. -/
theorem accepted_imp_iff_evidence_E {count : ℕ} {φ ψ : ModalFormula}
    (below : AtomsBelow count (φ ➝ ψ)) :
    Accepted E count (φ ➝ ψ) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies
      (inClass Neighborhood.FrameClass.E) φ ψ :=
  accepted_imp_iff_evidence E axioms_E Neighborhood.FrameClass.E below

/-- `EMN`, read as evidence. -/
theorem accepted_imp_iff_evidence_EMN {count : ℕ} {φ ψ : ModalFormula}
    (below : AtomsBelow count (φ ➝ ψ)) :
    Accepted EMN count (φ ➝ ψ) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies
      (inClass Neighborhood.FrameClass.EMN) φ ψ :=
  accepted_imp_iff_evidence EMN axioms_EMN Neighborhood.FrameClass.EMN below

/-- `EMT`, read as evidence. -/
theorem accepted_imp_iff_evidence_EMT {count : ℕ} {φ ψ : ModalFormula}
    (below : AtomsBelow count (φ ➝ ψ)) :
    Accepted EMT count (φ ➝ ψ) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies
      (inClass Neighborhood.FrameClass.EMT) φ ψ :=
  accepted_imp_iff_evidence EMT axioms_EMT Neighborhood.FrameClass.EMT below

/-! ## Controls -/

/-- Necessitation of truth separates `EM` from `EMN`: some formula has an
accepted proof in `EMN` and none in `EM`. -/
theorem EM_EMN_separated :
    ∃ (count : ℕ) (φ : ModalFormula), Accepted EMN count φ ∧ ¬ Accepted EM count φ := by
  obtain ⟨-, φ, unprovable, provable⟩ := Entailment.strictlyWeakerThan_iff.mp
    (inferInstance : Modal.EM ⪱ Modal.EMN)
  obtain ⟨count, below⟩ := exists_atomsBelow φ
  exact ⟨count, φ, (accepted_iff_provable EMN axioms_EMN below).mpr provable,
    fun accepted => unprovable ((accepted_iff_provable EM axioms_EM below).mp accepted)⟩

/-- Reflexivity separates `EM` from `EMT` in the same way. -/
theorem EM_EMT_separated :
    ∃ (count : ℕ) (φ : ModalFormula), Accepted EMT count φ ∧ ¬ Accepted EM count φ := by
  obtain ⟨-, φ, unprovable, provable⟩ := Entailment.strictlyWeakerThan_iff.mp
    (inferInstance : Modal.EM ⪱ Modal.EMT)
  obtain ⟨count, below⟩ := exists_atomsBelow φ
  exact ⟨count, φ, (accepted_iff_provable EMT axioms_EMT below).mpr provable,
    fun accepted => unprovable ((accepted_iff_provable EM axioms_EM below).mp accepted)⟩

/-- The `M` axiom has an accepted proof in `EM`: it is one of its axioms. -/
example : Accepted EM 2 (Axioms.M (.atom 0) (.atom 1)) :=
  (accepted_iff_provable EM axioms_EM
    (count := 2) (φ := Axioms.M (.atom 0) (.atom 1))
    (by simp [AtomsBelow])).mpr
    (Hilbert.WithRE.axm'! (by simp [Modal.EM.axioms]))

end Mettapedia.Languages.MM0.Translation.FirstOrderModalMeaning
