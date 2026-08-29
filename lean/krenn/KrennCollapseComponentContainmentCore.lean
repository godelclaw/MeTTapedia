import KrennCollapseComponentContainmentData
import KrennCollapseSupportCoverSemantic

/-!
Semantic bottom-up connector for the reduced C6 collapse cover.

A chosen support stratum supplies two kinds of generator certificate:

* a coordinate declared zero in each monomial; or
* one of the checked signed chains of active reduced-collapse relations.

The first kills the generator directly.  The second invokes the finite
exponent-balance theorem and cancels only an active, hence nonzero, auxiliary
monomial.
-/

namespace Krenn.CollapseComponentContainment

open Krenn.LatticeCombinationReflection
open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainmentData

inductive GeneratorWitness where
  | killed (positiveZero : Fin 26) (negativeZero : Option (Fin 26))
  | chain (certificate : Fin 91)
deriving DecidableEq, Repr

/-- Evaluation of a normalized component generator.  A missing negative term
means a monomial generator. -/
noncomputable def generatorEval {R : Type*} [CommRing R]
    (values : Fin 26 → R) (generator : Fin 78) : R :=
  monomial values (generatorPositive generator) -
    match generatorNegative generator with
    | none => 0
    | some negative => monomial values negative

/-- Pure finite-data validity of one generator witness for one stratum. -/
def GeneratorWitness.Valid (stratum : GlobalFormula.Stratum)
    (generator : Fin 78) : GeneratorWitness → Prop
  | .killed positiveZero negativeZero =>
      stratum.zeroMask.testBit positiveZero ∧
      (generatorPositiveSupport generator).testBit positiveZero ∧
      match generatorNegativeSupport generator, negativeZero with
      | none, none => True
      | some negativeSupport, some coordinate =>
          stratum.zeroMask.testBit coordinate ∧
            negativeSupport.testBit coordinate
      | _, _ => False
  | .chain certificate =>
      (chainCertificate certificate).target = generator ∧
      generatorNegativeSupport generator ≠ none ∧
      ∀ use ∈ (chainCertificate certificate).steps,
        stratum.activeMask.testBit use.index

instance (stratum : GlobalFormula.Stratum) (generator : Fin 78)
    (witness : GeneratorWitness) :
    Decidable (witness.Valid stratum generator) := by
  cases witness with
  | killed positiveZero negativeZero =>
      unfold GeneratorWitness.Valid
      cases negativeEquation : generatorNegativeSupport generator <;>
        cases negativeZero <;> infer_instance
  | chain certificate =>
      unfold GeneratorWitness.Valid
      infer_instance

structure StratumCertificate where
  stratum : GlobalFormula.Stratum
  witnesses : List GeneratorWitness
deriving DecidableEq, Repr

/-- Witnesses are aligned exactly with the selected component's generator
list. -/
def StratumCertificate.Valid (certificate : StratumCertificate) : Prop :=
  List.Forall₂
    (fun generator witness => witness.Valid certificate.stratum generator)
    (componentGenerators certificate.stratum.component)
    certificate.witnesses

instance (certificate : StratumCertificate) : Decidable certificate.Valid := by
  unfold StratumCertificate.Valid
  infer_instance

theorem monomial_eq_zero_of_coordinate {R : Type*}
    [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (values : Fin 26 → R) (exponent : Fin 26 →₀ ℕ)
    (coordinate : Fin 26) (positivePower : exponent coordinate ≠ 0)
    (coordinateZero : values coordinate = 0) :
    monomial values exponent = 0 := by
  classical
  rw [monomial]
  apply Finset.prod_eq_zero (i := coordinate)
  · exact Finsupp.mem_support_iff.mpr positivePower
  · change values coordinate ^ exponent coordinate = 0
    rw [coordinateZero]
    exact zero_pow positivePower

theorem coordinate_zero_of_cover {R : Type*} [Zero R]
    (stratum : GlobalFormula.Stratum) (pattern : Fin 26 → Prop)
    (values : Fin 26 → R) (covered : Covers stratum pattern)
    (support : ∀ coordinate, pattern coordinate ↔ values coordinate ≠ 0)
    (coordinate : Fin 26) (declaredZero : stratum.zeroMask.testBit coordinate) :
    values coordinate = 0 := by
  by_contra nonzero
  exact covers_zero stratum pattern covered coordinate declaredZero
    ((support coordinate).mpr nonzero)

set_option maxHeartbeats 0 in
theorem relationLeft_monomial_ne_zero_of_active {R : Type*}
    [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (pattern : Fin 26 → Prop) (values : Fin 26 → R)
    (support : ∀ coordinate, pattern coordinate ↔ values coordinate ≠ 0)
    (index : Fin 14) (active : relationLeftActive pattern index) :
    monomial values (relation index).left ≠ 0 := by
  apply monomial_ne_zero_of_support
  intro coordinate inSupport
  apply (support coordinate).mp
  fin_cases index <;> fin_cases coordinate <;>
    simp [relation, relationLeftSupport, squarefreeExponent] at inSupport <;>
    norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow] at inSupport <;>
    simp_all [relationLeftActive]

/-- Semantic soundness of a single finite witness. -/
theorem generator_vanishes_of_valid_witness {R : Type*}
    [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (stratum : GlobalFormula.Stratum) (pattern : Fin 26 → Prop)
    (values : Fin 26 → R) (covered : Covers stratum pattern)
    (support : ∀ coordinate, pattern coordinate ↔ values coordinate ≠ 0)
    (relationEq : ∀ index,
      monomial values (relation index).left =
        monomial values (relation index).right)
    (generator : Fin 78) (witness : GeneratorWitness)
    (valid : witness.Valid stratum generator) :
    generatorEval values generator = 0 := by
  cases witness with
  | killed positiveZero negativeZero =>
      rcases valid with ⟨positiveDeclared, positiveOccurs, negativeValid⟩
      have positiveCoordinateZero := coordinate_zero_of_cover stratum pattern
        values covered support positiveZero positiveDeclared
      have positiveTermZero :
          monomial values (generatorPositive generator) = 0 := by
        apply monomial_eq_zero_of_coordinate values _ positiveZero
        · simp [generatorPositive, squarefreeExponent_apply,
            positiveOccurs]
        · exact positiveCoordinateZero
      cases negativeEquation : generatorNegativeSupport generator with
      | none =>
          cases negativeZero with
          | none =>
              simp [generatorEval, generatorNegative, negativeEquation,
                positiveTermZero]
          | some coordinate => simp [negativeEquation] at negativeValid
      | some negativeSupport =>
          cases negativeZero with
          | none => simp [negativeEquation] at negativeValid
          | some coordinate =>
              simp [negativeEquation] at negativeValid
              rcases negativeValid with ⟨negativeDeclared, negativeOccurs⟩
              have negativeCoordinateZero := coordinate_zero_of_cover stratum
                pattern values covered support coordinate negativeDeclared
              have negativeTermZero :
                  monomial values (squarefreeExponent negativeSupport) = 0 := by
                apply monomial_eq_zero_of_coordinate values _ coordinate
                · simp [squarefreeExponent_apply, negativeOccurs]
                · exact negativeCoordinateZero
              simp [generatorEval, generatorNegative, negativeEquation,
                positiveTermZero, negativeTermZero]
  | chain certificate =>
      rcases valid with ⟨targetEquation, negativeExists, activeRelations⟩
      cases negativeEquation : generatorNegativeSupport generator with
      | none => exact False.elim (negativeExists negativeEquation)
      | some negativeSupport =>
          have targetEquality :
              monomial values
                  (generatorBinomial
                    (chainCertificate certificate).target).left =
                monomial values
                  (generatorBinomial
                    (chainCertificate certificate).target).right := by
            apply target_monomials_eq_of_signed_relation_chain relation
              (generatorBinomial (chainCertificate certificate).target)
              (chainCertificate certificate).steps values relationEq
            · intro use member
              apply relationLeft_monomial_ne_zero_of_active pattern values support
              have activeBit := activeRelations use member
              simpa [activeBit] using
                (covers_activity stratum pattern covered use.index)
            · exact chainBalance certificate
          rw [targetEquation] at targetEquality
          have normalizedTarget :
              monomial values (generatorPositive generator) =
                monomial values (squarefreeExponent negativeSupport) := by
            simpa [generatorBinomial, generatorNegative, negativeEquation]
              using targetEquality
          simpa [generatorEval, generatorNegative, negativeEquation] using
            (sub_eq_zero.mpr normalizedTarget)

theorem exists_related_right_of_forall₂_of_mem
    {α β : Type*} {relation : α → β → Prop} {left : List α} {right : List β}
    (aligned : List.Forall₂ relation left right) {item : α}
    (member : item ∈ left) :
    ∃ witness ∈ right, relation item witness := by
  induction aligned with
  | nil => simp at member
  | cons headRelation tailRelation inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · exact ⟨_, by simp, headRelation⟩
      · obtain ⟨witness, witnessMember, related⟩ :=
          inductionHypothesis tailMember
        exact ⟨witness, by simp [witnessMember], related⟩

/-- A valid aligned certificate kills every generator of its selected
component. -/
theorem component_generators_vanish_of_valid_certificate {R : Type*}
    [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (certificate : StratumCertificate) (pattern : Fin 26 → Prop)
    (values : Fin 26 → R) (covered : Covers certificate.stratum pattern)
    (support : ∀ coordinate, pattern coordinate ↔ values coordinate ≠ 0)
    (relationEq : ∀ index,
      monomial values (relation index).left =
        monomial values (relation index).right)
    (valid : certificate.Valid) :
    ∀ generator ∈ componentGenerators certificate.stratum.component,
      generatorEval values generator = 0 := by
  intro generator member
  obtain ⟨witness, _, witnessValid⟩ :=
    exists_related_right_of_forall₂_of_mem valid member
  exact generator_vanishes_of_valid_witness certificate.stratum pattern
    values covered support relationEq generator witness witnessValid

end Krenn.CollapseComponentContainment

#print axioms Krenn.CollapseComponentContainment.generator_vanishes_of_valid_witness
#print axioms Krenn.CollapseComponentContainment.component_generators_vanish_of_valid_certificate
