import Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Ring

/-!
# A portable calculus of polynomial readout identities

The signature distinguishes primitive queries from algebraic readout terms.
Its rules express commutative-semiring identities and equality composition.
They impose no additivity law on world-model revision and no independence law
on probabilistic events. Symbolic polynomial semantics keeps primitive query
identities until a consumer supplies an interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PolynomialReadoutCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open FirstOrderCalculus
open InferenceChecker CertificateGSLT

abbrev PolynomialQuery := MvPolynomial Pattern ℕ

def read (query : Pattern) : Pattern := app "Read" [query]
def zero : Pattern := app "Zero" []
def one : Pattern := app "One" []
def add (first second : Pattern) : Pattern := app "Sum" [first, second]
def mul (first second : Pattern) : Pattern := app "Product" [first, second]
def equal (first second : Pattern) : Pattern := app "SameReadout" [first, second]

/-- An uninterpreted readout term remains a symbolic generator. The
recognized algebra constructors are interpreted recursively. -/
noncomputable def polynomial : Pattern → PolynomialQuery
  | .apply "Read" [query] => MvPolynomial.X query
  | .apply "Zero" [] => 0
  | .apply "One" [] => 1
  | .apply "Sum" [first, second] => polynomial first + polynomial second
  | .apply "Product" [first, second] => polynomial first * polynomial second
  | other => MvPolynomial.X other
termination_by pattern => sizeOf pattern

def meaning : Pattern → Prop
  | .apply "SameReadout" [first, second] => polynomial first = polynomial second
  | _ => False

def rules : List RuleSchema :=
  [rule "refl" ["a"] [] (equal (fv "a") (fv "a")),
    rule "symm" ["a", "b"] [equal (fv "a") (fv "b")] (equal (fv "b") (fv "a")),
    rule "trans" ["a", "b", "c"] [equal (fv "a") (fv "b"), equal (fv "b") (fv "c")]
      (equal (fv "a") (fv "c")),
    rule "sum-congr" ["a", "b", "c", "d"]
      [equal (fv "a") (fv "b"), equal (fv "c") (fv "d")]
      (equal (add (fv "a") (fv "c")) (add (fv "b") (fv "d"))),
    rule "product-congr" ["a", "b", "c", "d"]
      [equal (fv "a") (fv "b"), equal (fv "c") (fv "d")]
      (equal (mul (fv "a") (fv "c")) (mul (fv "b") (fv "d"))),
    rule "sum-comm" ["a", "b"] [] (equal (add (fv "a") (fv "b")) (add (fv "b") (fv "a"))),
    rule "sum-assoc" ["a", "b", "c"] []
      (equal (add (add (fv "a") (fv "b")) (fv "c")) (add (fv "a") (add (fv "b") (fv "c")))),
    rule "sum-zero" ["a"] [] (equal (add zero (fv "a")) (fv "a")),
    rule "product-comm" ["a", "b"] [] (equal (mul (fv "a") (fv "b")) (mul (fv "b") (fv "a"))),
    rule "product-assoc" ["a", "b", "c"] []
      (equal (mul (mul (fv "a") (fv "b")) (fv "c")) (mul (fv "a") (mul (fv "b") (fv "c")))),
    rule "product-one" ["a"] [] (equal (mul one (fv "a")) (fv "a")),
    rule "product-zero" ["a"] [] (equal (mul zero (fv "a")) zero),
    rule "distribute" ["a", "b", "c"] []
      (equal (mul (fv "a") (add (fv "b") (fv "c")))
        (add (mul (fv "a") (fv "b")) (mul (fv "a") (fv "c"))))]

def calculus : CalculusLanguageDef where
  name := "polynomial-readouts"
  types := [TypeDecl.plain "Query", TypeDecl.plain "Readout"]
  terms := [term "Read" "Readout" [("query", "Query")], term "Zero" "Readout" [],
    term "One" "Readout" [], term "Sum" "Readout" [("first", "Readout"), ("second", "Readout")],
    term "Product" "Readout" [("first", "Readout"), ("second", "Readout")]]
  judgments := [⟨"SameReadout", 2⟩]
  rules := rules
  equations := []
  rewrites := []

theorem calculus_admitted : calculus.isAdmitted = true := by decide +kernel

def validated : ValidatedCalculusLanguageDef := calculus.validated calculus_admitted

def moduleText : String := ModuleFormat.Portable.renderCalculus validated.val

theorem moduleText_read : ModuleFormat.Portable.readValidatedCalculus? moduleText = some validated :=
  ModuleFormat.Portable.readValidatedCalculus_renderCalculus _

/-- The admitted equality rules preserve the symbolic polynomial under
arbitrary ground argument expressions. -/
theorem rule_application_sound (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern) (application : RuleApplication validated ruleInstance premises conclusion)
    (premisesSound : ∀ premise ∈ premises, meaning premise) : meaning conclusion := by
  rcases ruleInstance with ⟨id, arguments⟩
  cases application with
  | intro schema lookup valid _ premisesInstantiate conclusionInstantiates =>
    have member := List.mem_of_find?_eq_some lookup
    change schema ∈ rules at member
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have length : arguments.length = 1 := (argumentsValidAt_length valid).symm
      obtain ⟨a, argumentsEq⟩ := List.length_eq_one_iff.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]

      rfl
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hypotheses
      dsimp only [meaning, equal, app] at hypotheses ⊢

      exact hypotheses.symm
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, c, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, equal, app] at hypotheses ⊢

      exact hypotheses.1.trans hypotheses.2
    · have length : arguments.length = 4 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, c, d, argumentsEq⟩ := List.length_eq_four.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, equal, app] at hypotheses ⊢
      simp only [polynomial] at hypotheses ⊢
      exact congrArg₂ (· + ·) hypotheses.1 hypotheses.2
    · have length : arguments.length = 4 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, c, d, argumentsEq⟩ := List.length_eq_four.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, equal, app] at hypotheses ⊢
      simp only [polynomial] at hypotheses ⊢
      exact congrArg₂ (· * ·) hypotheses.1 hypotheses.2
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      ring
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, c, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      ring
    · have length : arguments.length = 1 := (argumentsValidAt_length valid).symm
      obtain ⟨a, argumentsEq⟩ := List.length_eq_one_iff.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      simp
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      ring
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, c, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      ring
    · have length : arguments.length = 1 := (argumentsValidAt_length valid).symm
      obtain ⟨a, argumentsEq⟩ := List.length_eq_one_iff.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      simp
    · have length : arguments.length = 1 := (argumentsValidAt_length valid).symm
      obtain ⟨a, argumentsEq⟩ := List.length_eq_one_iff.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      simp
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, c, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, read, zero, one, add, mul, equal]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      dsimp only [meaning, equal, app]
      simp only [polynomial]
      ring

/-- A checked open equality proof justifies the symbolic identity whenever
its external context equalities hold. -/
theorem checked_polynomial_equal (context : List Pattern) (first second : Pattern)
    (proof : RawOpenProof) (checked : checkOpenRaw validated context (equal first second) proof = true)
    (contextSound : ∀ premise ∈ context, meaning premise) : polynomial first = polynomial second := by
  obtain ⟨derivation, _⟩ := checkOpenRaw_exact_derivation checked
  exact derivation.sound_of_ruleApplications meaning rule_application_sound contextSound

end Mettapedia.GSLT.LanguageDef.PolynomialReadoutCalculus
