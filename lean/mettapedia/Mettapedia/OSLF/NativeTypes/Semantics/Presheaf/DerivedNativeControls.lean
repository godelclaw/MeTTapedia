import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointReadout
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeEqualityComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementNativeDeclarationModels
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Derived higher-order native controls on actual dependent scalar contexts

The original native parser evaluates the complete generated quantifiers,
predicate abstraction and application. A nonconstant seed retains exactly
positive scalar parameters. The printed existential-implication encoding is
separately refuted against independent least fixed-point semantics.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.DerivedNativeControls

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeDeclarationModels NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming FixedPointEvaluation NativeFixedPointEncodings

universe u v
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}

def variableBody : Logic.Formula (Sum Unit Unit) := .atom (.inr ())
def seededBody : Logic.Formula (Sum Unit Unit) := .disj (.atom (.inl ())) variableBody
theorem variable_checked : Monotone.variance true variableBody = true := rfl
theorem seeded_checked : Monotone.variance true seededBody = true := rfl

theorem inductive_identity (atoms : Unit → Subfunctor P) :
    Monotone.inductiveMeaning atoms variableBody variable_checked = ⊥ := by
  apply le_antisymm _ bot_le
  exact least_induction _ ⊥ le_rfl

theorem coinductive_identity (atoms : Unit → Subfunctor P) :
    Monotone.coinductiveMeaning atoms variableBody variable_checked = ⊤ := by
  apply le_antisymm le_top
  exact greatest_coinduction _ ⊤ le_rfl

theorem inductive_seed (seed : Subfunctor P) :
    Monotone.inductiveMeaning (fun _ : Unit => seed) seededBody seeded_checked = seed := by
  apply le_antisymm
  · exact least_induction _ seed (sup_idem seed).le
  · have unfolded := Monotone.inductive_unfold (fun _ : Unit => seed) seededBody seeded_checked
    change seed ⊔ Monotone.inductiveMeaning (fun _ : Unit => seed) seededBody seeded_checked = _ at unfolded
    exact le_sup_left.trans unfolded.le

theorem coinductive_seed (seed : Subfunctor P) :
    Monotone.coinductiveMeaning (fun _ : Unit => seed) seededBody seeded_checked = ⊤ := by
  apply le_antisymm le_top
  exact greatest_coinduction _ ⊤ le_sup_right

/-- Literal printed mu: existential implication, with the postfixed guard.
This is recorded as a source reading, separate from corrected generation. -/
def printedLeast {S : Symbols.{v}} {n : Nat} (domain : TypeExpr S n)
    (atoms : Unit → PropExpr S (n + 1)) (body : Logic.Formula (Sum Unit Unit))
    (tested : TermExpr S n) : PropExpr S n :=
  .exists (FixedPointSyntax.predicateType domain)
    (.implies (FixedPointSyntax.postfixed domain atoms body)
      (FixedPointSyntax.application (domain.rename Fin.succ) (.var 0) (tested.rename Fin.succ)))

noncomputable def printedLeastMeaning (A : NativeType P)
    (atoms : Unit → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Unit Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) : Subfunctor P :=
  (postGuard A atoms body checked ⇨ testedMembership A value).image
    (totalProjection (predicate A).decoded)

theorem printed_least_top (A : NativeType P)
    (atoms : Unit → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Unit Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) : printedLeastMeaning A atoms body checked value = ⊤ := by
  apply le_antisymm le_top
  let naming := sectionLift (predicate A).decoded (NativeLocalTypeOperations.lam (nativeQuote
    (⊤ : Subfunctor (totalSpace A.decoded))))
  have tested : (testedMembership A value).preimage naming = ⊤ := by
    rw [tested_reified]
    ext world parameter
    rfl
  have selected : (postGuard A atoms body checked ⇨ testedMembership A value).preimage naming = ⊤ := by
    rw [preimage_himp, tested, himp_top]
  intro world parameter _
  refine ⟨naming.app world parameter, ?_, rfl⟩
  change parameter ∈ ((postGuard A atoms body checked ⇨ testedMembership A value).preimage naming).obj world
  rw [selected]
  trivial

theorem evaluate_printed_least_top {S : Symbols.{v}} {n : Nat}
    (interpreter : ModelData S C) (context : Scope C n) (domain : TypeExpr S n)
    (A : NativeType context.1) (atoms : Unit → PropExpr S (n + 1))
    (meanings : Unit → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Unit Unit)) (checked : Monotone.variance true body = true)
    (tested : TermExpr S n) (value : A.decoded.sections)
    (domainRead : interpreter.evaluateType context domain = some A)
    (atomRead : ∀ atom, interpreter.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom))
    (valueRead : interpreter.evaluateTerm context tested = some ⟨A, value⟩) :
    interpreter.evaluatePredicate context (printedLeast domain atoms body tested) = some ⊤ := by
  have implication := interpreter.evaluate_implies _ _ _ _ _
    (evaluate_postfixed interpreter context domain A atoms meanings body checked domainRead atomRead)
    (evaluate_application_under_predicate interpreter context domain tested A value domainRead valueRead)
  rw [himpPointwise_eq_himp] at implication
  have result := interpreter.evaluate_exists _ _ _ _ _
    (FixedPointSyntax.evaluate_predicateType interpreter context domain A domainRead) implication
  exact result.trans (congrArg some (printed_least_top A meanings body checked value))

abbrev World := Discrete PUnit.{1}
abbrev spot : Worldᵒᵖ := Opposite.op (Discrete.mk PUnit.unit)

def atomCodes : Unit → PropExpr Controls.symbols 2 := fun _ => Controls.positive 1
def atomMeanings : Unit → Subfunctor (doubleScope (C := World)).1 :=
  fun _ => positivity.preimage newestScalar

theorem atoms_read (name : Unit) :
    (model (C := World)).evaluatePredicate doubleScope (atomCodes name) = some (atomMeanings name) :=
  newest_positive_read

theorem argument_seed_identity :
    sectionLift (scalarVariableType (C := World)).decoded scalarVariable ≫ newestScalar =
      𝟙 (scalarScope (C := World)).1 := by
  ext world parameter
  rfl

theorem scalar_inductive_seed :
    Monotone.inductiveMeaning atomMeanings seededBody seeded_checked =
      positivity.preimage newestScalar := inductive_seed _

theorem scalar_coinductive_seed :
    Monotone.coinductiveMeaning atomMeanings seededBody seeded_checked = ⊤ := coinductive_seed _

/-- The complete generated least formula actually runs through the original
parser and retains exactly the positive scalar parameters. -/
theorem actual_seeded_least :
    (model (C := World)).evaluatePredicate scalarScope
      (FixedPointSyntax.least (Controls.scalar 1) atomCodes seededBody (.var 0)) = some positivity := by
  have result := FixedPointReadout.evaluate_least_exact model scalarScope (Controls.scalar 1)
    scalarVariableType atomCodes atomMeanings seededBody seeded_checked (.var 0) scalarVariable
    scalar_variable_type_read atoms_read scalar_variable_read
  rw [scalar_inductive_seed] at result
  rw [← Subfunctor.preimage_comp, argument_seed_identity, Subfunctor.preimage_id] at result
  exact result

theorem actual_seeded_greatest :
    (model (C := World)).evaluatePredicate scalarScope
      (FixedPointSyntax.greatest (Controls.scalar 1) atomCodes seededBody (.var 0)) = some ⊤ := by
  have result := FixedPointReadout.evaluate_greatest_exact model scalarScope (Controls.scalar 1)
    scalarVariableType atomCodes atomMeanings seededBody seeded_checked (.var 0) scalarVariable
    scalar_variable_type_read atoms_read scalar_variable_read
  rw [scalar_coinductive_seed] at result
  have pulled : (⊤ : Subfunctor (doubleScope (C := World)).1).preimage
      (sectionLift scalarVariableType.decoded scalarVariable) = ⊤ := by
    ext world parameter
    rfl
  rw [pulled] at result
  exact result

theorem seeded_positive :
    (⟨PUnit.unit, (1 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) ∈ positivity.obj spot :=
  Nat.zero_lt_succ 0

theorem seeded_zero_excluded :
    (⟨PUnit.unit, (0 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) ∉ positivity.obj spot :=
  Nat.not_lt_zero 0

theorem printed_mu_refuted :
    printedLeastMeaning (scalarVariableType (C := World)) atomMeanings seededBody seeded_checked scalarVariable ≠
      (Monotone.inductiveMeaning atomMeanings seededBody seeded_checked).preimage
        (sectionLift scalarVariableType.decoded scalarVariable) := by
  rw [printed_least_top, scalar_inductive_seed, ← Subfunctor.preimage_comp,
    argument_seed_identity, Subfunctor.preimage_id]
  intro equality
  have absurd : (⟨PUnit.unit, (0 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) ∈
      positivity.obj spot := by rw [← equality]; trivial
  exact seeded_zero_excluded absurd

theorem actual_printed_mu_top :
    (model (C := World)).evaluatePredicate scalarScope
      (printedLeast (Controls.scalar 1) atomCodes seededBody (.var 0)) = some ⊤ :=
  evaluate_printed_least_top model scalarScope (Controls.scalar 1) scalarVariableType atomCodes
    atomMeanings seededBody seeded_checked (.var 0) scalarVariable
    scalar_variable_type_read atoms_read scalar_variable_read

theorem printed_nu_refuted :
    (model (C := World)).evaluatePredicate scalarScope
      (FixedPointSyntax.least (Controls.scalar 1) atomCodes seededBody (.var 0)) ≠ some ⊤ := by
  rw [actual_seeded_least]
  intro alleged
  have equality := Option.some.inj alleged
  have absurd : (⟨PUnit.unit, (0 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) ∈
      positivity.obj spot := by rw [equality]; trivial
  exact seeded_zero_excluded absurd

abbrev doubleVariableType : NativeType (doubleScope (C := World)).1 :=
  (scalarVariableType (C := World)).reindex (totalProjection scalarVariableType.decoded)

noncomputable def previousValue : doubleVariableType.decoded.sections :=
  ContextualLocalUniverses.substituteTerm (type := scalarVariableType) scalarVariable
    (totalProjection scalarVariableType.decoded)

noncomputable def newestValue : doubleVariableType.decoded.sections :=
  (NativeModel World).toCwf.vz scalarVariableType

theorem double_scalar_read :
    (model (C := World)).evaluateType doubleScope (Controls.scalar 2) = some doubleVariableType := by
  have read := (model (C := World)).evaluateType_rename (products_substitution World)
    (Controls.scalar 1) doubleScope scalarScope Fin.succ
    (ModelRenaming.weaken scalarScope scalarVariableType) scalarVariableType scalar_variable_type_read
  rw [Controls.scalar_rename] at read
  exact read

theorem previous_value_read : (model (C := World)).evaluateTerm doubleScope (.var 1) =
    some ⟨doubleVariableType, previousValue⟩ := rfl

theorem newest_value_read : (model (C := World)).evaluateTerm doubleScope (.var 0) =
    some ⟨doubleVariableType, newestValue⟩ := rfl

theorem actual_equality_read :
    (model (C := World)).evaluatePredicate doubleScope
      (Generation.NativeEquality.equal (Controls.scalar 2) (.var 1) (.var 0)) =
        some (NativeEqualityComparison.diagonal doubleVariableType previousValue newestValue) :=
  NativeEqualityComparison.evaluate_equal model doubleScope (Controls.scalar 2) (.var 1) (.var 0)
    doubleVariableType previousValue newestValue double_scalar_read previous_value_read newest_value_read

theorem actual_equality_positive :
    (⟨⟨PUnit.unit, (3 : Nat)⟩, (3 : Nat)⟩ : (doubleScope (C := World)).1.obj spot) ∈
      (NativeEqualityComparison.diagonal doubleVariableType previousValue newestValue).obj spot := rfl

theorem actual_equality_negative :
    (⟨⟨PUnit.unit, (0 : Nat)⟩, (1 : Nat)⟩ : (doubleScope (C := World)).1.obj spot) ∉
      (NativeEqualityComparison.diagonal doubleVariableType previousValue newestValue).obj spot :=
  Nat.zero_ne_one

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.DerivedNativeControls
