import Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedDecomposition
import Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend

open Mettapedia.OSLF.Framework

/-!
# Executable original rho structural families with ordered input predicates

Checking a structural family inspects actual typed object introductions and
their ordered argument classes. Positive answers retain a listed introduction;
negative answers require complete fibre coverage. The same predicate can be
used as a leaf of the compositional native modal checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition
open Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations
open Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedDecomposition

abbrev Inputs (rule : GrammarRule) :=
  ∀ position, BooleanPredicate (inputEquations rule position)

/-- The independent typed constructor image, with every ordered input test. -/
def Holds (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (inputs : Inputs rule) (source : Pattern) : Prop :=
  ∃ value : Value free bound rule, canonicalEquations.r source value.val.pattern ∧
    ∀ position, (inputs position).meaning (argument value position)

def evaluate (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (inputs : Inputs rule) (budget : Nat) (source : Pattern) : Option Bool :=
  if (values free bound rule budget source).any
      (acceptsArguments argument (inputEquations rule) inputs) then some true
  else if closed budget source then some false else none

theorem positive (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (inputs : Inputs rule) (budget : Nat) (source : Pattern)
    (read : evaluate free bound rule inputs budget source = some true) :
    Holds free bound rule inputs source := by
  unfold evaluate at read
  split at read
  · rename_i accepted
    obtain ⟨value, listed, arguments⟩ := List.any_eq_true.mp accepted
    exact ⟨value, values_sound listed,
      (acceptsArguments_exact argument (inputEquations rule) inputs value).mp arguments⟩
  · split at read <;> contradiction

theorem negative (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (member : rule ∈ rhoCalc.terms) (inputs : Inputs rule) (budget : Nat) (source : Pattern)
    (read : evaluate free bound rule inputs budget source = some false) :
    ¬ Holds free bound rule inputs source := by
  rintro ⟨value, represents, arguments⟩
  unfold evaluate at read
  split at read
  · contradiction
  · rename_i noneAccepted
    split at read
    · rename_i completed
      obtain ⟨candidate, listed, related⟩ :=
        (backend free bound rule member).ordered_coverage budget source completed value represents
      have candidateAccepted : acceptsArguments argument (inputEquations rule) inputs candidate = true := by
        apply (acceptsArguments_exact argument (inputEquations rule) inputs candidate).mpr
        intro position
        exact ((inputs position).invariant (related position)).mp (arguments position)
      exact noneAccepted (List.any_eq_true.mpr ⟨candidate, listed, candidateAccepted⟩)
    · contradiction

theorem checked_complete (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (inputs : Inputs rule) (source : Pattern) :
    ∃ answer, evaluate free bound rule inputs (completionBudget source) source = some answer := by
  unfold evaluate
  split
  · exact ⟨true, rfl⟩
  · rw [complete_at]
    exact ⟨false, rfl⟩

theorem checked_exact (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (member : rule ∈ rhoCalc.terms) (inputs : Inputs rule) (source : Pattern) :
    evaluate free bound rule inputs (completionBudget source) source = some true ↔
      Holds free bound rule inputs source := by
  constructor
  · exact positive free bound rule inputs _ source
  · intro holds
    obtain ⟨answer, read⟩ := checked_complete free bound rule inputs source
    cases answer with
    | false => exact False.elim (negative free bound rule member inputs _ source read holds)
    | true => exact read

theorem zero_budget_unknown (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (inputs : Inputs rule) (source : Pattern) :
    evaluate free bound rule inputs 0 source = none := by
  simp [evaluate, values, closed, representatives]

theorem holds_invariant (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (inputs : Inputs rule) {first second : Pattern} (related : canonicalEquations.r first second) :
    Holds free bound rule inputs first ↔ Holds free bound rule inputs second := by
  constructor
  · rintro ⟨value, firstRepresents, arguments⟩
    exact ⟨value, related.symm.trans firstRepresents, arguments⟩
  · rintro ⟨value, secondRepresents, arguments⟩
    exact ⟨value, related.trans secondRepresents, arguments⟩

/-- A structural family is an actual leaf of the original rho modal checker. -/
def test (free : FreeTypeContext) (bound : List TypeExpr) (rule : GrammarRule)
    (member : rule ∈ rhoCalc.terms) (inputs : Inputs rule) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Test rhoReflectiveGSLT Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted where
  predicate := ⟨fun source => Holds free bound rule inputs source.1,
    fun {_ _} related => holds_invariant free bound rule inputs
      ((Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.original_equations_exact _ _).mp related)⟩
  evaluate budget source := evaluate free bound rule inputs budget source.1
  positive budget source := positive free bound rule inputs budget source.1
  negative budget source := negative free bound rule member inputs budget source.1
  completionBudget source := completionBudget source.1
  complete_at source _ := checked_complete free bound rule inputs source.1
  complete_above source _ budget enough := by
    unfold evaluate
    rw [values_stable free bound rule source.1 budget enough, closed_stable source.1 budget enough]
    exact checked_complete free bound rule inputs source.1

/-- Equality with a particular ordered input class is executable and respects
the actual input carrier, including the collection carrier. -/
def equalInput (rule : GrammarRule) (position : Fin rule.params.length) (expected : Pattern) :
    BooleanPredicate (inputEquations rule position) where
  meaning actual := canonicalize actual = canonicalize expected
  invariant related := by
    have same := (input_equations_iff_canonical rule position _ _).mp related
    change canonicalize _ = canonicalize _ at same
    rw [same]
  accepts actual := decide (canonicalize actual = canonicalize expected)
  exact actual := decide_eq_true_iff

def equalInputs (rule : GrammarRule) (expected : Fin rule.params.length → Pattern) : Inputs rule :=
  fun position => equalInput rule position (expected position)

#print axioms positive
#print axioms negative
#print axioms checked_exact
#print axioms test

end Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking
