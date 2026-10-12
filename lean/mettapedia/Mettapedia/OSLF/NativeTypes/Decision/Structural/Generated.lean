import Mettapedia.OSLF.NativeTypes.Decision.Structural.Backend
import Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition
import Mettapedia.OSLF.NativeTypes.Instances.Local.Structural

open Mettapedia.OSLF.Framework

/-!
# Executable generated structural native types

Local constructor decompositions and primitive interpreted argument tests
construct the executable result. Comparison with the independently specified
native quotient image is derived from primitive equation preservation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated StructuralInputs structuralDeclaration structuralInputSort structuralOutputSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes (Model)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction (EquationsInterpreted equation_sort_transport)
open Mettapedia.OSLF.NativeTypes.Decision.Structural.ConstructorBackend (Constructor Related InputRelated argument OrderedBackend)
open GSLTTypeSynthesis

def sourceTheory (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) :=
  GeneralOccurrenceSemantics.gslt generated.plan bound (.base (structuralDeclaration generated index).category)

def inputEquations (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (position : Fin (structuralDeclaration generated index).params.length) : Setoid Pattern :=
  (GeneralOccurrenceSemantics.gslt generated.plan bound
    (structuralDeclaration generated index).params[position].typeExpr).equations

/-- Only the input code's primitive equation generators are a model law.
Transport through the full equation class is proved below. -/
def InputsInterpreted {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} (inputs : StructuralInputs generated bound index) : Prop :=
  ∀ position source receipt,
    GeneralEquationJobs.Completion generated.plan bound
      (structuralDeclaration generated index).params[position].typeExpr source receipt →
    ((inputs position).meaning source ↔ (inputs position).meaning receipt.target)

theorem input_transport {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} {inputs : StructuralInputs generated bound index}
    (interpreted : InputsInterpreted inputs) (position : Fin (structuralDeclaration generated index).params.length)
    {first second : Pattern} (related : InputRelated generated bound index position first second) :
    (inputs position).meaning first ↔ (inputs position).meaning second := by
  induction related with
  | rel first second primitive =>
    obtain ⟨receipt, completed, equal⟩ := primitive
    exact equal ▸ interpreted position first receipt completed
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ left right => exact left.trans right

/-- Executable primitive subobjects at the actual output and ordered input
sorts. No field states the generated constructor comparison. -/
structure Effective {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index) where
  output : Pattern → Bool
  output_exact : ∀ source, output source = true ↔
    (model bound).sortDomain (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) source
  input : Fin (structuralDeclaration generated index).params.length → Pattern → Bool
  input_exact : ∀ position source, input position source = true ↔
    (model bound).sortDomain (structuralDeclaration generated index).params[position].typeExpr
      (structuralInputSort generated index position) source ∧ (inputs position).meaning source

def outputPredicate {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} {inputs : StructuralInputs generated bound index}
    (effective : Effective model bound index inputs) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.BooleanPredicate (sourceTheory generated bound index).equations where
  meaning := (model bound).sortDomain (.base (structuralDeclaration generated index).category)
    (structuralOutputSort generated index)
  invariant := equation_sort_transport equations bound _ _
  accepts := effective.output
  exact := effective.output_exact

def inputPredicates {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} {inputs : StructuralInputs generated bound index}
    (interpreted : InputsInterpreted inputs) (effective : Effective model bound index inputs)
    (position : Fin (structuralDeclaration generated index).params.length) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.BooleanPredicate (inputEquations generated bound index position) where
  meaning source := (model bound).sortDomain (structuralDeclaration generated index).params[position].typeExpr
    (structuralInputSort generated index position) source ∧ (inputs position).meaning source
  invariant := by
    intro first second related
    exact and_congr (equation_sort_transport equations bound _ _ related)
      (input_transport interpreted position related)
  accepts := effective.input position
  exact := effective.input_exact position

def decompositionBackend {generated : Generated} {bound : List TypeExpr} {admitted : Pattern → Prop}
    (backend : OrderedBackend generated bound admitted)
    (index : Fin generated.snapshot.language.terms.length) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.Backend (Constructor generated bound index)
      (structuralDeclaration generated index).params.length
      Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue.pattern argument
      (sourceTheory generated bound index).equations (inputEquations generated bound index) admitted where
  values budget source := backend.values budget index source
  closed budget source := backend.closed budget index source
  sound budget source value listed := backend.sound budget index source value listed
  ordered_coverage budget source closed value related := backend.ordered_coverage budget index source closed value related
  completionBudget source := backend.completionBudget index source
  complete_at source sourceAdmitted := backend.complete_at index source sourceAdmitted
  values_stable source budget enough := backend.values_stable index source budget enough
  closed_stable source budget enough := backend.closed_stable index source budget enough

theorem decomposition_native_comparison {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (interpreted : InputsInterpreted inputs) (effective : Effective model bound index inputs) (source : Pattern) :
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.imagePredicate (Value := Constructor generated bound index)
      Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue.pattern
      argument (inputEquations generated bound index) (outputPredicate equations effective)
      (inputPredicates equations interpreted effective) source ↔
    Mettapedia.OSLF.NativeTypes.Semantics.Structural.predicate model bound index inputs source := by
  constructor
  · rintro ⟨output, value, related, arguments⟩
    exact ⟨⟨value, (equation_sort_transport equations bound _ _ related).mp output, arguments⟩,
      Quotient.sound related⟩
  · rintro ⟨introduction, equal⟩
    have related := Quotient.exact equal
    exact ⟨(equation_sort_transport equations bound _ _ related).mpr introduction.output,
      introduction.value, related, introduction.arguments⟩

def test {generated : Generated} {model : Model generated} (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {admitted : Pattern → Prop} (backend : OrderedBackend generated bound admitted)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (interpreted : InputsInterpreted inputs) (effective : Effective model bound index inputs) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Test (sourceTheory generated bound index) admitted where
  predicate := Mettapedia.OSLF.NativeTypes.Semantics.Structural.predicate model bound index inputs
  evaluate := Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.evaluate (decompositionBackend backend index)
    (outputPredicate equations effective) (inputPredicates equations interpreted effective)
  positive budget source read := (decomposition_native_comparison model equations bound index inputs
    interpreted effective source).mp (Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.evaluate_positive
      (decompositionBackend backend index) (outputPredicate equations effective)
      (inputPredicates equations interpreted effective) budget source read)
  negative budget source read := fun holds =>
    Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.evaluate_negative
      (decompositionBackend backend index) (outputPredicate equations effective)
      (inputPredicates equations interpreted effective) budget source read
      ((decomposition_native_comparison model equations bound index inputs interpreted effective source).mpr holds)
  completionBudget := backend.completionBudget index
  complete_at := Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.evaluate_complete
    (decompositionBackend backend index) (outputPredicate equations effective)
    (inputPredicates equations interpreted effective)
  complete_above := (Mettapedia.OSLF.NativeTypes.Decision.Structural.Decomposition.test
    (decompositionBackend backend index) (outputPredicate equations effective)
    (inputPredicates equations interpreted effective)).complete_above

theorem test_generated_comparison {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr} {admitted : Pattern → Prop}
    (backend : OrderedBackend generated bound admitted) (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) (interpreted : InputsInterpreted inputs)
    (effective : Effective model bound index inputs) (source : Pattern) :
    (test equations backend index inputs interpreted effective).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model bound) index inputs).meaning source :=
  (Mettapedia.OSLF.NativeTypes.Semantics.Structural.generated_native_comparison model equations bound index inputs source).symm

/-- Equation-free decomposition is concrete: it decodes one source and keeps
its actual typed ordered arguments. Closure checks object representation. -/
def localBackend (generated : Generated) (bound : List TypeExpr) (empty : generated.plan.equations = []) :
    OrderedBackend generated bound (fun source => isObjectPattern source = true) where
  values _ index source := Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.decompositions generated.snapshot.language
    generated.snapshot.free bound (structuralDeclaration generated index) source
  closed _ _ source := isObjectPattern source
  sound _ index source value listed :=
    (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq empty bound _ source value.pattern).mpr
      (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.decomposition_sound listed).symm
  coverage _ index source closed value related := by
    have same := (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq empty bound _ source value.pattern).mp related
    exact ⟨value, Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.decomposition_complete closed value same.symm⟩
  completionBudget _ _ := 0
  complete_at _ _ sourceAdmitted := sourceAdmitted
  values_stable _ _ _ _ := rfl
  closed_stable _ _ _ _ := rfl
  ordered_coverage _ index source closed value related := by
    have same := (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq empty bound _ source value.pattern).mp related
    exact ⟨value, Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.decomposition_complete closed value same.symm,
      fun _ => .refl _⟩

/-- Chosen computational sort subobjects, bounded by the authored type checker.
The sort mask may distinguish the actual star and box domains. -/
def booleanModel (generated : Generated)
    (domain : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool) : Model generated :=
  fun bound =>
    {sortDomain carrier sort source :=
      checkHasType generated.snapshot.language generated.snapshot.free bound source carrier = true ∧
        domain bound carrier sort source = true
     carrierBounded _ _ _ inhabited := checkHasType_sound inhabited.1}

theorem booleanModel_equations {generated : Generated}
    (empty : generated.plan.equations = [])
    (domain : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool) :
    EquationsInterpreted (booleanModel generated domain) := by
  intro _ _ _ _ _ completed
  have impossible := completed.job.1
  rw [empty] at impossible
  exact False.elim (List.not_mem_nil impossible)

def booleanCode (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr)
    (sort : ModalHypercube.HSort) (accepts : Pattern → Bool) :
    Mettapedia.OSLF.NativeTypes.Modal.Rules.TypeCode generated.plan bound carrier sort where
  meaning source := checkHasType generated.snapshot.language generated.snapshot.free bound source carrier = true ∧
    accepts source = true
  bounded _ inhabited := checkHasType_sound inhabited.1

def booleanInputs (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool) :
    StructuralInputs generated bound index := fun position =>
  booleanCode generated bound (structuralDeclaration generated index).params[position].typeExpr
    (structuralInputSort generated index position) (accepts position)

theorem booleanInputs_interpreted {generated : Generated}
    (empty : generated.plan.equations = []) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool) :
    InputsInterpreted (booleanInputs generated bound index accepts) := by
  intro _ _ _ completed
  have impossible := completed.job.1
  rw [empty] at impossible
  exact False.elim (List.not_mem_nil impossible)

def booleanEffective (generated : Generated)
    (domain : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool) :
    Effective (booleanModel generated domain) bound index (booleanInputs generated bound index accepts) where
  output source := checkHasType generated.snapshot.language generated.snapshot.free bound source
    (.base (structuralDeclaration generated index).category) &&
    domain bound (.base (structuralDeclaration generated index).category) (structuralOutputSort generated index) source
  output_exact _ := Bool.and_eq_true_iff
  input position source :=
    (checkHasType generated.snapshot.language generated.snapshot.free bound source
      (structuralDeclaration generated index).params[position].typeExpr &&
      domain bound (structuralDeclaration generated index).params[position].typeExpr
        (structuralInputSort generated index position) source) &&
    (checkHasType generated.snapshot.language generated.snapshot.free bound source
      (structuralDeclaration generated index).params[position].typeExpr && accepts position source)
  input_exact _ _ := by simp only [Bool.and_eq_true]; rfl

def localTest (generated : Generated) (empty : generated.plan.equations = [])
    (domain : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Test (sourceTheory generated bound index) (fun source => isObjectPattern source = true) :=
  test (booleanModel_equations empty domain) (localBackend generated bound empty) index
    (booleanInputs generated bound index accepts) (booleanInputs_interpreted empty bound index accepts)
    (booleanEffective generated domain bound index accepts)

theorem localTest_native (generated : Generated) (empty : generated.plan.equations = [])
    (domain : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool) (source : Pattern) :
    (localTest generated empty domain bound index accepts).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (booleanModel generated domain bound) index
        (booleanInputs generated bound index accepts)).meaning source :=
  test_generated_comparison (booleanModel_equations empty domain) (localBackend generated bound empty)
    index (booleanInputs generated bound index accepts) (booleanInputs_interpreted empty bound index accepts)
    (booleanEffective generated domain bound index accepts) source

end Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated
