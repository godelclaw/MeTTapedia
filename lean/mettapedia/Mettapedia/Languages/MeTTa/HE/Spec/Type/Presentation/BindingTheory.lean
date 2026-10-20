import Mettapedia.Languages.MeTTa.MetavariableFrameStore
import Mathlib.Data.Nat.Pairing
import Std.Data.String.ToNat
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.PrincipalAlpha
import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Finite presentations of binding equation systems

An ordinary HE binding record is a finite first-order equation system.  This
module presents that whole system by one normal finite type substitution.
The construction uses the exact syntactic presentation matcher, not the
gradual type-matching lane, so `%Undefined%` and `Atom` remain ordinary
symbols here.

`BindingMaterializationRel` selects the ordinary ordered equation-fold
presentation. This is a specific readout profile: equal solution theories do
not by themselves determine its literal residual names or establish agreement
with a native query's narrowing and rendering policies.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.MatchSolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness

/-- Atom-valued equations denoted by an HE binding record. -/
def bindingAtomEquations (bindings : Bindings) : List (Atom × Atom) :=
  bindings.assignments.map (fun entry => (.var entry.1, entry.2)) ++
    bindings.equalities.map (fun edge => (.var edge.1, .var edge.2))

/-- Native binding satisfaction is pointwise satisfaction of its atom-valued
equation list. -/
theorem typeBindingSatisfied_iff_equations
    (valuation : String → Atom) (bindings : Bindings) :
    TypeBindingSatisfied valuation bindings ↔
      ∀ equation ∈ bindingAtomEquations bindings,
        applyTypeValuation valuation equation.1 =
          applyTypeValuation valuation equation.2 := by
  constructor
  · intro satisfied equation member
    rcases List.mem_append.mp member with assignment | equality
    · obtain ⟨⟨name, value⟩, assignmentMember, rfl⟩ :=
        List.mem_map.mp assignment
      simpa [applyTypeValuation] using
        satisfied.1 name value assignmentMember
    · obtain ⟨⟨left, right⟩, equalityMember, rfl⟩ :=
        List.mem_map.mp equality
      simpa [applyTypeValuation] using
        satisfied.2 left right equalityMember
  · intro equations
    constructor
    · intro name value member
      have equation := equations (.var name, value) (by
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨(name, value), member, rfl⟩)
      simpa [applyTypeValuation] using equation
    · intro left right member
      have equation := equations (.var left, .var right) (by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨(left, right), member, rfl⟩)
      simpa [applyTypeValuation] using equation

/-- One syntactic equation packages the complete native constraint record.
The two tuples retain equalities as well as assignments, including aliases. -/
def bindingLeftPacket (bindings : Bindings) : Atom :=
  .expression ((bindingAtomEquations bindings).map Prod.fst)

def bindingRightPacket (bindings : Bindings) : Atom :=
  .expression ((bindingAtomEquations bindings).map Prod.snd)

theorem bindingPacket_equation_iff (valuation : String → Atom) (bindings : Bindings) :
    applyTypeValuation valuation (bindingLeftPacket bindings) =
      applyTypeValuation valuation (bindingRightPacket bindings) ↔
    TypeBindingSatisfied valuation bindings := by
  rw [typeBindingSatisfied_iff_equations]
  simp only [bindingLeftPacket,bindingRightPacket,applyTypeValuation,List.map_map,
    Function.comp_def,Atom.expression.injEq,List.map_eq_map_iff]

/-- Left-to-right presentation of an ordered finite equation system. -/
inductive EquationListPresentationRel :
    List (Atom × Atom) → TypeSubst → TypeSubst → Prop where
  | nil (incoming : TypeSubst) :
      EquationListPresentationRel [] incoming incoming
  | cons {equation : Atom × Atom} {equations : List (Atom × Atom)}
      {incoming next output : TypeSubst} :
      AppliedTypePresentationMatchRel
        incoming equation.1 equation.2 next →
      EquationListPresentationRel equations next output →
      EquationListPresentationRel (equation :: equations) incoming output

/-- A normal incoming presentation stays normal across an equation fold. -/
theorem EquationListPresentationRel.output_normal
    {equations : List (Atom × Atom)} {incoming output : TypeSubst}
    (derivation : EquationListPresentationRel equations incoming output)
    (normal : incoming.Normal) : output.Normal := by
  induction derivation with
  | nil => exact normal
  | cons head _tail inductionHypothesis =>
      exact inductionHypothesis (head.output_normal normal)

/-- The equation fold presents exactly the conjunction of its incoming
theory and every ordered equation. -/
theorem EquationListPresentationRel.solutions
    {equations : List (Atom × Atom)} {incoming output : TypeSubst}
    (derivation : EquationListPresentationRel equations incoming output)
    (normal : incoming.Normal) (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation incoming ∧
        ∀ equation ∈ equations,
          applyTypeValuation valuation equation.1 =
            applyTypeValuation valuation equation.2 := by
  induction derivation with
  | nil => simp
  | @cons equation equations incoming next output head tail
      inductionHypothesis =>
      have nextNormal := head.output_normal normal
      rw [inductionHypothesis nextNormal,
        MatchSolutionTheory.AppliedTypePresentationMatchRel.solutions
          head normal valuation]
      constructor
      · rintro ⟨⟨incomingSatisfied, headEquation⟩, tailEquations⟩
        refine ⟨incomingSatisfied, ?_⟩
        intro current member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact headEquation
        · exact tailEquations current tailMember
      · rintro ⟨incomingSatisfied, allEquations⟩
        exact ⟨⟨incomingSatisfied,
          allEquations equation List.mem_cons_self⟩,
          fun current member =>
            allEquations current (List.mem_cons_of_mem _ member)⟩

/-- Every satisfiable ordered equation system has a normal exact finite
presentation extending the incoming normal presentation. -/
theorem EquationListPresentationRel.exists_of_satisfied
    {valuation : String → Atom} {incoming : TypeSubst}
    (normal : incoming.Normal)
    (incomingSatisfied : TypeSubstSatisfied valuation incoming) :
    ∀ {equations : List (Atom × Atom)},
      (∀ equation ∈ equations,
        applyTypeValuation valuation equation.1 =
          applyTypeValuation valuation equation.2) →
      ∃ output,
        EquationListPresentationRel equations incoming output ∧
          output.Normal ∧ TypeSubstSatisfied valuation output := by
  intro equations equationsSatisfied
  induction equations generalizing incoming with
  | nil => exact ⟨incoming, .nil incoming, normal, incomingSatisfied⟩
  | cons equation equations inductionHypothesis =>
      obtain ⟨next, head, nextNormal, nextSatisfied⟩ :=
        AppliedTypePresentationMatchRel.exists_of_satisfied
          normal incomingSatisfied equation.1 equation.2
            (equationsSatisfied equation List.mem_cons_self)
      obtain ⟨output, tail, outputNormal, outputSatisfied⟩ :=
        inductionHypothesis nextNormal nextSatisfied
          (fun current member => equationsSatisfied current
            (List.mem_cons_of_mem _ member))
      exact ⟨output, .cons head tail, outputNormal, outputSatisfied⟩

/-- An actual fold of a whole binding theory earns normality and its complete
solution theory together. Neither property is a separate admission premise. -/
theorem EquationListPresentationRel.bindingTheory
    {bindings : Bindings} {presentation : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations bindings) [] presentation) :
    presentation.Normal ∧ ∀ valuation,
      TypeSubstSatisfied valuation presentation ↔ TypeBindingSatisfied valuation bindings := by
  refine ⟨fold.output_normal TypeSubst.normal_empty, ?_⟩
  intro valuation
  rw [fold.solutions TypeSubst.normal_empty, typeBindingSatisfied_iff_equations]
  simp [TypeSubstSatisfied]

/-- Construct the syntactic fold itself, retaining the derivation needed by
operational materialization rather than only its semantic consequences. -/
theorem exists_binding_presentation {bindings : Bindings}
    (satisfiable : ∃ valuation, TypeBindingSatisfied valuation bindings) :
    ∃ presentation, EquationListPresentationRel (bindingAtomEquations bindings) [] presentation := by
  obtain ⟨valuation, satisfied⟩ := satisfiable
  obtain ⟨presentation, fold, _, _⟩ := EquationListPresentationRel.exists_of_satisfied
    TypeSubst.normal_empty (by simp [TypeSubstSatisfied])
    ((typeBindingSatisfied_iff_equations valuation bindings).mp satisfied)
  exact ⟨presentation, fold⟩

/-- Every satisfiable finite HE binding theory has a normal finite
presentation with exactly the same solution set. -/
theorem exists_normal_exact_presentation
    {bindings : Bindings}
    (satisfiable : ∃ valuation, TypeBindingSatisfied valuation bindings) :
    ∃ presentation,
      presentation.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentation ↔
            TypeBindingSatisfied valuation bindings := by
  obtain ⟨presentation, fold⟩ := exists_binding_presentation satisfiable
  exact ⟨presentation, fold.bindingTheory⟩

/-- Materialization of a finished operand under its current independent
binding theory. The presentation is generated by the syntactic equation fold;
no executable resolver or preferred backend spelling enters this relation. -/
def BindingMaterializationRel (bindings : Bindings) (raw normalized : Atom) : Prop :=
  ∃ presentation, EquationListPresentationRel (bindingAtomEquations bindings) [] presentation ∧
    normalized = presentation.apply raw

namespace BindingMaterializationRel

/-- Expose the same constructed presentation with its earned logical laws. -/
theorem presentation {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized) :
    ∃ presentation,
      EquationListPresentationRel (bindingAtomEquations bindings) [] presentation ∧
      presentation.Normal ∧
      (∀ valuation, TypeSubstSatisfied valuation presentation ↔ TypeBindingSatisfied valuation bindings) ∧
      normalized = presentation.apply raw := by
  obtain ⟨presentation, fold, result⟩ := materialized
  exact ⟨presentation, fold, fold.bindingTheory.1, fold.bindingTheory.2, result⟩

theorem exists_of_satisfiable {bindings : Bindings}
    (satisfiable : ∃ valuation, TypeBindingSatisfied valuation bindings) (raw : Atom) :
    ∃ normalized, BindingMaterializationRel bindings raw normalized := by
  obtain ⟨presentation, fold⟩ := exists_binding_presentation satisfiable
  exact ⟨presentation.apply raw, presentation, fold, rfl⟩

/-- A successful materialization carries a model; inconsistent bindings cannot
be admitted by supplying an arbitrary normalization result. -/
theorem satisfiable {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized) :
    ∃ valuation, TypeBindingSatisfied valuation bindings := by
  obtain ⟨presentation, fold, _⟩ := materialized
  exact ⟨presentedValuation presentation,
    (fold.bindingTheory.2 _).mp (normal_presentedValuation_satisfied fold.bindingTheory.1)⟩

/-- A model-independent value is produced by the actual finite equation
presentation. The witness is its canonical syntactic model, so a semantic
constant cannot be supplied without a realizable binding theory. -/
theorem of_model_constant {bindings : Bindings} {raw normalized : Atom}
    (satisfiable : ∃ valuation, TypeBindingSatisfied valuation bindings)
    (forced : ∀ valuation, TypeBindingSatisfied valuation bindings →
      applyTypeValuation valuation raw = normalized) :
    BindingMaterializationRel bindings raw normalized := by
  obtain ⟨presentation, fold⟩ := exists_binding_presentation satisfiable
  refine ⟨presentation, fold, ?_⟩
  have model := (fold.bindingTheory.2 _).mp
    (normal_presentedValuation_satisfied fold.bindingTheory.1)
  simpa only [applyTypeValuation_presented_eq_apply] using (forced _ model).symm

/-- A fixed pattern interpretation determines every covered template, even
when the pattern contains several or repeated variables. -/
theorem of_determined_pattern
    {bindings : Bindings} {pattern template observed : Atom}
    (covered : ∀ name ∈ TypeSubst.typeVars template, name ∈ TypeSubst.typeVars pattern)
    (model : String → Atom) (satisfied : TypeBindingSatisfied model bindings)
    (patternFixed : ∀ valuation, TypeBindingSatisfied valuation bindings →
      applyTypeValuation valuation pattern = observed) :
    BindingMaterializationRel bindings template (applyTypeValuation model template) := by
  apply BindingMaterializationRel.of_model_constant ⟨model, satisfied⟩
  intro valuation valuationSatisfied
  exact applyTypeValuation_template_eq_of_pattern_eq valuation model pattern template covered
    ((patternFixed valuation valuationSatisfied).trans (patternFixed model satisfied).symm)


theorem exists_iff_satisfiable (bindings : Bindings) (raw : Atom) :
    (∃ normalized, BindingMaterializationRel bindings raw normalized) ↔
      ∃ valuation, TypeBindingSatisfied valuation bindings :=
  ⟨fun ⟨_, materialized⟩ => materialized.satisfiable, fun model => exists_of_satisfiable model raw⟩

/-- Materialization preserves the operand in every model of the complete
current binding theory, including all correlated residual occurrences. -/
theorem preserves_model {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized)
    (valuation : String → Atom) (satisfied : TypeBindingSatisfied valuation bindings) :
    applyTypeValuation valuation normalized = applyTypeValuation valuation raw := by
  obtain ⟨presentation, fold, rfl⟩ := materialized
  exact ((fold.bindingTheory.2 valuation).mpr satisfied).absorbs raw

@[simp] theorem empty_iff (raw normalized : Atom) :
    BindingMaterializationRel Bindings.empty raw normalized ↔ normalized = raw := by
  constructor
  · rintro ⟨presentation, fold, result⟩
    change EquationListPresentationRel [] [] presentation at fold
    cases fold
    simpa using result
  · intro same
    subst normalized
    exact ⟨[], .nil [], (TypeSubst.apply_empty raw).symm⟩

theorem empty (raw : Atom) : BindingMaterializationRel Bindings.empty raw raw :=
  (empty_iff raw raw).mpr rfl

/-- A specific constructed presentation licenses a structurally fixed operand.
Fixedness of some other presentation is not silently transferred to this fold. -/
theorem of_fixed_presentation {bindings : Bindings} {presentation : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations bindings) [] presentation)
    (raw : Atom) (fixed : presentation.apply raw = raw) :
    BindingMaterializationRel bindings raw raw :=
  ⟨presentation, fold, fixed.symm⟩

theorem of_unassigned_variables {bindings : Bindings} {presentation : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations bindings) [] presentation)
    (raw : Atom)
    (unassigned : ∀ name ∈ TypeSubst.typeVars raw, name ∉ presentation.keys) :
    BindingMaterializationRel bindings raw raw :=
  of_fixed_presentation fold raw (TypeSubst.apply_eq_self_of_variables_not_keys _ _ unassigned)

/-- Reusing the same normal presentation is idempotent. Other legal
presentations may choose another representative of a residual equality class. -/
theorem reapply_same_presentation {bindings : Bindings} {presentation : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations bindings) [] presentation) (raw : Atom) :
    BindingMaterializationRel bindings (presentation.apply raw) (presentation.apply raw) :=
  of_fixed_presentation fold _ (fold.bindingTheory.1.apply_idempotent raw)

theorem closed_result {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized)
    (closed : TypeSubst.typeVars raw = []) : normalized = raw := by
  obtain ⟨presentation, _, rfl⟩ := materialized
  apply TypeSubst.apply_eq_self_of_variables_not_keys
  intro name member
  simp [closed] at member

/-- Closed operands are unchanged, but their frame must still be satisfiable. -/
theorem closed_iff (bindings : Bindings) (raw normalized : Atom)
    (closed : TypeSubst.typeVars raw = []) :
    BindingMaterializationRel bindings raw normalized ↔
      normalized = raw ∧ ∃ valuation, TypeBindingSatisfied valuation bindings := by
  constructor
  · intro materialized
    exact ⟨materialized.closed_result closed, materialized.satisfiable⟩
  · rintro ⟨same, model⟩
    subst normalized
    obtain ⟨normalized, materialized⟩ := exists_of_satisfiable model raw
    exact materialized.closed_result closed ▸ materialized

@[simp] theorem symbol_iff (bindings : Bindings) (symbol : String) (normalized : Atom) :
    BindingMaterializationRel bindings (.symbol symbol) normalized ↔
      normalized = .symbol symbol ∧ ∃ valuation, TypeBindingSatisfied valuation bindings :=
  closed_iff bindings _ _ rfl

@[simp] theorem grounded_iff (bindings : Bindings)
    (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) (normalized : Atom) :
    BindingMaterializationRel bindings (.grounded value) normalized ↔
      normalized = .grounded value ∧ ∃ valuation, TypeBindingSatisfied valuation bindings :=
  closed_iff bindings _ _ rfl

end BindingMaterializationRel

/-- One nonrecursive assignment is normalized by the actual independent
ordinary presentation rule, not by a model-chosen replacement. -/
theorem single_assignment_presentation (name : String) (value : Atom)
    (fresh : name ∉ TypeSubst.typeVars value) :
    EquationListPresentationRel
      (bindingAtomEquations (⟨[(name, value)], []⟩ : Bindings)) [] [(name, value)] := by
  change EquationListPresentationRel [(.var name, value)] [] [(name, value)]
  refine .cons (.ordinary (TypeSubst.apply_empty _) (TypeSubst.apply_empty _) ?_) (.nil _)
  simpa [TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase] using
    (AppliedReducedTypeMatchRel.bindLeft (substitution := []) (name := name) fresh)

theorem BindingMaterializationRel.single_assignment
    (name : String) (value raw : Atom) (fresh : name ∉ TypeSubst.typeVars value) :
    BindingMaterializationRel (⟨[(name, value)], []⟩ : Bindings) raw
      (TypeSubst.apply [(name, value)] raw) :=
  ⟨[(name, value)], single_assignment_presentation name value fresh, rfl⟩

/-! ## Boundary examples -/

/-- Positive: a mixed assignment/equality theory has an exact normal finite
presentation. -/
theorem mixed_binding_theory_presentable :
    ∃ presentation,
      presentation.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentation ↔
            TypeBindingSatisfied valuation
              (⟨[("x", .symbol "A")], [("y", "z")]⟩ : Bindings) := by
  apply exists_normal_exact_presentation
  refine ⟨fun name => if name = "x" then .symbol "A" else .symbol "C", ?_⟩
  constructor
  · intro name value member
    simp at member
    rcases member with ⟨rfl, rfl⟩
    simp [applyTypeValuation]
  · intro left right member
    simp at member
    rcases member with ⟨rfl, rfl⟩
    simp

/-- Negative: the inconsistent equation `$x = A` and `$x = B` has no
satisfying valuation. -/
theorem incompatible_binding_theory_not_satisfiable :
    ¬∃ valuation,
      TypeBindingSatisfied valuation
        (⟨[("x", .symbol "A"), ("x", .symbol "B")], []⟩ : Bindings) := by
  rintro ⟨valuation, satisfied⟩
  have first := satisfied.1 "x" (.symbol "A") (by simp)
  have second := satisfied.1 "x" (.symbol "B") (by simp)
  simp [applyTypeValuation] at first second
  have impossible : (Atom.symbol "A") = .symbol "B" :=
    first.symm.trans second
  simp at impossible

/-- A finished alias can expose a return marker while retaining repeated
unassigned variables in the returned value. -/
theorem alias_materializes_return_with_correlated_residual :
    let returned := Atom.expression [.symbol "return",
      .expression [.symbol "pair", .var "free", .var "free"]]
    BindingMaterializationRel (⟨[("pending", returned)], []⟩ : Bindings)
      (.var "pending") returned := by
  intro returned
  simpa [TypeSubst.apply, TypeSubst.lookup] using
    BindingMaterializationRel.single_assignment "pending" returned (.var "pending")
      (by simp [returned, TypeSubst.typeVars, TypeSubst.typeVarsList])

/-- A finished alias can also reveal another instruction-shaped expression.
The evaluator decides when that materialized result is scheduled. -/
theorem alias_materializes_instruction :
    let instruction := Atom.expression [.symbol "cons-atom", .symbol "a", .expression []]
    BindingMaterializationRel (⟨[("pending", instruction)], []⟩ : Bindings)
      (.var "pending") instruction := by
  intro instruction
  simpa [TypeSubst.apply, TypeSubst.lookup] using
    BindingMaterializationRel.single_assignment "pending" instruction (.var "pending")
      (by simp [instruction, TypeSubst.typeVars, TypeSubst.typeVarsList])

/-- An open operand unrelated to a nonempty frame stays open. -/
theorem unrelated_variable_is_fixed :
    BindingMaterializationRel (⟨[("bound", .symbol "A")], []⟩ : Bindings)
      (.expression [.var "free", .var "free"]) (.expression [.var "free", .var "free"]) := by
  simpa [TypeSubst.apply, TypeSubst.lookup] using
    BindingMaterializationRel.single_assignment "bound" (.symbol "A")
      (.expression [.var "free", .var "free"]) (by simp [TypeSubst.typeVars])

/-- Invalid frames cannot materialize even a closed operand. -/
theorem inconsistent_binding_theory_cannot_materialize (raw : Atom) :
    ¬∃ normalized, BindingMaterializationRel
      (⟨[("x", .symbol "A"), ("x", .symbol "B")], []⟩ : Bindings) raw normalized := by
  rw [BindingMaterializationRel.exists_iff_satisfiable]
  exact incompatible_binding_theory_not_satisfiable

/-- Without a binding equation, materialization cannot invent a return head. -/
theorem empty_frame_cannot_expose_return (name : String) (value : Atom) :
    ¬BindingMaterializationRel Bindings.empty (.var name)
      (.expression [.symbol "return", value]) := by
  simp only [BindingMaterializationRel.empty_iff, reduceCtorEq, not_false_eq_true]

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-- The chronological equation fold retains every equation and its position. -/
theorem EquationListPresentationRel.rename (permutation : Equiv.Perm String)
    {equations : List (Atom × Atom)} {incoming output : TypeSubst}
    (derivation : EquationListPresentationRel equations incoming output) :
    EquationListPresentationRel
      (equations.map (fun equation =>
        (renameTypeVars permutation equation.1, renameTypeVars permutation equation.2)))
      (incoming.renameVars permutation) (output.renameVars permutation) := by
  induction derivation with
  | nil incoming => exact .nil _
  | cons head _tail ih =>
      exact .cons (AppliedTypePresentationMatchRel.rename permutation head) ih

theorem bindingAtomEquations_renameBindings (rename : String → String)
    (bindings : Bindings) :
    bindingAtomEquations (renameBindings rename bindings) =
      (bindingAtomEquations bindings).map
        (fun equation => (renameTypeVars rename equation.1, renameTypeVars rename equation.2)) := by
  simp [bindingAtomEquations, renameBindings, List.map_append,
    List.map_map, Function.comp_def, renameTypeVars]

/-- Independent materialization transports the complete binding record and
observed syntax with the same permutation. -/
theorem BindingMaterializationRel.rename (permutation : Equiv.Perm String)
    {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized) :
    BindingMaterializationRel (renameBindings permutation bindings)
      (renameTypeVars permutation raw) (renameTypeVars permutation normalized) := by
  obtain ⟨presentation, fold, materialized⟩ := materialized
  refine ⟨presentation.renameVars permutation, ?_, ?_⟩
  · rw [bindingAtomEquations_renameBindings]
    exact EquationListPresentationRel.rename permutation fold
  · rw [materialized, TypeSubst.apply_renameVars]

theorem BindingMaterializationRel.rename_iff (permutation : Equiv.Perm String)
    (bindings : Bindings) (raw normalized : Atom) :
    BindingMaterializationRel (renameBindings permutation bindings)
        (renameTypeVars permutation raw) (renameTypeVars permutation normalized) ↔
      BindingMaterializationRel bindings raw normalized := by
  constructor
  · intro materialized
    simpa only [renameBindings_perm_inverse, renameTypeVars_perm_inverse] using
      materialized.rename permutation.symm
  · exact fun materialized => materialized.rename permutation


end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Exact Spec.Type.Presentation.Freshness
open Spec.Bindings.ScopeObservation

/-- The actual ordered normalization fold cannot introduce a name absent
from its initial presentation and every source equation. -/
theorem EquationListPresentationRel.avoids
    {equations : List (Atom×Atom)} {incoming output : TypeSubst}
    {forbidden : List String}
    (derivation : EquationListPresentationRel equations incoming output)
    (initial : incoming.Avoids forbidden)
    (source : ∀ equation∈equations,
      AtomAvoids equation.1 forbidden ∧ AtomAvoids equation.2 forbidden) :
    output.Avoids forbidden := by
  induction derivation with
  | nil => exact initial
  | @cons equation equations incoming next output head tail ih =>
    exact ih (Freshness.appliedTypePresentationMatch_output_avoids head initial
      (source equation (by simp)).1 (source equation (by simp)).2)
      (fun e member=>source e (List.mem_cons_of_mem _ member))

/-- Every key and value variable in the normalization input is part of the
binding record's full support, including equality-only and duplicate rows. -/
theorem binding_equations_avoid {bindings : Bindings} {forbidden : List String}
    (outside : ∀ name∈forbidden,name∉specBindingVars bindings) :
    ∀ equation∈bindingAtomEquations bindings,
      AtomAvoids equation.1 forbidden ∧ AtomAvoids equation.2 forbidden := by
  intro equation member
  rcases List.mem_append.mp member with assigned | equated
  · obtain ⟨⟨key,value⟩,stored,rfl⟩ := List.mem_map.mp assigned
    constructor
    · intro name occurs forbiddenName
      have same : name=key := by simpa [TypeSubst.typeVars] using occurs
      subst name
      apply outside key forbiddenName
      simp only [specBindingVars,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨(key,value),stored,by simp⟩
    · intro name occurs forbiddenName
      apply outside name forbiddenName
      simp only [specBindingVars,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨(key,value),stored,by simp [occurs]⟩
  · obtain ⟨⟨left,right⟩,stored,rfl⟩ := List.mem_map.mp equated
    constructor
    · intro name occurs forbiddenName
      have same : name=left := by simpa [TypeSubst.typeVars] using occurs
      subst name
      apply outside left forbiddenName
      simp only [specBindingVars,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨(left,right),stored,by simp⟩
    · intro name occurs forbiddenName
      have same : name=right := by simpa [TypeSubst.typeVars] using occurs
      subst name
      apply outside right forbiddenName
      simp only [specBindingVars,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨(left,right),stored,by simp⟩

theorem EquationListPresentationRel.binding_avoids
    {bindings : Bindings} {output : TypeSubst} {forbidden : List String}
    (derivation : EquationListPresentationRel (bindingAtomEquations bindings) [] output)
    (outside : ∀ name∈forbidden,name∉specBindingVars bindings) :
    output.Avoids forbidden :=
  derivation.avoids (TypeSubst.avoids_empty _) (binding_equations_avoid outside)

/-- Outside public references are fixed literally by every constructed
source materialization. Residual representatives inside the theory remain
free to use the declared alpha observer. -/
theorem BindingMaterializationRel.outside_result
    {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized)
    (outside : ∀ name∈TypeSubst.typeVars raw,name∉specBindingVars bindings) :
    normalized=raw := by
  obtain ⟨presentation,fold,rfl⟩ := materialized
  apply TypeSubst.apply_eq_self_of_variables_not_keys
  intro name occurs key
  exact (fold.binding_avoids outside).keys name key occurs

/-- Materialization can only expose a variable from the actual operand or
from its complete binding support. No chosen fresh names enter this fold. -/
theorem BindingMaterializationRel.variables_subset
    {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized)
    {name : String} (occurs : name∈TypeSubst.typeVars normalized) :
    name∈TypeSubst.typeVars raw ∨ name∈specBindingVars bindings := by
  by_cases rawName : name∈TypeSubst.typeVars raw
  · exact Or.inl rawName
  right
  by_contra bindingName
  obtain ⟨presentation,fold,rfl⟩ := materialized
  have avoided : presentation.Avoids [name] := fold.binding_avoids (by simpa using bindingName)
  have valueFresh := TypeSubst.apply_variable_avoids avoided.values raw
    (fun candidate found same=>rawName (by simpa using (List.mem_singleton.mp same) ▸ found))
  exact valueFresh name occurs (by simp)

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-- Conjugating a normal principal presentation by a model-fixed permutation
retains its whole theory, while changing its residual representative. The
operand itself remains unchanged. This statement does not claim that the
chronological fold over the original record selected that representative. -/
theorem EquationListPresentationRel.model_fixed_representative
    {bindings : Bindings} {presentation : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations bindings) [] presentation)
    (p : Equiv.Perm String)
    (fixed : ∀ valuation,TypeBindingSatisfied valuation bindings →
      ∀ name,valuation (p name)=valuation name) :
    (presentation.renameVars p).Normal ∧
    (∀ valuation,TypeSubstSatisfied valuation (presentation.renameVars p) ↔
      TypeBindingSatisfied valuation bindings) ∧
    (∀ raw,(presentation.renameVars p).apply raw=renameTypeVars p (presentation.apply raw)) := by
  have renamedFold : EquationListPresentationRel
      (bindingAtomEquations (renameBindings p bindings)) [] (presentation.renameVars p) := by
    rw [bindingAtomEquations_renameBindings]
    exact fold.rename p
  refine ⟨renamedFold.bindingTheory.1,?_,?_⟩
  · intro valuation
    exact (renamedFold.bindingTheory.2 valuation).trans
      (QueryBindingProjection.renameBindings_theory_of_model_fixed bindings p fixed valuation)
  · intro raw
    have presentedModel : TypeBindingSatisfied (presentedValuation presentation) bindings :=
      (fold.bindingTheory.2 _).mp (normal_presentedValuation_satisfied fold.bindingTheory.1)
    have inverseFixed (name : String) :
        presentedValuation presentation (p.symm name)=presentedValuation presentation name := by
      have same := fixed _ presentedModel (p.symm name)
      simpa only [p.apply_symm_apply] using same.symm
    have unchanged : presentation.apply (renameTypeVars p.symm raw)=presentation.apply raw := by
      simpa only [applyTypeValuation_presented_eq_apply] using
        applyTypeValuation_model_fixed p.symm (presentedValuation presentation) inverseFixed raw
    have renamed := TypeSubst.apply_renameVars p presentation (renameTypeVars p.symm raw)
    have inverse : renameTypeVars p (renameTypeVars p.symm raw)=raw := by
      simpa only [Equiv.symm_symm] using renameTypeVars_perm_inverse p.symm raw
    simpa only [inverse,unchanged] using renamed

/-- One model-fixed representative is still materialized by the original
fold relation, over its renamed record. That record retains complete models
and support; it is not asserted to be the original raw merge endpoint. -/
theorem BindingMaterializationRel.model_fixed_representative
    {bindings : Bindings} {raw normalized : Atom}
    (materialized : BindingMaterializationRel bindings raw normalized)
    (p : Equiv.Perm String)
    (fixed : ∀ valuation,TypeBindingSatisfied valuation bindings →
      ∀ name,valuation (p name)=valuation name) :
    BindingMaterializationRel (renameBindings p bindings) raw (renameTypeVars p normalized) := by
  obtain ⟨presentation,fold,rfl⟩:=materialized
  refine ⟨presentation.renameVars p,?_,(fold.model_fixed_representative p fixed).2.2 raw |>.symm⟩
  rw [bindingAtomEquations_renameBindings]
  exact fold.rename p

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Type.Presentation.Theory

/-- Fixed ordered equations determine the entire literal finite presentation.
No normality or satisfiability assumption is needed for uniqueness. -/
theorem EquationListPresentationRel.output_eq
    {equations : List (Atom × Atom)} {incoming first second : TypeSubst}
    (one : EquationListPresentationRel equations incoming first)
    (two : EquationListPresentationRel equations incoming second) : first = second := by
  induction one generalizing second with
  | nil => cases two; rfl
  | cons head tail inductionHypothesis =>
      cases two with
      | cons otherHead otherTail =>
          have same := head.output_eq otherHead
          cases same
          exact inductionHypothesis otherTail

/-- The historical materializer is functional on a fixed binding record. -/
theorem BindingMaterializationRel.output_eq
    {bindings : Bindings} {raw first second : Atom}
    (one : BindingMaterializationRel bindings raw first)
    (two : BindingMaterializationRel bindings raw second) : first = second := by
  obtain ⟨firstTable, firstFold, rfl⟩ := one
  obtain ⟨secondTable, secondFold, rfl⟩ := two
  rw [firstFold.output_eq secondFold]

/-- One constructed source table serves every operand. Independent uses of
the historical materialization relation cannot choose different tables. -/
theorem BindingMaterializationRel.uniform_of_satisfiable {bindings : Bindings}
    (model : ∃ valuation, TypeBindingSatisfied valuation bindings) :
    ∃ presentation,
      EquationListPresentationRel (bindingAtomEquations bindings) [] presentation ∧
      presentation.Normal ∧
      (∀ valuation, TypeSubstSatisfied valuation presentation ↔
        TypeBindingSatisfied valuation bindings) ∧
      (∀ raw normalized, BindingMaterializationRel bindings raw normalized ↔
        normalized = presentation.apply raw) := by
  obtain ⟨presentation, fold⟩ := exists_binding_presentation model
  refine ⟨presentation, fold, fold.bindingTheory.1, fold.bindingTheory.2, ?_⟩
  intro raw normalized
  constructor
  · rintro ⟨other, otherFold, output⟩
    simpa only [otherFold.output_eq fold] using output
  · intro output
    exact ⟨presentation, fold, output⟩

/-- A small equation fork exposes the ordered selector's residual name. -/
theorem fork_equality_presentation (hub left right : String)
    (hubLeft : hub ≠ left) (hubRight : hub ≠ right) (leftRight : left ≠ right) :
    EquationListPresentationRel
      [(.var hub, .var left), (.var hub, .var right)] []
      [(left, .var right), (hub, .var right)] := by
  have first : AppliedTypePresentationMatchRel [] (.var hub) (.var left)
      [(hub, .var left)] := by
    refine .ordinary (TypeSubst.apply_empty _) (TypeSubst.apply_empty _) ?_
    simpa [TypeSubst.bind, TypeSubst.erase] using
      (AppliedReducedTypeMatchRel.bindLeft (substitution := [])
        (name := hub) (right := .var left) (by simpa [TypeSubst.typeVars] using hubLeft))
  have second : AppliedTypePresentationMatchRel [(hub, .var left)] (.var hub) (.var right)
      [(left, .var right), (hub, .var right)] := by
    refine .ordinary (resolvedLeft := .var left) (resolvedRight := .var right) ?_ ?_ ?_
    · simp [TypeSubst.apply, TypeSubst.lookup]
    · simp [TypeSubst.apply, TypeSubst.lookup, Ne.symm hubRight]
    · simpa [TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase,
        TypeSubst.applyAssignment, Ne.symm hubRight, hubLeft] using
      (AppliedReducedTypeMatchRel.bindLeft (substitution := [(hub, .var left)])
        (name := left) (right := .var right) (by simpa [TypeSubst.typeVars] using leftRight))
  exact .cons first (.cons second (.nil _))

/-- Uniqueness is a property of a fixed ordered record, not invariance under
reordering its relations. Both records retain the same full solution theory,
but the historical source selector gives different jointly shared names. -/
theorem historical_readout_can_change_under_relation_permutation :
    let first : Bindings := ⟨[], [("a", "b"), ("a", "c")]⟩
    let second : Bindings := ⟨[], [("a", "c"), ("a", "b")]⟩
    let raw := Atom.expression [.var "a", .var "a"]
    BindingRecordPerm first second ∧
      BindingMaterializationRel first raw (.expression [.var "c", .var "c"]) ∧
      BindingMaterializationRel second raw (.expression [.var "b", .var "b"]) ∧
      ¬BindingMaterializationRel second raw (.expression [.var "c", .var "c"]) := by
  dsimp only
  have firstFold := fork_equality_presentation "a" "b" "c" (by decide) (by decide) (by decide)
  have secondFold := fork_equality_presentation "a" "c" "b" (by decide) (by decide) (by decide)
  have first : BindingMaterializationRel
      (⟨[], [("a", "b"), ("a", "c")]⟩ : Bindings)
      (.expression [.var "a", .var "a"]) (.expression [.var "c", .var "c"]) := by
    exact ⟨_, firstFold, by simp [TypeSubst.apply, TypeSubst.lookup]⟩
  have second : BindingMaterializationRel
      (⟨[], [("a", "c"), ("a", "b")]⟩ : Bindings)
      (.expression [.var "a", .var "a"]) (.expression [.var "b", .var "b"]) := by
    exact ⟨_, secondFold, by simp [TypeSubst.apply, TypeSubst.lookup]⟩
  refine ⟨⟨.refl _, .swap _ _ []⟩, first, second, ?_⟩
  intro other
  have same := other.output_eq second
  exact (by decide : Atom.expression [Atom.var "c", Atom.var "c"] ≠
    .expression [.var "b", .var "b"]) same

/-! ## Certified finite readout for a retained binding frame -/

/-- A finite representation of one complete independent binding record.
The representative choice is certified once for every future operand. -/
structure ReadoutCertificate (bindings : Bindings) (table : TypeSubst) : Prop where
  normal : table.Normal
  representative : ∃ (folded : TypeSubst) (choice : Equiv.Perm String),
    EquationListPresentationRel (bindingAtomEquations bindings) [] folded ∧
    (∀ valuation, TypeBindingSatisfied valuation bindings →
      ∀ name, valuation (choice name) = valuation name) ∧
    (∀ name, name ∉ specBindingVars bindings → choice name = name) ∧
    ∀ atom, table.apply atom = (folded.renameVars choice).apply atom

namespace ReadoutCertificate

theorem of_fold {bindings : Bindings} {table : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations bindings) [] table) :
    ReadoutCertificate bindings table := by
  refine ⟨fold.bindingTheory.1, table, Equiv.refl String, fold, ?_, ?_, ?_⟩
  · intro valuation _ name
    rfl
  · intro name _
    rfl
  · intro atom
    simp only [Equiv.coe_refl, TypeSubst.renameVars_id]

theorem theory {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (valuation : String → Atom) :
    TypeSubstSatisfied valuation table ↔ TypeBindingSatisfied valuation bindings := by
  obtain ⟨folded, choice, fold, fixed, _outside, allAtoms⟩ := certified.representative
  have selected := fold.model_fixed_representative choice fixed
  exact (TypeSubst.satisfied_iff_of_same_readout certified.normal selected.1
    (fun name => allAtoms (.var name)) valuation).trans (selected.2.1 valuation)

theorem satisfiable {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) :
    ∃ valuation, TypeBindingSatisfied valuation bindings :=
  ⟨presentedValuation table, (certified.theory _).mp
    (normal_presentedValuation_satisfied certified.normal)⟩

/-- A model-independent source value is the literal read of the retained
certified table, regardless of its chosen residual representatives. -/
theorem forced_read {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (raw value : Atom)
    (forced : ∀ valuation, TypeBindingSatisfied valuation bindings →
      applyTypeValuation valuation raw = value) : table.apply raw = value := by
  have model := (certified.theory (presentedValuation table)).mp
    (normal_presentedValuation_satisfied certified.normal)
  simpa only [applyTypeValuation_presented_eq_apply] using forced _ model

/-- Any normal finite table with exactly the record's solution theory earns
one representative certificate for all future operands. The finite tuple
contains the whole binding support and every table key; its model-fixed
permutation then extends to all variables and all atoms. -/
theorem of_normal_theory {bindings : Bindings} {table : TypeSubst}
    (normal : table.Normal)
    (sameSolutions : ∀ valuation,
      TypeSubstSatisfied valuation table ↔ TypeBindingSatisfied valuation bindings) :
    ReadoutCertificate bindings table := by
  have model : ∃ valuation, TypeBindingSatisfied valuation bindings :=
    ⟨presentedValuation table, (sameSolutions _).mp
      (normal_presentedValuation_satisfied normal)⟩
  obtain ⟨folded, fold⟩ := exists_binding_presentation model
  let scope := specBindingVars bindings ++ table.keys
  let tuple : Atom := .expression (scope.map Atom.var)
  have alpha := PrincipalAlpha.observedTypeAlpha_of_solution_equiv
    fold.bindingTheory.1 normal
    (fun valuation => (fold.bindingTheory.2 valuation).trans (sameSolutions valuation).symm)
    tuple
  obtain ⟨choice, observed, fixedModels, _support⟩ :=
    PrincipalAlpha.observedTypeAlpha_exists_model_fixed_permutation alpha
      (fun valuation : {v : String → Atom // TypeBindingSatisfied v bindings} => valuation.1)
      (fun valuation => ((fold.bindingTheory.2 valuation.1).mpr valuation.2).absorbs tuple |>.trans
        (((sameSolutions valuation.1).mpr valuation.2).absorbs tuple).symm)
  have fixed : ∀ valuation, TypeBindingSatisfied valuation bindings →
      ∀ name, valuation (choice name) = valuation name := by
    intro valuation satisfied name
    exact fixedModels ⟨valuation, satisfied⟩ name
  have outside := Spec.Bindings.ScopeObservation.model_fixed_fixes_outside choice model fixed
  let selected := folded.renameVars choice
  have selectedRead := (fold.model_fixed_representative choice fixed).2.2
  have mapped : scope.map (fun name => table.apply (.var name)) =
      scope.map (fun name => selected.apply (.var name)) := by
    have equal := observed.trans (selectedRead tuple).symm
    simpa only [tuple, TypeSubst.apply, List.map_map, Atom.expression.injEq,
      Function.comp_def, selected] using equal
  have each : ∀ name ∈ scope, table.apply (.var name) = selected.apply (.var name) := by
    have mapEqual : ∀ names : List String,
        names.map (fun name => table.apply (.var name)) =
          names.map (fun name => selected.apply (.var name)) →
        ∀ name ∈ names, table.apply (.var name) = selected.apply (.var name) := by
      intro names
      induction names with
      | nil => simp
      | cons first rest ih =>
          intro equal name member
          have parts := List.cons.inj equal
          rcases List.mem_cons.mp member with rfl | restMember
          · exact parts.1
          · exact ih parts.2 name restMember
    exact mapEqual scope mapped
  have allVariables : ∀ name, table.apply (.var name) = selected.apply (.var name) := by
    intro name
    by_cases present : name ∈ scope
    · exact each name present
    · have noBinding : name ∉ specBindingVars bindings := fun member =>
        present (List.mem_append_left _ member)
      have noKey : name ∉ table.keys := fun member =>
        present (List.mem_append_right _ member)
      have historical : folded.apply (.var name) = .var name :=
        BindingMaterializationRel.outside_result ⟨folded, fold, rfl⟩
          (by simpa [TypeSubst.typeVars] using noBinding)
      rw [show selected.apply (.var name) = renameTypeVars choice (folded.apply (.var name))
        from selectedRead (.var name), historical]
      simp only [renameTypeVars, outside name noBinding, TypeSubst.apply,
        TypeSubst.lookup_eq_none_of_not_mem_keys noKey, Option.getD_none]
  refine ⟨normal, folded, choice, fold, fixed, outside, ?_⟩
  intro atom
  rw [← applyTypeValuation_presented_eq_apply table atom,
    ← applyTypeValuation_presented_eq_apply selected atom]
  congr 1
  exact funext allVariables

/-- A certificate cannot introduce a stored key outside the source record's
complete support, even when residual representatives have been changed. -/
theorem lookup_none_of_outside {bindings : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate bindings table) {name : String}
    (fresh : name ∉ specBindingVars bindings) : table.lookup name = none := by
  obtain ⟨folded, choice, fold, _fixed, outside, allAtoms⟩ := certificate.representative
  have unbound : folded.lookup name = none := by
    apply TypeSubst.lookup_eq_none_of_not_mem_keys
    exact fun stored => (fold.binding_avoids (forbidden := [name]) (by simpa using fresh)).keys
      name stored (by simp)
  have read := TypeSubst.apply_renameVars choice folded (.var name)
  have unchanged : table.apply (.var name) = .var name := by
    simpa only [allAtoms, renameTypeVars, outside name fresh, TypeSubst.apply,
      unbound, Option.getD_none] using read
  apply TypeSubst.lookup_eq_none_of_not_mem_keys
  exact certificate.normal.apply_variable_not_key (.var name) name
    (by rw [unchanged]; simp [TypeSubst.typeVars])

/-- A certified readout cannot expose a name outside both the complete
binding record and its operand. This also covers open values and aliases. -/
theorem avoids_outside {bindings : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate bindings table) {name : String}
    (fresh : name ∉ specBindingVars bindings) (atom : Atom)
    (absent : name ∉ TypeSubst.typeVars atom) : name ∉ TypeSubst.typeVars (table.apply atom) := by
  obtain ⟨folded, choice, fold, fixed, outside, allAtoms⟩ := certificate.representative
  intro occurs
  rw [allAtoms, (fold.model_fixed_representative choice fixed).2.2 atom,
    Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars] at occurs
  obtain ⟨other, original, renamed⟩ := List.mem_map.mp occurs
  have same : other = name := choice.injective (renamed.trans (outside name fresh).symm)
  subst other
  exact (BindingMaterializationRel.variables_subset ⟨folded, fold, rfl⟩ original).elim absent fresh

private theorem unbound_occurrence_survives (table : TypeSubst) (name : String)
    (unbound : table.lookup name = none) (atom : Atom) :
    name ∈ TypeSubst.typeVars atom → name ∈ TypeSubst.typeVars (table.apply atom) := by
  induction atom using Atom.rec
      (motive_2 := fun atoms => name ∈ TypeSubst.typeVarsList atoms →
        name ∈ TypeSubst.typeVarsList (atoms.map table.apply)) with
  | symbol | grounded => simp only [TypeSubst.typeVars,List.not_mem_nil,false_implies]
  | var otherName =>
      intro present
      have same : name = otherName := by simpa only [TypeSubst.typeVars,List.mem_singleton] using present
      subst otherName
      simp only [TypeSubst.apply,unbound,Option.getD_none,TypeSubst.typeVars,List.mem_singleton]
  | expression atoms ih => simpa only [TypeSubst.typeVars,TypeSubst.apply] using ih
  | nil =>
      rename_i present
      simpa only [List.map_nil] using present
  | cons atom atoms head tail =>
      rename_i present
      simp only [TypeSubst.typeVarsList,List.map_cons,List.mem_append] at present ⊢
      exact present.elim (fun h => Or.inl (head h)) (fun h => Or.inr (tail h))

/-- Reading a certified operand changes no support outside the incoming
constraints. The union is the inventory needed by a subsequent operation. -/
theorem support_union_apply {bindings : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate bindings table) (atom : Atom) (name : String) :
    (name ∈ specBindingVars bindings ∨ name ∈ TypeSubst.typeVars (table.apply atom)) ↔
      name ∈ specBindingVars bindings ∨ name ∈ TypeSubst.typeVars atom := by
  by_cases old : name ∈ specBindingVars bindings
  · simp only [old,true_or]
  · simp only [old,false_or]
    constructor
    · intro present
      by_contra absent
      exact certificate.avoids_outside old atom absent present
    · exact unbound_occurrence_survives table name (certificate.lookup_none_of_outside old) atom

/-- A fresh assignment extends the whole frame certificate, including for
open values that avoid the new name. The old record may contain aliases;
pending operands continue to use the same extended table. -/
theorem fresh_assignment {bindings : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate bindings table) (name : String) (value : Atom)
    (fresh : name ∉ specBindingVars bindings) (absent : name ∉ TypeSubst.typeVars value) :
    ReadoutCertificate (bindings.assign name value) (table.bind name value) := by
  have unbound : bindings.lookup name = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry stored
    have absent : name ≠ entry.1 := by
      intro same
      apply fresh
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨entry, stored, by simp [same]⟩
    simpa using absent
  have assigned : bindings.assign name value =
      ⟨bindings.assignments ++ [(name, value)], bindings.equalities⟩ := by
    simp [Bindings.assign, Bindings.isBound, unbound]
  apply of_normal_theory
  · exact certificate.normal.bind (certificate.avoids_outside fresh value absent)
  · intro valuation
    rw [TypeSubstSatisfied.bind_iff (certificate.lookup_none_of_outside fresh),
      certificate.theory, assigned,
      Spec.Bindings.ScopeObservation.appendPrivatePresentation_solutions]
    simp [TypeSubstSatisfied]

/-- Later constraints absorb every pending operand under the same two tables. -/
theorem absorbs {before after : Bindings} {earlier later : TypeSubst}
    (old : ReadoutCertificate before earlier) (next : ReadoutCertificate after later)
    (extension : ∀ valuation, TypeBindingSatisfied valuation after →
      TypeBindingSatisfied valuation before) (atom : Atom) :
    later.apply (earlier.apply atom) = later.apply atom :=
  apply_absorbs_of_solution_implication next.normal
    (fun valuation model => (old.theory valuation).mpr
      (extension valuation ((next.theory valuation).mp model))) atom

theorem pending_absorbed {before after : Bindings} {earlier later : TypeSubst}
    (old : ReadoutCertificate before earlier) (next : ReadoutCertificate after later)
    (extension : ∀ valuation, TypeBindingSatisfied valuation after →
      TypeBindingSatisfied valuation before) (pending : List Atom) :
    (pending.map earlier.apply).map later.apply = pending.map later.apply := by
  simp only [List.map_map]
  exact List.map_congr_left fun atom _ => old.absorbs next extension atom

/-- A selected finite readout preserves its operand in every model of the
whole record; already-rendered strings remain ordinary grounded data. -/
theorem preserves_model {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (valuation : String → Atom)
    (satisfied : TypeBindingSatisfied valuation bindings) (atom : Atom) :
    applyTypeValuation valuation (table.apply atom) = applyTypeValuation valuation atom :=
  ((certified.theory valuation).mpr satisfied).absorbs atom

/-- One certified table preserves the joint observation of every pending
packet, including repeated variables and caller/return correlations. -/
theorem observedTuples_eq {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) (atoms : List Atom) :
    Spec.Bindings.ScopeObservation.observedTuples bindings (atoms.map table.apply) =
      Spec.Bindings.ScopeObservation.observedTuples bindings atoms := by
  apply Spec.Bindings.ScopeObservation.observedTuples_congr_models
  intro model satisfied
  simp only [List.map_map]
  exact List.map_congr_left fun atom _ => certified.preserves_model model satisfied atom

/-- Adding source constraints preserves an earlier packet read without
requiring the later store to choose the same residual representatives. -/
theorem observedTuples_eq_after_extension {before after : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate before table)
    (extension : ∀ model, TypeBindingSatisfied model after → TypeBindingSatisfied model before)
    (atoms : List Atom) :
    Spec.Bindings.ScopeObservation.observedTuples after (atoms.map table.apply) =
      Spec.Bindings.ScopeObservation.observedTuples after atoms := by
  apply Spec.Bindings.ScopeObservation.observedTuples_congr_models
  intro model satisfied
  simp only [List.map_map]
  exact List.map_congr_left fun atom _ => certified.preserves_model model (extension model satisfied) atom

/-- The same finite representative choice follows a simultaneous variable
permutation; it is conjugated rather than selected again for each operand. -/
theorem rename (permutation : Equiv.Perm String) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table) :
    ReadoutCertificate (renameBindings permutation bindings) (table.renameVars permutation) := by
  obtain ⟨folded, choice, fold, fixed, outside, allAtoms⟩ := certified.representative
  let transported : Equiv.Perm String := permutation.symm.trans (choice.trans permutation)
  refine ⟨certified.normal.rename permutation, folded.renameVars permutation,
    transported, ?_, ?_, ?_, ?_⟩
  · rw [bindingAtomEquations_renameBindings]
    simpa only [TypeSubst.renameVars_nil] using EquationListPresentationRel.rename permutation fold
  · intro valuation satisfies name
    have original : TypeBindingSatisfied (valuation ∘ permutation) bindings :=
      (renameBindings_typeBindingSatisfied permutation bindings valuation).mp satisfies
    simpa [transported, Function.comp_def] using
      fixed (valuation ∘ permutation) original (permutation.symm name)
  · intro name absent
    have originalAbsent : permutation.symm name ∉ specBindingVars bindings := by
      intro member
      apply absent
      rw [specBindingVars_renameBindings]
      exact List.mem_map.mpr ⟨permutation.symm name, member, by simp⟩
    simp [transported, outside _ originalAbsent]
  · intro atom
    have inverse : renameTypeVars permutation (renameTypeVars permutation.symm atom) = atom := by
      simpa only [Equiv.symm_symm] using renameTypeVars_perm_inverse permutation.symm atom
    have tableRead := TypeSubst.apply_renameVars permutation table (renameTypeVars permutation.symm atom)
    have foldRead := TypeSubst.apply_renameVars permutation (folded.renameVars choice)
      (renameTypeVars permutation.symm atom)
    have sameTables : (folded.renameVars choice).renameVars permutation =
        (folded.renameVars permutation).renameVars transported := by
      rw [TypeSubst.renameVars_comp, TypeSubst.renameVars_comp]
      congr 1
      funext name
      simp [transported, Function.comp_def]
    rw [inverse] at tableRead foldRead
    calc
      (table.renameVars permutation).apply atom =
          renameTypeVars permutation (table.apply (renameTypeVars permutation.symm atom)) := by
            exact tableRead
      _ = renameTypeVars permutation
          ((folded.renameVars choice).apply (renameTypeVars permutation.symm atom)) :=
            congrArg (renameTypeVars permutation) (allAtoms _)
      _ = ((folded.renameVars permutation).renameVars transported).apply atom := by
            rw [← sameTables]
            exact foldRead.symm

end ReadoutCertificate

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

/-! ## Joint current-store presentations

The ranked component is an explicit finite-tree profile. Contextual atoms
retain their lexical frame token; qualification constructs globally distinct
slot names from complete references before normalizing the actual assignments.
One snapshot and one table serve every operand. Rational-tree stores and
runtime pointer representations are separate instances.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open MetavariableFrame
open Spec.Type.Presentation Spec.Type.RuntimeRefinement

abbrev Row := MetavariableFrameStore.Snapshot.RowOf Atom

/-- An explicit finite-tree admission: every stored dependency decreases.
This does not describe a rational-tree store with cyclic values. -/
def Ranked (rank : String → Nat) (entries : TypeSubst) : Prop :=
  ∀ key value, (key, value) ∈ entries →
    ∀ name ∈ TypeSubst.typeVars value, rank name < rank key

theorem Ranked.apply_below {rank : String → Nat} {entries : TypeSubst}
    (ranked : Ranked rank entries) (bound : Nat) (atom : Atom)
    (below : ∀ name ∈ TypeSubst.typeVars atom, rank name < bound) :
    ∀ name ∈ TypeSubst.typeVars (entries.apply atom), rank name < bound := by
  induction atom using Atom.rec
      (motive_2 := fun atoms =>
        (∀ name ∈ TypeSubst.typeVarsList atoms, rank name < bound) →
        ∀ name ∈ TypeSubst.typeVarsList (atoms.map entries.apply), rank name < bound) with
  | symbol value => simp [TypeSubst.apply, TypeSubst.typeVars]
  | grounded value => simp [TypeSubst.apply, TypeSubst.typeVars]
  | var varName =>
      have original := below varName (by simp [TypeSubst.typeVars])
      cases found : entries.lookup varName with
      | none => simpa [TypeSubst.apply, found, TypeSubst.typeVars] using original
      | some value =>
          intro name occurs
          have member := TypeSubst.lookup_eq_some_mem found
          have smaller := ranked varName value member name
            (by simpa [TypeSubst.apply, found] using occurs)
          exact Nat.lt_trans smaller original
  | expression atoms ih =>
      simpa only [TypeSubst.apply, TypeSubst.typeVars] using ih below
  | nil =>
      rename_i _ name occurs
      simp only [List.map_nil, TypeSubst.typeVarsList, List.not_mem_nil] at occurs
  | cons atom atoms first rest below name occurs =>
      simp only [List.map_cons, TypeSubst.typeVarsList, List.mem_append] at occurs
      rcases occurs with left | right
      · exact first (fun x hx => below x (by simp [TypeSubst.typeVarsList, hx])) name left
      · exact rest (fun x hx => below x (by simp [TypeSubst.typeVarsList, hx])) name right

theorem Ranked.bind {rank : String → Nat} {entries : TypeSubst}
    (ranked : Ranked rank entries) (key : String) (value : Atom)
    (below : ∀ name ∈ TypeSubst.typeVars value, rank name < rank key) :
    Ranked rank (entries.bind key value) := by
  have resolved := ranked.apply_below (rank key) value below
  have singleton : Ranked rank [(key, entries.apply value)] := by
    intro name stored member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact resolved
  intro name stored member
  simp only [TypeSubst.bind, List.mem_cons] at member
  rcases member with first | rest
  · cases first
    exact resolved
  · obtain ⟨⟨older, raw⟩, present, equal⟩ := List.mem_map.mp rest
    simp only [Prod.mk.injEq] at equal
    rcases equal with ⟨rfl, rfl⟩
    exact singleton.apply_below (rank older) raw
      (ranked older raw (List.mem_of_mem_filter present))

/-- Normalize exactly the stored assignments using the existing substitution
composition operation. Neither a model nor an expected readout is an input. -/
def normalizeFrom (incoming entries : TypeSubst) : TypeSubst :=
  entries.foldl (fun current entry => current.bind entry.1 entry.2) incoming

def normalize (entries : TypeSubst) : TypeSubst := normalizeFrom [] entries

theorem normalizeFrom_presentation {rank : String → Nat}
    {entries incoming : TypeSubst}
    (unique : entries.keys.Nodup) (ranked : Ranked rank entries)
    (normal : incoming.Normal) (priorRanked : Ranked rank incoming)
    (fresh : ∀ name ∈ entries.keys, name ∉ incoming.keys) :
    EquationListPresentationRel
      (entries.map (fun entry => (Atom.var entry.1, entry.2))) incoming
      (normalizeFrom incoming entries) := by
  induction entries generalizing incoming with
  | nil => exact .nil _
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      have tailUnique : (TypeSubst.keys rest).Nodup := (List.nodup_cons.mp unique).2
      have keyAbsent : key ∉ TypeSubst.keys rest := (List.nodup_cons.mp unique).1
      have freshKey : key ∉ incoming.keys := fresh key (by simp [TypeSubst.keys])
      have below : ∀ name ∈ TypeSubst.typeVars value, rank name < rank key :=
        ranked key value (by simp)
      have resolved := priorRanked.apply_below (rank key) value below
      have clean : key ∉ TypeSubst.typeVars (incoming.apply value) := by
        intro occurs
        exact (Nat.lt_irrefl _) (resolved key occurs)
      have applied : AppliedTypePresentationMatchRel incoming (.var key) value
          (incoming.bind key value) := by
        refine .ordinary (resolvedLeft := .var key)
          (resolvedRight := incoming.apply value) ?_ rfl ?_
        · simp [TypeSubst.apply, TypeSubst.lookup_eq_none_of_not_mem_keys freshKey]
        · have result := AppliedReducedTypeMatchRel.bindLeft
            (substitution := incoming) clean
          simpa only [TypeSubst.bind, normal.apply_idempotent] using result
      have tailFresh : ∀ name ∈ TypeSubst.keys rest, name ∉ (incoming.bind key value).keys := by
        intro name present after
        rw [TypeSubst.keys_bind] at after
        rcases List.mem_cons.mp after with same | old
        · exact keyAbsent (same ▸ present)
        · exact fresh name (by simp [TypeSubst.keys] at present ⊢; exact Or.inr present)
            (List.mem_filter.mp old).1
      exact .cons applied (ih tailUnique
        (fun name stored present => ranked name stored (List.mem_cons_of_mem _ present))
        (normal.bind clean) (priorRanked.bind key value below) tailFresh)

theorem normalize_presentation {rank : String → Nat} {entries : TypeSubst}
    (unique : entries.keys.Nodup) (ranked : Ranked rank entries) :
    EquationListPresentationRel (bindingAtomEquations ⟨entries, []⟩) [] (normalize entries) := by
  simpa only [bindingAtomEquations, List.map_nil, List.append_nil, normalize] using
    normalizeFrom_presentation unique ranked TypeSubst.normal_empty
      (by intro name value absent; simp at absent)
      (by intro name _; simp [TypeSubst.keys])

theorem normalize_certified {rank : String → Nat} {entries : TypeSubst}
    (unique : entries.keys.Nodup) (ranked : Ranked rank entries) :
    ReadoutCertificate ⟨entries, []⟩ (normalize entries) :=
  .of_fold (normalize_presentation unique ranked)

/-- A stored assignment determines the normalized variable and right-hand side
under the one constructed presentation. -/
theorem normalize_assignment {rank : String → Nat} {entries : TypeSubst}
    (unique : entries.keys.Nodup) (ranked : Ranked rank entries)
    {name : String} {value : Atom} (member : (name, value) ∈ entries) :
    (normalize entries).apply (.var name) = (normalize entries).apply value := by
  have certified := normalize_certified unique ranked
  have model := (certified.theory _).mp
    (Theory.normal_presentedValuation_satisfied certified.normal)
  simpa only [Theory.presentedValuation,
    Theory.applyTypeValuation_presented_eq_apply] using model.1 name value member

theorem normalizeFrom_keys_subset (incoming entries : TypeSubst) :
    ∀ name ∈ (normalizeFrom incoming entries).keys,
      name ∈ incoming.keys ∨ name ∈ entries.keys := by
  induction entries generalizing incoming with
  | nil => intro name present; exact Or.inl present
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      intro name present
      rcases ih (incoming.bind key value) name present with prior | later
      · rw [TypeSubst.keys_bind] at prior
        rcases List.mem_cons.mp prior with same | earlier
        · exact Or.inr (by simp [TypeSubst.keys, same])
        · exact Or.inl (List.mem_filter.mp earlier).1
      · exact Or.inr (by simpa [TypeSubst.keys] using Or.inr later)

theorem normalize_unassigned (entries : TypeSubst) (name : String)
    (openSlot : name ∉ entries.keys) :
    (normalize entries).apply (.var name) = .var name := by
  have missing : name ∉ (normalize entries).keys := by
    intro present
    rcases normalizeFrom_keys_subset [] entries name present with impossible | stored
    · simp only [TypeSubst.keys, List.map_nil, List.not_mem_nil] at impossible
    · exact openSlot stored
  simp [TypeSubst.apply, TypeSubst.lookup_eq_none_of_not_mem_keys missing]

theorem normalizeFrom_rename (permutation : Equiv.Perm String)
    (incoming entries : TypeSubst) :
    normalizeFrom (incoming.renameVars permutation) (entries.renameVars permutation) =
      (normalizeFrom incoming entries).renameVars permutation := by
  induction entries generalizing incoming with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      simp only [TypeSubst.renameVars_cons, normalizeFrom, List.foldl_cons]
      rw [TypeSubst.bind_renameVars]
      exact ih (incoming.bind name value)

theorem normalize_rename (permutation : Equiv.Perm String) (entries : TypeSubst) :
    normalize (entries.renameVars permutation) = (normalize entries).renameVars permutation := by
  simpa only [normalize, TypeSubst.renameVars_nil] using
    normalizeFrom_rename permutation [] entries


/-- Open slots remain in the inventory. Only equations are omitted for them. -/
def assignments (snapshot : List Row) : TypeSubst :=
  snapshot.filterMap fun row => row.observed.value.map fun value => (row.name, value)

theorem mem_assignments {snapshot : List Row} {name : String} {value : Atom} :
    (name, value) ∈ assignments snapshot ↔
      ∃ row ∈ snapshot, row.name = name ∧ row.observed.value = some value := by
  simp only [assignments, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨row, member, actual, read, equal⟩
    cases equal
    exact ⟨row, member, rfl, read⟩
  · rintro ⟨row, member, same, read⟩
    exact ⟨row, member, value, read, by simp [same]⟩

theorem assignments_key_source {snapshot : List Row} {name : String}
    (member : name ∈ (assignments snapshot).keys) : name ∈ snapshot.map RowOf.name := by
  obtain ⟨⟨key, value⟩, stored, equal⟩ := List.mem_map.mp member
  have keyEq : key = name := equal
  obtain ⟨row, present, rowKey, _⟩ := mem_assignments.mp stored
  exact List.mem_map.mpr ⟨row, present, rowKey.trans keyEq⟩

theorem assignments_unique {snapshot : List Row} (unique : (snapshot.map RowOf.name).Nodup) :
    (assignments snapshot).keys.Nodup := by
  induction snapshot with
  | nil => exact List.nodup_nil
  | cons row rest ih =>
    have names := List.nodup_cons.mp unique
    cases stored : row.observed.value with
    | none => simpa [assignments, stored] using ih names.2
    | some value =>
      simp only [assignments, List.filterMap_cons, stored, Option.map_some,
        TypeSubst.keys, List.map_cons]
      exact List.nodup_cons.mpr ⟨fun present => names.1 (assignments_key_source present), ih names.2⟩

theorem name_injective_on_snapshot {snapshot : List Row}
    (unique : (snapshot.map RowOf.name).Nodup)
    {left right : Row} (first : left ∈ snapshot) (second : right ∈ snapshot)
    (same : left.name = right.name) : left = right := by
  induction snapshot with
  | nil => simp at first
  | cons row rest ih =>
    have names := List.nodup_cons.mp unique
    rcases List.mem_cons.mp first with leftHead | first
    · rcases List.mem_cons.mp second with rightHead | second
      · exact leftHead.trans rightHead.symm
      · exact False.elim (names.1 (List.mem_map.mpr
          ⟨right, second, same.symm.trans (congrArg RowOf.name leftHead)⟩))
    · rcases List.mem_cons.mp second with rightHead | second
      · exact False.elim (names.1 (List.mem_map.mpr
          ⟨left, first, same.trans (congrArg RowOf.name rightHead)⟩))
      · exact ih names.2 first second

theorem open_slot_not_assigned {snapshot : List Row}
    (unique : (snapshot.map RowOf.name).Nodup) {row : Row}
    (member : row ∈ snapshot) (unbound : row.observed.value = none) :
    row.name ∉ (assignments snapshot).keys := by
  intro assigned
  obtain ⟨⟨name, value⟩, present, equal⟩ := List.mem_map.mp assigned
  obtain ⟨other, otherPresent, same, bound⟩ := mem_assignments.mp present
  have names : other.name = row.name := same.trans equal
  have rowsEqual := name_injective_on_snapshot unique otherPresent member names
  subst other
  simp [unbound] at bound

/-- A finite named source view. Unique names are a scope representation
condition; the complete rows still retain reference identity independently. -/
def bindings (image : ImageOf Atom) : Bindings := ⟨assignments (rows image), []⟩

def table (image : ImageOf Atom) : TypeSubst := normalize (assignments (rows image))

theorem table_certified {image : ImageOf Atom} {rank : String → Nat}
    (unique : ((rows image).map RowOf.name).Nodup)
    (ranked : Ranked rank (assignments (rows image))) :
    ReadoutCertificate (bindings image) (table image) :=
  normalize_certified (assignments_unique unique) ranked

theorem table_open_slot {image : ImageOf Atom}
    (unique : ((rows image).map RowOf.name).Nodup) {row : Row}
    (member : row ∈ rows image) (unbound : row.observed.value = none) :
    (table image).apply (.var row.name) = .var row.name :=
  normalize_unassigned _ _ (open_slot_not_assigned unique member unbound)


/-- Source spelling for a contextual slot includes its complete identity.
The distinct prefix for unbound external names prevents accidental capture. -/
def referenceName (reference : Ref) : String :=
  "slot:" ++ Nat.repr (Nat.pair reference.handle (Nat.pair reference.generation reference.slot))

def freeName (name : String) : String := "free:" ++ name

theorem referenceName_injective : Function.Injective referenceName := by
  intro left right same
  have encoded := (String.append_right_inj "slot:").mp same
  have paired := Nat.pair_eq_pair.mp (Nat.repr_injective encoded)
  have rest := Nat.pair_eq_pair.mp paired.2
  cases left
  cases right
  simp_all

theorem freeName_injective : Function.Injective freeName :=
  fun _ _ same => (String.append_right_inj "free:").mp same

theorem referenceName_ne_freeName (reference : Ref) (name : String) :
    referenceName reference ≠ freeName name := by
  intro same
  have chars := congrArg String.toList same
  simp [referenceName, freeName, String.toList_append] at chars

/-- The same inventory serves every occurrence. An unlisted spelling denotes
an ambient global variable in this view, not a fresh name per use. Private
unresolved variables must occur in their frame inventory; the checked finite
global-context entry point below enforces that coverage. -/
def nameIn (token : Token) (frame : Frame) (name : String) : String :=
  match indexOf frame name with
  | some slot => referenceName (token.ref slot)
  | none => freeName name

theorem nameIn_slot (token : Token) (frame : Frame) (unique : frame.Nodup)
    (slot : Slot frame) :
    nameIn token frame (nameOf slot) = referenceName (token.ref slot.val) := by
  simp [nameIn, indexOf_get unique slot]

theorem nameIn_external (token : Token) (frame : Frame) (name : String)
    (absent : indexOf frame name = none) :
    nameIn token frame name = freeName name := by simp [nameIn, absent]

/-- Contextual syntax consists of the original atom and its live lexical token.
It contains no expected materialization or evaluator answer. -/
abbrev ContextualOperand := Token × Atom

/-- Qualify source variables by the actual current inventory. This is a
structural renaming; applications remain syntax. -/
def qualify? {Payload : Type} (image : ImageOf Payload) (operand : ContextualOperand) :
    Option Atom := do
  let entry ← image.frameAt operand.1.handle
  if entry.generation = operand.1.generation ∧ entry.frame.Nodup then
    some (renameTypeVars (nameIn operand.1 entry.frame) operand.2)
  else none

theorem qualify?_of_frame {Payload : Type} {image : ImageOf Payload}
    {token : Token} {entry : EntryOf Payload}
    (present : image.frameAt token.handle = some entry)
    (generation : entry.generation = token.generation) (unique : entry.frame.Nodup)
    (atom : Atom) :
    qualify? image (token, atom) = some (renameTypeVars (nameIn token entry.frame) atom) := by
  simp [qualify?, present, generation, unique]

theorem qualify?_stale {Payload : Type} {image : ImageOf Payload}
    {token : Token} {entry : EntryOf Payload}
    (present : image.frameAt token.handle = some entry)
    (stale : entry.generation ≠ token.generation) (atom : Atom) :
    qualify? image (token, atom) = none := by simp [qualify?, present, stale]

theorem qualify?_ambiguous {Payload : Type} {image : ImageOf Payload}
    {token : Token} {entry : EntryOf Payload}
    (present : image.frameAt token.handle = some entry)
    (ambiguous : ¬ entry.frame.Nodup) (atom : Atom) :
    qualify? image (token, atom) = none := by simp [qualify?, present, ambiguous]

theorem qualify?_slot {Payload : Type} {image : ImageOf Payload}
    {token : Token} {entry : EntryOf Payload}
    (present : image.frameAt token.handle = some entry)
    (generation : entry.generation = token.generation) (unique : entry.frame.Nodup)
    (slot : Slot entry.frame) :
    qualify? image (token, .var (nameOf slot)) = some (.var (referenceName (token.ref slot.val))) := by
  rw [qualify?_of_frame present generation unique]
  simp [renameTypeVars, nameIn_slot token entry.frame unique slot]

/-- Raw slot metadata is preserved while each stored contextual atom is renamed
through its own lexical inventory. A stale payload context rejects the packet. -/
def qualifyRow? (image : ImageOf ContextualOperand) (row : RowOf ContextualOperand) : Option Row := do
  let value ← match row.observed.value with
    | none => some none
    | some operand => (qualify? image operand).map some
  pure ⟨row.reference, referenceName row.reference,
    ⟨value, row.observed.writeVersion, row.observed.writeClock, row.observed.activationBoundary⟩⟩

def qualifyRowsFrom? (image : ImageOf ContextualOperand) :
    List (RowOf ContextualOperand) → Option (List Row)
  | [] => some []
  | row :: rest => do
    let qualified ← qualifyRow? image row
    let tail ← qualifyRowsFrom? image rest
    pure (qualified :: tail)

def contextualRows? (image : ImageOf ContextualOperand) : Option (List Row) :=
  qualifyRowsFrom? image (rows image)

theorem qualifyRow?_coordinates {image : ImageOf ContextualOperand}
    {raw : RowOf ContextualOperand} {qualified : Row}
    (success : qualifyRow? image raw = some qualified) :
    qualified.reference = raw.reference ∧ qualified.name = referenceName raw.reference ∧
    qualified.observed.writeVersion = raw.observed.writeVersion ∧
    qualified.observed.writeClock = raw.observed.writeClock ∧
    qualified.observed.activationBoundary = raw.observed.activationBoundary := by
  unfold qualifyRow? at success
  cases stored : raw.observed.value with
  | none => simp [stored] at success; subst qualified; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some operand =>
    cases result : qualify? image operand with
    | none => simp [stored, result] at success
    | some atom => simp [stored, result] at success; subst qualified; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem qualifyRow?_value {image : ImageOf ContextualOperand}
    {raw : RowOf ContextualOperand} {qualified : Row}
    (success : qualifyRow? image raw = some qualified) :
    match raw.observed.value with
    | none => qualified.observed.value = none
    | some operand => ∃ atom, qualify? image operand = some atom ∧
        qualified.observed.value = some atom := by
  unfold qualifyRow? at success
  cases stored : raw.observed.value with
  | none => simp [stored] at success; subst qualified; rfl
  | some operand =>
    cases result : qualify? image operand with
    | none => simp [stored, result] at success
    | some atom =>
      simp [stored, result] at success
      subst qualified
      exact ⟨atom, result, rfl⟩

theorem qualifyRowsFrom?_names {image : ImageOf ContextualOperand}
    {input : List (RowOf ContextualOperand)} {output : List Row}
    (success : qualifyRowsFrom? image input = some output) :
    output.map RowOf.name = (input.map RowOf.reference).map referenceName := by
  induction input generalizing output with
  | nil => simp [qualifyRowsFrom?] at success; subst output; rfl
  | cons raw rest ih =>
    cases first : qualifyRow? image raw with
    | none => simp [qualifyRowsFrom?, first] at success
    | some qualified =>
      cases tail : qualifyRowsFrom? image rest with
      | none => simp [qualifyRowsFrom?, first, tail] at success
      | some remaining =>
        simp [qualifyRowsFrom?, first, tail] at success
        subst output
        simp only [List.map_cons, (qualifyRow?_coordinates first).2.1, ih tail]

theorem qualifyRowsFrom?_members {image : ImageOf ContextualOperand}
    {input : List (RowOf ContextualOperand)} {output : List Row}
    (success : qualifyRowsFrom? image input = some output) (qualified : Row) :
    qualified ∈ output ↔
      ∃ raw ∈ input, qualifyRow? image raw = some qualified := by
  induction input generalizing output with
  | nil => simp [qualifyRowsFrom?] at success; subst output; simp
  | cons raw rest ih =>
    cases first : qualifyRow? image raw with
    | none => simp [qualifyRowsFrom?, first] at success
    | some head =>
      cases tail : qualifyRowsFrom? image rest with
      | none => simp [qualifyRowsFrom?, first, tail] at success
      | some remaining =>
        simp [qualifyRowsFrom?, first, tail] at success
        subst output
        rw [List.mem_cons, ih tail]
        constructor
        · rintro (rfl | ⟨stored, member, result⟩)
          · exact ⟨raw, by simp, first⟩
          · exact ⟨stored, List.mem_cons_of_mem _ member, result⟩
        · rintro ⟨stored, member, result⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl (Option.some.inj (result.symm.trans first))
          · exact Or.inr ⟨stored, member, result⟩

theorem contextualRows?_unique {image : ImageOf ContextualOperand} {snapshot : List Row}
    (success : contextualRows? image = some snapshot) :
    (snapshot.map RowOf.name).Nodup := by
  rw [qualifyRowsFrom?_names success]
  exact (rows_reference_unique image).map referenceName_injective

theorem contextualRows?_complete {image : ImageOf ContextualOperand} {snapshot : List Row}
    (success : contextualRows? image = some snapshot) (qualified : Row) :
    qualified ∈ snapshot ↔ ∃ raw, readRow? image raw.reference = some raw ∧
      qualifyRow? image raw = some qualified := by
  rw [qualifyRowsFrom?_members success]
  simp only [rows_complete]

/-- The independently certified readout is constructed from the successful
whole snapshot. The strict rank admits finite trees; it is not rational-tree
or arbitrary cyclic-store semantics. -/
theorem contextualRows?_certified {image : ImageOf ContextualOperand} {snapshot : List Row}
    {rank : String → Nat} (success : contextualRows? image = some snapshot)
    (ranked : Ranked rank (assignments snapshot)) :
    ReadoutCertificate ⟨assignments snapshot, []⟩ (normalize (assignments snapshot)) :=
  normalize_certified (assignments_unique (contextualRows?_unique success)) ranked


theorem qualifyRowsFrom?_every_slot {image : ImageOf ContextualOperand}
    {input : List (RowOf ContextualOperand)} {output : List Row}
    (success : qualifyRowsFrom? image input = some output)
    {raw : RowOf ContextualOperand} (member : raw ∈ input) :
    ∃ qualified ∈ output, qualifyRow? image raw = some qualified := by
  induction input generalizing output with
  | nil => simp at member
  | cons head rest ih =>
    cases first : qualifyRow? image head with
    | none => simp [qualifyRowsFrom?, first] at success
    | some qualified =>
      cases tail : qualifyRowsFrom? image rest with
      | none => simp [qualifyRowsFrom?, first, tail] at success
      | some remaining =>
        simp [qualifyRowsFrom?, first, tail] at success
        subst output
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨qualified, by simp, first⟩
        · obtain ⟨result, present, read⟩ := ih tail member
          exact ⟨result, List.mem_cons_of_mem _ present, read⟩

theorem contextual_bound_slot {image : ImageOf ContextualOperand} {snapshot : List Row}
    {rank : String → Nat} (success : contextualRows? image = some snapshot)
    (ranked : Ranked rank (assignments snapshot))
    {raw : RowOf ContextualOperand} (read : readRow? image raw.reference = some raw)
    {operand : ContextualOperand} (stored : raw.observed.value = some operand) :
    ∃ qualified,
      qualify? image operand = some qualified ∧
      (normalize (assignments snapshot)).apply (.var (referenceName raw.reference)) =
        (normalize (assignments snapshot)).apply qualified := by
  obtain ⟨row, member, projected⟩ :=
    qualifyRowsFrom?_every_slot success (readRow?_mem_rows read)
  have value := qualifyRow?_value projected
  rw [stored] at value
  obtain ⟨qualified, renamed, observed⟩ := value
  have named := (qualifyRow?_coordinates projected).2.1
  refine ⟨qualified, renamed, ?_⟩
  exact normalize_assignment (assignments_unique (contextualRows?_unique success)) ranked
    (mem_assignments.mpr ⟨row, member, named, observed⟩)

theorem contextual_open_slot {image : ImageOf ContextualOperand} {snapshot : List Row}
    (success : contextualRows? image = some snapshot)
    {raw : RowOf ContextualOperand} (read : readRow? image raw.reference = some raw)
    (unbound : raw.observed.value = none) :
    (normalize (assignments snapshot)).apply (.var (referenceName raw.reference)) =
      .var (referenceName raw.reference) := by
  obtain ⟨row, member, projected⟩ :=
    qualifyRowsFrom?_every_slot success (readRow?_mem_rows read)
  have value := qualifyRow?_value projected
  rw [unbound] at value
  have named := (qualifyRow?_coordinates projected).2.1
  rw [← named]
  exact normalize_unassigned _ _ (open_slot_not_assigned
    (contextualRows?_unique success) member value)

/-- One finite source renaming transports rows and all operands together;
reference identity and write history do not change. -/
def renameRow (permutation : Equiv.Perm String) (row : Row) : Row :=
  ⟨row.reference, permutation row.name,
    row.observed.mapPayload (renameTypeVars permutation)⟩

theorem assignments_rename (permutation : Equiv.Perm String) (snapshot : List Row) :
    assignments (snapshot.map (renameRow permutation)) =
      (assignments snapshot).renameVars permutation := by
  induction snapshot with
  | nil => rfl
  | cons row rest ih =>
    cases stored : row.observed.value <;>
      simpa [assignments, renameRow, SlotReadbackOf.mapPayload,
        stored, TypeSubst.renameVars] using ih

/-- The law is joint on the complete ordered operand tuple, including repeated
uses. It cannot choose a different residual renaming for each operand. -/
theorem readout_joint_rename (permutation : Equiv.Perm String)
    (snapshot : List Row) (operands : List Atom) :
    (operands.map (renameTypeVars permutation)).map
        (normalize (assignments (snapshot.map (renameRow permutation)))).apply =
      (operands.map (normalize (assignments snapshot)).apply).map
        (renameTypeVars permutation) := by
  rw [assignments_rename, normalize_rename]
  exact TypeSubst.applyList_renameVars permutation _ operands

/-- Preparation keeps the actual whole slot snapshot and the ordered operand
tuple. Qualification does not apply bindings or invoke any expression. -/
def prepare? (image : ImageOf ContextualOperand) (operands : List ContextualOperand) :
    Option (List Row × List Atom) := do
  let snapshot ← contextualRows? image
  let qualified ← operands.mapM (qualify? image)
  pure (snapshot, qualified)

/-- All contextual operands share one readout presentation. -/
def readout? (image : ImageOf ContextualOperand) (operands : List ContextualOperand) :
    Option (List Atom) :=
  (prepare? image operands).map fun (snapshot, qualified) =>
    qualified.map (normalize (assignments snapshot)).apply

theorem prepare?_components {image : ImageOf ContextualOperand}
    {operands : List ContextualOperand} {snapshot : List Row} {qualified : List Atom}
    (prepared : prepare? image operands = some (snapshot, qualified)) :
    contextualRows? image = some snapshot ∧
      operands.mapM (qualify? image) = some qualified := by
  unfold prepare? at prepared
  cases snapshotRead : contextualRows? image with
  | none => simp [snapshotRead] at prepared
  | some actual =>
    cases operandRead : operands.mapM (qualify? image) with
    | none => simp [snapshotRead, operandRead] at prepared
    | some values =>
      simp [snapshotRead, operandRead] at prepared
      rcases prepared with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

theorem readout?_prepared {image : ImageOf ContextualOperand}
    {operands : List ContextualOperand} {snapshot : List Row} {qualified : List Atom}
    (prepared : prepare? image operands = some (snapshot, qualified)) :
    readout? image operands = some (qualified.map (normalize (assignments snapshot)).apply) := by
  simp only [readout?, prepared, Option.map_some]

theorem prepare?_certified {image : ImageOf ContextualOperand}
    {operands : List ContextualOperand} {snapshot : List Row} {qualified : List Atom}
    {rank : String → Nat} (prepared : prepare? image operands = some (snapshot, qualified))
    (ranked : Ranked rank (assignments snapshot)) :
    ReadoutCertificate ⟨assignments snapshot, []⟩ (normalize (assignments snapshot)) :=
  contextualRows?_certified (prepare?_components prepared).1 ranked

/-- Structural application retains the expression constructor and the order
and multiplicity of its children. It is not language evaluation. -/
theorem normalized_expression (snapshot : List Row) (children : List Atom) :
    (normalize (assignments snapshot)).apply (.expression children) =
      .expression (children.map (normalize (assignments snapshot)).apply) := by
  simp only [TypeSubst.apply]


/-- Coverage is checked from syntax and the actual contextual inventory.
The global list declares shared free-variable identity; it is not a readout. -/
def operandScope (globals : List String) (image : ImageOf ContextualOperand)
    (operand : ContextualOperand) : Bool :=
  match image.frameAt operand.1.handle with
  | none => false
  | some entry => (TypeSubst.typeVars operand.2).all fun name =>
      decide (name ∈ entry.frame ∨ name ∈ globals)

theorem operandScope_iff {globals : List String} {image : ImageOf ContextualOperand}
    {token : Token} {atom : Atom} {entry : EntryOf ContextualOperand}
    (present : image.frameAt token.handle = some entry) :
    operandScope globals image (token, atom) = true ↔
      ∀ name ∈ TypeSubst.typeVars atom, name ∈ entry.frame ∨ name ∈ globals := by
  simp [operandScope, present, List.all_eq_true]

/-- Check the complete stored graph and full operand tuple against one global
context before using their shared presentation. Unlisted private syntax is
refused; repeated declared globals remain one variable across all frames. -/
def prepareScoped? (globals : List String) (image : ImageOf ContextualOperand)
    (operands : List ContextualOperand) : Option (List Row × List Atom) :=
  if (rows image).all (fun row => match row.observed.value with
      | none => true
      | some operand => operandScope globals image operand) &&
      operands.all (operandScope globals image) then
    prepare? image operands
  else none

theorem prepareScoped?_success {globals : List String} {image : ImageOf ContextualOperand}
    {operands : List ContextualOperand} {pair : List Row × List Atom}
    (prepared : prepareScoped? globals image operands = some pair) :
    prepare? image operands = some pair := by
  unfold prepareScoped? at prepared
  split at prepared
  · exact prepared
  · contradiction

theorem prepareScoped?_scope {globals : List String} {image : ImageOf ContextualOperand}
    {operands : List ContextualOperand} {pair : List Row × List Atom}
    (prepared : prepareScoped? globals image operands = some pair) :
    (∀ operand ∈ operands, operandScope globals image operand = true) ∧
      (∀ row ∈ rows image, ∀ operand, row.observed.value = some operand →
        operandScope globals image operand = true) := by
  unfold prepareScoped? at prepared
  split at prepared
  · rename_i admitted
    have supported := Bool.and_eq_true_iff.mp admitted
    constructor
    · exact List.all_eq_true.mp supported.2
    · intro row member operand stored
      have checked := List.all_eq_true.mp supported.1 row member
      simpa only [stored] using checked
  · contradiction

theorem prepareScoped?_operand_supported {globals : List String}
    {image : ImageOf ContextualOperand} {operands : List ContextualOperand}
    {pair : List Row × List Atom} {token : Token} {atom : Atom}
    {entry : EntryOf ContextualOperand}
    (prepared : prepareScoped? globals image operands = some pair)
    (member : (token, atom) ∈ operands)
    (present : image.frameAt token.handle = some entry) :
    ∀ name ∈ TypeSubst.typeVars atom, name ∈ entry.frame ∨ name ∈ globals :=
  (operandScope_iff present).mp ((prepareScoped?_scope prepared).1 _ member)

theorem prepareScoped?_certified {globals : List String}
    {image : ImageOf ContextualOperand} {operands : List ContextualOperand}
    {snapshot : List Row} {qualified : List Atom} {rank : String → Nat}
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified))
    (ranked : Ranked rank (assignments snapshot)) :
    ReadoutCertificate ⟨assignments snapshot, []⟩ (normalize (assignments snapshot)) :=
  prepare?_certified (prepareScoped?_success prepared) ranked

/-- The shared allocator guards the complete logical image. It does not
reinterpret a stale stored payload as an unbound source variable. -/
def prepareOwned? (allocator : Allocator) (image : ImageOf ContextualOperand)
    (operands : List ContextualOperand) : Option (List Row × List Atom) :=
  if image.inventory.all (fun token => decide (Live allocator token)) then
    prepare? image operands
  else none

theorem prepareOwned?_success {allocator : Allocator} {image : ImageOf ContextualOperand}
    {operands : List ContextualOperand} {pair : List Row × List Atom}
    (prepared : prepareOwned? allocator image operands = some pair) :
    prepare? image operands = some pair := by
  unfold prepareOwned? at prepared
  split at prepared
  · exact prepared
  · contradiction

theorem prepareOwned?_of_live (allocator : Allocator) (image : ImageOf ContextualOperand)
    (live : ∀ token ∈ image.inventory, Live allocator token) (operands : List ContextualOperand) :
    prepareOwned? allocator image operands = prepare? image operands := by
  have accepted : image.inventory.all (fun token => decide (Live allocator token)) = true :=
    List.all_eq_true.mpr (fun token member => decide_eq_true (live token member))
  simp only [prepareOwned?, accepted, ↓reduceIte]

theorem prepareOwned?_stale {allocator : Allocator} {image : ImageOf ContextualOperand}
    {token : Token} (present : token ∈ image.inventory) (stale : ¬ Live allocator token)
    (operands : List ContextualOperand) : prepareOwned? allocator image operands = none := by
  unfold prepareOwned?
  have refused : image.inventory.all (fun token => decide (Live allocator token)) ≠ true := by
    intro accepted
    exact stale (of_decide_eq_true (List.all_eq_true.mp accepted token present))
  simp [refused]

theorem prepareOwned?_capture {allocator next : Allocator}
    {image captured : ImageOf ContextualOperand}
    (capturedAll : image.captureAll? allocator = some (next, captured))
    (operands : List ContextualOperand) :
    prepareOwned? next captured operands = prepare? image operands := by
  have same := ImageOf.captureAll_preserves_image capturedAll
  subst captured
  exact prepareOwned?_of_live next image (ImageOf.captureAll_live capturedAll) operands


end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared
open MetavariableFrameStore.Snapshot

def caller : Token := ⟨0, 3⟩
def child : Token := ⟨1, 8⟩
def callerX : Ref := caller.ref 0
def callerOpen : Ref := caller.ref 1
def childX : Ref := child.ref 0

def image : ImageOf ContextualOperand :=
  ⟨#[some (EntryOf.initial 3 ["x", "open"]
      (fun slot => if slot.val = 0 then some (child, .var "x") else none)),
     some (EntryOf.initial 8 ["x"] (fun _ => some (child, .symbol "A")))], 11⟩

attribute [local simp] readout? prepare? contextualRows? qualifyRowsFrom? qualifyRow? qualify?
  rows entryRows Row.ofEntry EntryOf.initial entryEnv image_frameAt List.range_succ List.ofFn_succ
  assignments normalize normalizeFrom TypeSubst.bind TypeSubst.apply TypeSubst.applyAssignment
  TypeSubst.lookup TypeSubst.erase RuntimeRefinement.renameTypeVars nameIn
  MetavariableFrame.indexOf referenceName freeName Token.ref
  caller child callerX callerOpen childX image

def snapshot : List Row := (contextualRows? image).get (by decide +kernel)

attribute [local simp] snapshot

theorem complete_snapshot : contextualRows? image = some snapshot := by
  exact (Option.some_get _).symm

theorem actual_assignments :
    assignments snapshot =
      [(referenceName callerX, .var (referenceName childX)),
       (referenceName childX, .symbol "A")] := by simp

def rank (name : String) : Nat := if name = referenceName callerX then 2 else 1

theorem actual_rank : Ranked rank (assignments snapshot) := by
  rw [actual_assignments]
  intro name value present
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at present
  rcases present with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro varName occurs
    simp only [TypeSubst.typeVars, List.mem_singleton] at occurs
    subst varName
    simp [rank]
  · simp [TypeSubst.typeVars]

theorem actual_certificate :
    ReadoutCertificate ⟨assignments snapshot, []⟩ (normalize (assignments snapshot)) :=
  contextualRows?_certified complete_snapshot actual_rank

theorem cross_frame_alias_and_repeated_use :
    readout? image [(caller, .expression [.symbol "pair", .var "x", .var "x"])] =
      some [.expression [.symbol "pair", .symbol "A", .symbol "A"]] := by simp

theorem authored_spelling_does_not_merge_frames :
    qualify? image (caller, .var "x") = some (.var (referenceName callerX)) ∧
    qualify? image (child, .var "x") = some (.var (referenceName childX)) ∧
    referenceName callerX ≠ referenceName childX := by simp

theorem open_slot_and_stale_reference_are_distinct :
    (readRow? image callerOpen).map (fun row => row.observed.value) = some none ∧
    readRow? image ⟨0, 4, 1⟩ = none := by decide +kernel

theorem known_open_source_name_retained :
    readout? image [(caller, .var "open")] =
      some [.var (referenceName callerOpen)] := by simp

theorem external_free_variable_shared :
    readout? image [(caller, .expression [.var "outside", .var "outside"]),
      (child, .var "outside")] =
      some [.expression [.var (freeName "outside"), .var (freeName "outside")],
        .var (freeName "outside")] := by
  simp
  decide +kernel

theorem structural_read_does_not_invoke_call :
    readout? image [(caller, .expression [.symbol "effect!", .var "x"])] =
      some [.expression [.symbol "effect!", .symbol "A"]] := by simp

theorem original_metadata_retained :
    (rows image).map (fun row =>
      (row.reference, row.observed.writeVersion, row.observed.writeClock,
        row.observed.activationBoundary)) =
      [(callerX, 0, 11, none), (callerOpen, 0, 11, none), (childX, 0, 11, none)] := by decide +kernel

def openAliasImage : ImageOf ContextualOperand :=
  ⟨#[some (EntryOf.initial 3 ["x"]
      (fun _ => some (child, .var "x"))),
     some (EntryOf.initial 8 ["x"] (fun _ => none))], 11⟩

attribute [local simp] openAliasImage

theorem unresolved_alias_keeps_one_correlated_residual :
    readout? openAliasImage
      [(caller, .expression [.var "x", .var "x"]), (child, .var "x")] =
      some [.expression [.var (referenceName childX), .var (referenceName childX)],
        .var (referenceName childX)] := by simp

theorem lost_context_changes_the_answer :
    qualify? image (caller, .var "x") ≠ qualify? image (child, .var "x") := by simp

theorem stale_operand_is_not_free_syntax :
    prepare? image [(⟨1, 9⟩, .var "x")] = none := by decide +kernel

def stalePayloadImage : ImageOf ContextualOperand :=
  ⟨#[some (EntryOf.initial 3 ["x"] (fun _ => some (⟨1, 9⟩, .var "x"))),
     some (EntryOf.initial 8 ["x"] (fun _ => none))], 11⟩

theorem stale_stored_context_rejects_whole_snapshot :
    contextualRows? stalePayloadImage = none := by decide +kernel

def ambiguousImage : ImageOf ContextualOperand :=
  ⟨#[some (EntryOf.initial 3 ["x", "x"] (fun _ => none))], 0⟩

theorem ambiguous_lexical_inventory_refused :
    prepare? ambiguousImage [(caller, .var "x")] = none := by decide +kernel

def authority : Allocator := ⟨#[⟨3, 1⟩, ⟨8, 1⟩], 16⟩
def staleAuthority : Allocator := ⟨#[⟨4, 1⟩, ⟨8, 1⟩], 16⟩

theorem owned_preparation_accepts_current_authority :
    (prepareOwned? authority image [(caller, .var "x")]).isSome = true := by decide +kernel

theorem owned_preparation_rejects_retired_incarnation :
    prepareOwned? staleAuthority image [(caller, .var "open")] = none := by decide +kernel

theorem cyclic_tree_is_outside_ranked_component (rankOf : String → Nat) :
    ¬ Ranked rankOf [("x", .expression [.symbol "f", .var "x"])] := by
  intro ranked
  have smaller := ranked "x" (.expression [.symbol "f", .var "x"]) (by simp) "x"
    (by simp [TypeSubst.typeVars, TypeSubst.typeVarsList])
  exact Nat.lt_irrefl _ smaller

theorem reference_generation_is_not_erased :
    referenceName ⟨0, 3, 0⟩ ≠ referenceName ⟨0, 4, 0⟩ := by decide +kernel

theorem free_name_cannot_capture_slot (name : String) :
    freeName name ≠ referenceName callerX :=
  (referenceName_ne_freeName callerX name).symm


/-- Without a declared local inventory, the unguarded profile intentionally
identifies the same ambient free spelling across contexts. -/
theorem unlisted_spelling_is_ambient_in_global_profile :
    readout? image [(caller, .var "hidden"), (child, .var "hidden")] =
      some [.var (freeName "hidden"), .var (freeName "hidden")] := by
  simp
  decide +kernel

theorem scoped_preparation_rejects_unregistered_private_name :
    prepareScoped? [] image [(caller, .var "hidden"), (child, .var "hidden")] = none := by
  simp [prepareScoped?, operandScope, TypeSubst.typeVars]

theorem scoped_preparation_accepts_declared_global :
    prepareScoped? ["hidden"] image [(caller, .var "hidden"), (child, .var "hidden")] =
      some (snapshot, [.var (freeName "hidden"), .var (freeName "hidden")]) := by
  simp [prepareScoped?, operandScope, TypeSubst.typeVars]

theorem scoped_preparation_retains_actual_aliases :
    prepareScoped? [] image [(caller, .expression [.symbol "pair", .var "x", .var "x"])] =
      some (snapshot,
        [.expression [.symbol "pair", .var (referenceName callerX), .var (referenceName callerX)]]) := by
  simp [prepareScoped?, operandScope, TypeSubst.typeVars, TypeSubst.typeVarsList]

def unregisteredPayloadImage : ImageOf ContextualOperand :=
  ⟨#[some (EntryOf.initial 3 ["x"] (fun _ => some (child, .var "hidden"))),
     some (EntryOf.initial 8 ["x"] (fun _ => none))], 11⟩

theorem scoped_preparation_checks_stored_contexts :
    prepareScoped? [] unregisteredPayloadImage [(child, .var "x")] = none := by
  simp [prepareScoped?, operandScope, unregisteredPayloadImage, TypeSubst.typeVars]

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.Controls


namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot

/-- Contextual qualification depends on retained identities and lexical
inventories, not on a slot's current value or observation clock. -/
theorem qualify?_write {Payload : Type} {image next : ImageOf Payload}
    {target : Ref} {value : Option Payload}
    (written : image.write? target value = some next) (operand : ContextualOperand) :
    qualify? next operand = qualify? image operand := by
  have info := frameInfo_write written operand.1.handle
  cases before : image.frameAt operand.1.handle with
  | none =>
    cases after : next.frameAt operand.1.handle with
    | none => simp [qualify?, before, after]
    | some entry => simp [before, after] at info
  | some old =>
    cases after : next.frameAt operand.1.handle with
    | none => simp [before, after] at info
    | some updated =>
      simp only [before, after, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at info
      simp [qualify?, before, after, info.1, info.2.1]

theorem operandScope_write {image next : ImageOf ContextualOperand}
    {target : Ref} {value : Option ContextualOperand}
    (written : image.write? target value = some next)
    (globals : List String) (operand : ContextualOperand) :
    operandScope globals next operand = operandScope globals image operand := by
  have info := frameInfo_write written operand.1.handle
  cases before : image.frameAt operand.1.handle with
  | none =>
    cases after : next.frameAt operand.1.handle with
    | none => simp [operandScope, before, after]
    | some entry => simp [before, after] at info
  | some old =>
    cases after : next.frameAt operand.1.handle with
    | none => simp [before, after] at info
    | some updated =>
      simp only [before, after, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at info
      simp only [operandScope, before, after, info.2.1]

theorem qualifyRow?_afterWrite {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    {raw : RowOf ContextualOperand} {qualified : Row}
    (projected : qualifyRow? image raw = some qualified) :
    qualifyRow? next (raw.afterWrite next.writeClock target (some payload)) =
      some (qualified.afterWrite next.writeClock target (some atom)) := by
  unfold qualifyRow? at projected ⊢
  cases stored : raw.observed.value with
  | none =>
    simp [stored] at projected
    subst qualified
    by_cases selected : raw.reference = target
    · simp [RowOf.afterWrite, selected, qualify?_write written, qualifiedPayload]
    · simp [RowOf.afterWrite, selected, stored]
  | some previous =>
    cases read : qualify? image previous with
    | none => simp [stored, read] at projected
    | some oldAtom =>
      simp [stored, read] at projected
      subst qualified
      by_cases selected : raw.reference = target
      · simp [RowOf.afterWrite, selected, qualify?_write written, qualifiedPayload]
      · simp [RowOf.afterWrite, selected, stored, qualify?_write written, read]

theorem qualifyRowsFrom?_afterWrite {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    {input : List (RowOf ContextualOperand)} {output : List Row}
    (projected : qualifyRowsFrom? image input = some output) :
    qualifyRowsFrom? next
        (input.map (RowOf.afterWrite next.writeClock target (some payload))) =
      some (output.map (RowOf.afterWrite next.writeClock target (some atom))) := by
  induction input generalizing output with
  | nil => simp [qualifyRowsFrom?] at projected; subst output; rfl
  | cons raw rest ih =>
    cases first : qualifyRow? image raw with
    | none => simp [qualifyRowsFrom?, first] at projected
    | some qualified =>
      cases tail : qualifyRowsFrom? image rest with
      | none => simp [qualifyRowsFrom?, first, tail] at projected
      | some remaining =>
        simp [qualifyRowsFrom?, first, tail] at projected
        subst output
        simp [qualifyRowsFrom?,
          qualifyRow?_afterWrite written qualifiedPayload first, ih tail]

theorem contextualRows?_write {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom} {snapshot : List Row}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (projected : contextualRows? image = some snapshot) :
    contextualRows? next =
      some (snapshot.map (RowOf.afterWrite next.writeClock target (some atom))) := by
  unfold contextualRows?
  rw [rows_write written]
  exact qualifyRowsFrom?_afterWrite written qualifiedPayload projected

theorem prepare?_write {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom}
    {operands : List ContextualOperand} {snapshot : List Row} {qualified : List Atom}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (prepared : prepare? image operands = some (snapshot, qualified)) :
    prepare? next operands =
      some (snapshot.map (RowOf.afterWrite next.writeClock target (some atom)), qualified) := by
  obtain ⟨projected, observed⟩ := prepare?_components prepared
  have sameOperands : qualify? next = qualify? image := funext (qualify?_write written)
  simp [prepare?, contextualRows?_write written qualifiedPayload projected,
    sameOperands, observed]

theorem prepareScoped?_write {globals : List String} {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom}
    {operands : List ContextualOperand} {snapshot : List Row} {qualified : List Atom}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (payloadScope : operandScope globals image payload = true)
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified)) :
    prepareScoped? globals next operands =
      some (snapshot.map (RowOf.afterWrite next.writeClock target (some atom)), qualified) := by
  have scope := prepareScoped?_scope prepared
  have operandsScope : operands.all (operandScope globals next) = true := by
    apply List.all_eq_true.mpr
    intro operand member
    rw [operandScope_write written]
    exact scope.1 operand member
  have rowsScope : (rows next).all (fun row => match row.observed.value with
      | none => true
      | some operand => operandScope globals next operand) = true := by
    rw [rows_write written]
    apply List.all_eq_true.mpr
    intro row member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    by_cases selected : old.reference = target
    · simpa only [RowOf.afterWrite, if_pos selected, operandScope_write written] using payloadScope
    · simp only [RowOf.afterWrite, if_neg selected]
      cases stored : old.observed.value with
      | none => rfl
      | some operand =>
        change operandScope globals next operand = true
        rw [operandScope_write written]
        exact scope.2 old present operand stored
  have admitted : ((rows next).all (fun row => match row.observed.value with
      | none => true
      | some operand => operandScope globals next operand) &&
      operands.all (operandScope globals next)) = true :=
    Bool.and_eq_true_iff.mpr ⟨rowsScope, operandsScope⟩
  unfold prepareScoped?
  split
  · exact prepare?_write written qualifiedPayload (prepareScoped?_success prepared)
  · rename_i refused
    exact False.elim (refused admitted)

/-- A write preserves captured generational authority as well as the exact
operand tuple; the allocator is not replaced or reinterpreted. -/
theorem prepareOwned?_write {allocator : Allocator} {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom}
    {operands : List ContextualOperand} {snapshot : List Row} {qualified : List Atom}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (prepared : prepareOwned? allocator image operands = some (snapshot, qualified)) :
    prepareOwned? allocator next operands =
      some (snapshot.map (RowOf.afterWrite next.writeClock target (some atom)), qualified) := by
  have ordinary := prepareOwned?_success prepared
  unfold prepareOwned? at prepared ⊢
  rw [inventory_write written]
  split at prepared
  · rename_i live
    rw [if_pos live]
    exact prepare?_write written qualifiedPayload ordinary
  · contradiction

theorem readout?_write {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom}
    {operands : List ContextualOperand} {snapshot : List Row} {qualified : List Atom}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (prepared : prepare? image operands = some (snapshot, qualified)) :
    readout? next operands = some
      (qualified.map (normalize (assignments
        (snapshot.map (RowOf.afterWrite next.writeClock target (some atom))))).apply) :=
  readout?_prepared (prepare?_write written qualifiedPayload prepared)

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open RuntimeRefinement

/-- Exact equation order after a write. Other positions are retained; a
previously open slot acquires an equation at its actual inventory position. -/
theorem assignments_afterWrite (snapshot : List Row) (clock : Nat)
    (target : Ref) (value : Atom) :
    assignments (snapshot.map (RowOf.afterWrite clock target (some value))) =
      snapshot.filterMap (fun row => if row.reference = target then some (row.name, value)
        else row.observed.value.map (fun atom => (row.name, atom))) := by
  simp only [assignments, List.filterMap_map]
  apply List.filterMap_congr
  intro row _
  by_cases selected : row.reference = target <;> simp [RowOf.afterWrite, selected]

theorem contextualRows?_named {image : ImageOf ContextualOperand} {snapshot : List Row}
    (success : contextualRows? image = some snapshot) {row : Row} (present : row ∈ snapshot) :
    row.name = referenceName row.reference := by
  obtain ⟨raw, _read, projected⟩ := (contextualRows?_complete success row).mp present
  have coordinates := qualifyRow?_coordinates projected
  exact coordinates.2.1.trans (congrArg referenceName coordinates.1.symm)

theorem contextualRows?_open_target {image : ImageOf ContextualOperand} {snapshot : List Row}
    (success : contextualRows? image = some snapshot)
    {raw : RowOf ContextualOperand} (read : readRow? image raw.reference = some raw)
    (unbound : raw.observed.value = none) {row : Row} (present : row ∈ snapshot)
    (selected : row.reference = raw.reference) : row.observed.value = none := by
  obtain ⟨openRow, member, projected⟩ :=
    qualifyRowsFrom?_every_slot success (readRow?_mem_rows read)
  have value := qualifyRow?_value projected
  rw [unbound] at value
  have named := (qualifyRow?_coordinates projected).2.1
  have sameName : row.name = openRow.name := by
    rw [contextualRows?_named success present, selected, ← named]
  have same := name_injective_on_snapshot (contextualRows?_unique success) present member sameName
  exact same ▸ value

/-- A named snapshot acquires exactly one equation when an existing open
coordinate is written. Decoding the snapshot is independent of its payload
representation; repeated occurrences remain at their inventory positions. -/
theorem assignments_open_slot_mem (snapshot : List Row) (target : Ref)
    (named : ∀ row ∈ snapshot, row.name = referenceName row.reference)
    (present : ∃ row ∈ snapshot, row.reference = target)
    (unbound : ∀ row ∈ snapshot, row.reference = target → row.observed.value = none)
    (clock : Nat) (value : Atom) (key : String) (term : Atom) :
    (key,term) ∈ assignments (snapshot.map (RowOf.afterWrite clock target (some value))) ↔
      (key,term) ∈ assignments snapshot ∨ key = referenceName target ∧ term = value := by
  constructor
  · intro stored
    obtain ⟨changed,member,keyEq,observed⟩ := mem_assignments.mp stored
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp member
    by_cases selected : row.reference = target
    · exact Or.inr ⟨keyEq.symm.trans ((named row present).trans
        (congrArg referenceName selected)),by simpa [RowOf.afterWrite,selected] using observed.symm⟩
    · exact Or.inl (mem_assignments.mpr ⟨row,present,keyEq,
        by simpa [RowOf.afterWrite,selected] using observed⟩)
  · rintro (stored | ⟨rfl,rfl⟩)
    · obtain ⟨row,member,keyEq,observed⟩ := mem_assignments.mp stored
      have notSelected : row.reference ≠ target := by
        intro selected
        simp [unbound row member selected] at observed
      exact mem_assignments.mpr
        ⟨row.afterWrite clock target (some value),List.mem_map.mpr ⟨row,member,rfl⟩,
          keyEq,by simp [RowOf.afterWrite,notSelected,observed]⟩
    · obtain ⟨row,member,selected⟩ := present
      exact mem_assignments.mpr
        ⟨row.afterWrite clock target (some term),List.mem_map.mpr ⟨row,member,rfl⟩,
          (named row member).trans (congrArg referenceName selected),
          by simp [RowOf.afterWrite,selected]⟩

/-- The updated snapshot's complete model theory is the old theory and the
new equation. A previously bound overwrite does not satisfy this law. -/
theorem open_slot_write_models (snapshot : List Row) (target : Ref)
    (named : ∀ row ∈ snapshot, row.name = referenceName row.reference)
    (present : ∃ row ∈ snapshot, row.reference = target)
    (unbound : ∀ row ∈ snapshot, row.reference = target → row.observed.value = none)
    (clock : Nat) (value : Atom) (valuation : String → Atom) :
    TypeBindingSatisfied valuation
        ⟨assignments (snapshot.map (RowOf.afterWrite clock target (some value))),[]⟩ ↔
      TypeBindingSatisfied valuation ⟨assignments snapshot,[]⟩ ∧
        valuation (referenceName target) = applyTypeValuation valuation value := by
  have membership := assignments_open_slot_mem snapshot target named present unbound clock value
  constructor
  · intro model
    refine ⟨⟨?_,by simp⟩,model.1 _ _ ((membership _ _).mpr (Or.inr ⟨rfl,rfl⟩))⟩
    intro key term stored
    exact model.1 key term ((membership key term).mpr (Or.inl stored))
  · rintro ⟨model,added⟩
    refine ⟨?_,by simp⟩
    intro key term stored
    rcases (membership key term).mp stored with old | ⟨rfl,rfl⟩
    · exact model.1 key term old
    · exact added

/-- Membership in the post-write theory is exactly the original equations and
one new equation. This statement is restricted to an actual previously open
slot; no overwrite monotonicity is asserted. -/
theorem assignments_open_write_mem {image : ImageOf ContextualOperand} {snapshot : List Row}
    (success : contextualRows? image = some snapshot)
    {raw : RowOf ContextualOperand} (read : readRow? image raw.reference = some raw)
    (unbound : raw.observed.value = none) (clock : Nat) (value : Atom)
    (key : String) (term : Atom) :
    (key, term) ∈ assignments
        (snapshot.map (RowOf.afterWrite clock raw.reference (some value))) ↔
      (key, term) ∈ assignments snapshot ∨
        key = referenceName raw.reference ∧ term = value := by
  apply assignments_open_slot_mem snapshot raw.reference
    (fun row present => contextualRows?_named success present)
  · obtain ⟨row,present,projected⟩ :=
      qualifyRowsFrom?_every_slot success (readRow?_mem_rows read)
    exact ⟨row,present,(qualifyRow?_coordinates projected).1⟩
  · intro row present selected
    exact contextualRows?_open_target success read unbound present selected

/-- Preserving a supplied dependency rank is a local sufficient condition,
not an imposed variable ordering or a complete acyclicity criterion. -/
theorem open_write_ranked {image : ImageOf ContextualOperand} {snapshot : List Row}
    {rank : String → Nat} (success : contextualRows? image = some snapshot)
    (ranked : Ranked rank (assignments snapshot))
    {raw : RowOf ContextualOperand} (read : readRow? image raw.reference = some raw)
    (unbound : raw.observed.value = none) (clock : Nat) {value : Atom}
    (below : ∀ name ∈ TypeSubst.typeVars value, rank name < rank (referenceName raw.reference)) :
    Ranked rank (assignments (snapshot.map (RowOf.afterWrite clock raw.reference (some value)))) := by
  intro key term member name occurs
  rcases (assignments_open_write_mem success read unbound clock value key term).mp member with
    old | ⟨rfl, rfl⟩
  · exact ranked key term old name occurs
  · exact below name occurs

/-- The new independent theory is the old whole theory conjoined with the
one actual added equation; satisfaction is a conclusion, not admission data. -/
theorem open_write_models {image : ImageOf ContextualOperand} {snapshot : List Row}
    (success : contextualRows? image = some snapshot)
    {raw : RowOf ContextualOperand} (read : readRow? image raw.reference = some raw)
    (unbound : raw.observed.value = none) (clock : Nat) (value : Atom)
    (valuation : String → Atom) :
    TypeBindingSatisfied valuation
        ⟨assignments (snapshot.map (RowOf.afterWrite clock raw.reference (some value))), []⟩ ↔
      TypeBindingSatisfied valuation ⟨assignments snapshot, []⟩ ∧
        valuation (referenceName raw.reference) = applyTypeValuation valuation value := by
  apply open_slot_write_models snapshot raw.reference
    (fun row present => contextualRows?_named success present)
  · obtain ⟨row,present,projected⟩ :=
      qualifyRowsFrom?_every_slot success (readRow?_mem_rows read)
    exact ⟨row,present,(qualifyRow?_coordinates projected).1⟩
  · intro row present selected
    exact contextualRows?_open_target success read unbound present selected

theorem open_write_certified {image next : ImageOf ContextualOperand}
    {raw : RowOf ContextualOperand} {payload : ContextualOperand} {atom : Atom}
    {snapshot : List Row} {rank : String → Nat}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (success : contextualRows? image = some snapshot)
    (ranked : Ranked rank (assignments snapshot))
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none)
    (below : ∀ name ∈ TypeSubst.typeVars atom, rank name < rank (referenceName raw.reference)) :
    ReadoutCertificate
      ⟨assignments (snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))), []⟩
      (normalize (assignments (snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))))) :=
  contextualRows?_certified (contextualRows?_write written qualifiedPayload success)
    (open_write_ranked success ranked read unbound next.writeClock below)

/-- Every pending operand uses the same old and new finite readout. Filling an
open slot absorbs the previous materialization simultaneously, including all
repeated occurrences and still-open residual variables. -/
theorem open_write_pending_absorbed {image next : ImageOf ContextualOperand}
    {raw : RowOf ContextualOperand} {payload : ContextualOperand} {atom : Atom}
    {snapshot : List Row} {rank : String → Nat}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (success : contextualRows? image = some snapshot)
    (ranked : Ranked rank (assignments snapshot))
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none)
    (below : ∀ name ∈ TypeSubst.typeVars atom, rank name < rank (referenceName raw.reference))
    (pending : List Atom) :
    (pending.map (normalize (assignments snapshot)).apply).map
      (normalize (assignments (snapshot.map
        (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply =
    pending.map (normalize (assignments (snapshot.map
      (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply :=
  (contextualRows?_certified success ranked).pending_absorbed
    (open_write_certified written qualifiedPayload success ranked read unbound below)
    (fun valuation model => (open_write_models success read unbound next.writeClock atom valuation).mp model |>.1)
    pending

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Algorithms.WellFoundedServices

private theorem assignment_dependency {entries : TypeSubst} {key name : String} {value : Atom}
    (stored : (key, value) ∈ entries) (occurs : name ∈ TypeSubst.typeVars value) :
    Spec.Match.Merge.ClassDepends ⟨entries, []⟩ key name := by
  refine ⟨key, value, name, stored, ?_, ?_, ?_, ?_⟩
  · simp [Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep]
  · exact Spec.Match.Merge.mem_vars_iff_atomOccurs.mp
      (by simpa only [← TypeSubst.typeVars_eq_vars] using occurs)
  · simp [Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep]
  · rintro ⟨_, different, same⟩
    have equal : name = key := by
      simpa [Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep] using same
    exact different equal.symm

/-- Acyclic assignments earn a decreasing variable measure through the existing
finite dependency scheduler. No allocation order or caller-supplied ranking is
part of this admission. -/
theorem exists_ranked_of_loopFree (entries : TypeSubst)
    (acyclic : Spec.Match.Merge.SemanticLoopFree ⟨entries, []⟩) :
    ∃ rank : String → Nat, Ranked rank entries := by
  let bindings : Bindings := ⟨entries, []⟩
  let catalogue := bindings.dependencyCatalogue
  have checked : catalogue.acyclic?.isSome := by
    apply catalogue.acyclic?_isSome_iff.mpr
    intro name loop
    apply acyclic name
    simpa only [catalogue, bindings,
      Spec.Match.Merge.dependencyCatalogue_uses_eq_classDepends] using loop
  obtain ⟨certificate, _accepted⟩ := Option.isSome_iff_exists.mp checked
  refine ⟨catalogue.orderMeasure certificate.order, ?_⟩
  intro key value stored name occurs
  apply certificate.respects.orderMeasure_lt certificate.covers
  exact (Spec.Match.Merge.dependencyCatalogue_uses_iff_classDepends).mpr
    (assignment_dependency stored occurs)

/-- A decreasing assignment measure excludes every class-dependency cycle.
This is a structural property of the store, independent of its row order. -/
theorem Ranked.loopFree {entries : TypeSubst} {rank : String → Nat}
    (ranked : Ranked rank entries) : Spec.Match.Merge.SemanticLoopFree ⟨entries, []⟩ := by
  have one : ∀ source target,
      Spec.Match.Merge.ClassDepends ⟨entries, []⟩ source target → rank target < rank source := by
    intro source target edge
    obtain ⟨key, value, dependency, stored, sourceClass, occurs, targetClass, _proper⟩ := edge
    have sourceEq : source = key := by
      simpa [Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep] using sourceClass
    have targetEq : target = dependency := by
      simpa [Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep] using targetClass
    subst source
    subst target
    apply ranked key value stored dependency
    rw [TypeSubst.typeVars_eq_vars]
    exact Spec.Match.Merge.mem_vars_iff_atomOccurs.mpr occurs
  have path : ∀ source target,
      Relation.TransGen (Spec.Match.Merge.ClassDepends ⟨entries, []⟩) source target →
        rank target < rank source := by
    intro source target steps
    induction steps with
    | single edge => exact one _ _ edge
    | tail _ edge ih => exact Nat.lt_trans (one _ _ edge) ih
  intro name loop
  exact Nat.lt_irrefl _ (path name name loop)

/-- The ranked finite-tree component covers exactly the acyclic assignment
stores. Choosing a decreasing measure does not restrict allocation order. -/
theorem exists_ranked_iff_loopFree (entries : TypeSubst) :
    (∃ rank : String → Nat, Ranked rank entries) ↔
      Spec.Match.Merge.SemanticLoopFree ⟨entries, []⟩ :=
  ⟨fun ⟨_rank, ranked⟩ => ranked.loopFree, exists_ranked_of_loopFree entries⟩

/-- The existing normalization constructs the independent readout certificate
for every finite, uniquely assigned acyclic store, without prescribing the
backend's variable ordering. -/
theorem normalize_certified_of_loopFree {entries : TypeSubst}
    (unique : entries.keys.Nodup)
    (acyclic : Spec.Match.Merge.SemanticLoopFree ⟨entries, []⟩) :
    ReadoutCertificate ⟨entries, []⟩ (normalize entries) := by
  obtain ⟨rank, ranked⟩ := exists_ranked_of_loopFree entries acyclic
  exact normalize_certified unique ranked

/-- The actual total dependency-loop check earns the same independent
certificate. A failed rank check is not silently interpreted as no answers. -/
theorem normalize_certified_of_noLoop {entries : TypeSubst}
    (unique : entries.keys.Nodup) (checked : Bindings.hasLoop ⟨entries, []⟩ = false) :
    ReadoutCertificate ⟨entries, []⟩ (normalize entries) := by
  apply normalize_certified_of_loopFree unique
  intro name loop
  have refused := (Spec.Match.Merge.hasLoop_eq_true_iff_cycle ⟨entries, []⟩).mpr ⟨name, loop⟩
  simp only [checked, Bool.false_eq_true] at refused

namespace CatalogueRankControls

def chain : TypeSubst := [("x", .expression [.symbol "f", .var "y"]), ("y", .var "z")]

theorem chain_has_no_loop : Bindings.hasLoop ⟨chain, []⟩ = false := by decide +kernel

theorem reversed_chain_has_no_loop : Bindings.hasLoop ⟨chain.reverse, []⟩ = false := by decide +kernel

theorem chain_earns_certificate : ReadoutCertificate ⟨chain, []⟩ (normalize chain) :=
  normalize_certified_of_noLoop (by decide +kernel) chain_has_no_loop

theorem reversed_chain_earns_certificate :
    ReadoutCertificate ⟨chain.reverse, []⟩ (normalize chain.reverse) :=
  normalize_certified_of_noLoop (by decide +kernel) reversed_chain_has_no_loop

theorem both_row_orders_keep_one_residual_variable :
    (normalize chain).apply (.expression [.var "x", .var "y", .var "z"]) =
      .expression [.expression [.symbol "f", .var "z"], .var "z", .var "z"] ∧
    (normalize chain.reverse).apply (.expression [.var "x", .var "y", .var "z"]) =
      .expression [.expression [.symbol "f", .var "z"], .var "z", .var "z"] := by
  simp [chain, normalize, normalizeFrom, TypeSubst.bind, TypeSubst.apply,
    TypeSubst.lookup, TypeSubst.applyAssignment, TypeSubst.erase]

def cycle : TypeSubst := [("x", .var "y"), ("y", .var "x")]

theorem cyclic_alias_is_detected : Bindings.hasLoop ⟨cycle, []⟩ = true := by decide +kernel

theorem cyclic_alias_has_no_decreasing_measure : ¬ ∃ rank : String → Nat, Ranked rank cycle := by
  rintro ⟨rank, ranked⟩
  have loopFree := ranked.loopFree
  have present := (Spec.Match.Merge.hasLoop_eq_true_iff_cycle ⟨cycle, []⟩).mp cyclic_alias_is_detected
  obtain ⟨name, loop⟩ := present
  exact loopFree name loop

end CatalogueRankControls

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot

/-- The actual snapshot and loop checker earn a readout without a supplied
variable ranking or a restriction on directory/assignment ordering. -/
theorem contextualRows?_certified_of_noLoop {image : ImageOf ContextualOperand}
    {snapshot : List Row} (success : contextualRows? image = some snapshot)
    (checked : Bindings.hasLoop ⟨assignments snapshot, []⟩ = false) :
    ReadoutCertificate ⟨assignments snapshot, []⟩ (normalize (assignments snapshot)) :=
  normalize_certified_of_noLoop (assignments_unique (contextualRows?_unique success)) checked

theorem prepareScoped?_certified_of_noLoop {globals : List String}
    {image : ImageOf ContextualOperand} {operands : List ContextualOperand}
    {snapshot : List Row} {qualified : List Atom}
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified))
    (checked : Bindings.hasLoop ⟨assignments snapshot, []⟩ = false) :
    ReadoutCertificate ⟨assignments snapshot, []⟩ (normalize (assignments snapshot)) :=
  contextualRows?_certified_of_noLoop (prepare?_components (prepareScoped?_success prepared)).1 checked

/-- This applies even to an overwrite: a new acyclic snapshot earns a new
certificate. Strengthening is a separate property of writes to open slots. -/
theorem write_certified_of_noLoop {image next : ImageOf ContextualOperand}
    {target : Ref} {payload : ContextualOperand} {atom : Atom} {snapshot : List Row}
    (written : image.write? target (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (success : contextualRows? image = some snapshot)
    (checked : Bindings.hasLoop
      ⟨assignments (snapshot.map (RowOf.afterWrite next.writeClock target (some atom))), []⟩ = false) :
    ReadoutCertificate
      ⟨assignments (snapshot.map (RowOf.afterWrite next.writeClock target (some atom))), []⟩
      (normalize (assignments (snapshot.map (RowOf.afterWrite next.writeClock target (some atom))))) :=
  contextualRows?_certified_of_noLoop (contextualRows?_write written qualifiedPayload success) checked

theorem open_write_pending_absorbed_of_noLoop {image next : ImageOf ContextualOperand}
    {raw : RowOf ContextualOperand} {payload : ContextualOperand} {atom : Atom} {snapshot : List Row}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (success : contextualRows? image = some snapshot)
    (beforeChecked : Bindings.hasLoop ⟨assignments snapshot, []⟩ = false)
    (afterChecked : Bindings.hasLoop
      ⟨assignments (snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))), []⟩ = false)
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none)
    (pending : List Atom) :
    (pending.map (normalize (assignments snapshot)).apply).map
      (normalize (assignments (snapshot.map
        (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply =
    pending.map (normalize (assignments (snapshot.map
      (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply :=
  (contextualRows?_certified_of_noLoop success beforeChecked).pending_absorbed
    (write_certified_of_noLoop written qualifiedPayload success afterChecked)
    (fun valuation model => (open_write_models success read unbound next.writeClock atom valuation).mp model |>.1)
    pending

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.WriteControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open RuntimeRefinement

abbrev caller := Controls.caller
abbrev child := Controls.child
abbrev callerX := Controls.callerX
abbrev childX := Controls.childX
abbrev image := Controls.openAliasImage

def payload : ContextualOperand := (child, .symbol "A")
def next : ImageOf ContextualOperand :=
  (image.write? childX (some payload)).get (by decide +kernel)

theorem actual_write : image.write? childX (some payload) = some next :=
  (Option.some_get _).symm

def beforeRows : List Row := (contextualRows? image).get (by decide +kernel)
def afterRows : List Row := beforeRows.map (RowOf.afterWrite next.writeClock childX (some (.symbol "A")))
def openRow : RowOf ContextualOperand := ⟨childX, "x", ⟨none, 0, 11, none⟩⟩
def pending : List ContextualOperand :=
  [(caller, .expression [.symbol "pair", .var "x", .var "x"]), (child, .var "x")]
def qualified : List Atom :=
  [.expression [.symbol "pair", .var (referenceName callerX), .var (referenceName callerX)],
    .var (referenceName childX)]

attribute [local simp] readout? prepare? contextualRows? qualifyRowsFrom? qualifyRow? qualify?
  rows entryRows Row.ofEntry EntryOf.initial entryEnv image_frameAt List.range_succ List.ofFn_succ
  assignments normalize normalizeFrom TypeSubst.bind TypeSubst.apply TypeSubst.applyAssignment
  TypeSubst.lookup TypeSubst.erase RuntimeRefinement.renameTypeVars nameIn
  MetavariableFrame.indexOf referenceName freeName Token.ref
  Controls.caller Controls.child Controls.callerX Controls.childX Controls.openAliasImage
  caller child callerX childX image payload beforeRows pending qualified

theorem before_snapshot : contextualRows? image = some beforeRows :=
  (Option.some_get _).symm

theorem before_prepared : prepareScoped? [] image pending = some (beforeRows, qualified) := by
  simp [prepareScoped?, operandScope, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem payload_qualified : qualify? image payload = some (.symbol "A") := by simp

theorem payload_scoped : operandScope [] image payload = true := by
  simp [operandScope, TypeSubst.typeVars]

theorem target_open : readRow? image openRow.reference = some openRow ∧
    openRow.observed.value = none := by decide +kernel

theorem after_prepared : prepareScoped? [] next pending = some (afterRows, qualified) :=
  prepareScoped?_write actual_write payload_qualified payload_scoped before_prepared

theorem after_snapshot : contextualRows? next = some afterRows :=
  contextualRows?_write actual_write payload_qualified before_snapshot

theorem before_assignments : assignments beforeRows =
    [(referenceName callerX, .var (referenceName childX))] := by simp

theorem after_assignments : assignments afterRows =
    [(referenceName callerX, .var (referenceName childX)), (referenceName childX, .symbol "A")] := by
  simp [afterRows, RowOf.afterWrite]

def rank (name : String) : Nat := if name = referenceName callerX then 2 else 1

theorem before_ranked : Ranked rank (assignments beforeRows) := by
  rw [before_assignments]
  intro name value member varName occurs
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩
  simp only [TypeSubst.typeVars, List.mem_singleton] at occurs
  subst varName
  simp [rank]

theorem after_certificate : ReadoutCertificate ⟨assignments afterRows, []⟩
    (normalize (assignments afterRows)) :=
  open_write_certified actual_write payload_qualified before_snapshot before_ranked
    target_open.1 target_open.2 (by simp [TypeSubst.typeVars])

theorem repeated_aliases_share_new_value : readout? next pending =
    some [.expression [.symbol "pair", .symbol "A", .symbol "A"], .symbol "A"] := by
  rw [readout?_prepared (prepareScoped?_success after_prepared), after_assignments]
  simp

theorem old_pending_tuple_absorbed :
    (qualified.map (normalize (assignments beforeRows)).apply).map
        (normalize (assignments afterRows)).apply =
      qualified.map (normalize (assignments afterRows)).apply :=
  open_write_pending_absorbed actual_write payload_qualified before_snapshot before_ranked
    target_open.1 target_open.2 (by simp [TypeSubst.typeVars]) qualified

theorem clock_advances_once : next.writeClock = 12 :=
  ImageOf.write_advances_clock actual_write

theorem complete_inventory_preserved : next.inventory = image.inventory :=
  inventory_write actual_write

theorem exact_versions_and_clock : (rows next).map (fun row =>
    (row.reference, row.observed.writeVersion, row.observed.writeClock,
      row.observed.activationBoundary)) = [(callerX, 0, 12, none), (childX, 12, 12, none)] := by
  rw [rows_write actual_write, clock_advances_once]
  simp [RowOf.afterWrite]

theorem structural_call_not_forced : (normalize (assignments afterRows)).apply
    (.expression [.symbol "effect!", .var (referenceName childX)]) =
      .expression [.symbol "effect!", .symbol "A"] := by
  rw [after_assignments]
  simp

theorem stale_write_refused : image.write? ⟨1, 9, 0⟩ (some payload) = none := by decide +kernel

def hiddenPayload : ContextualOperand := (child, .var "hidden")
def hiddenNext : ImageOf ContextualOperand :=
  (image.write? childX (some hiddenPayload)).get (by decide +kernel)

theorem undeclared_payload_scope_refused : prepareScoped? [] hiddenNext pending = none := by
  decide +kernel

def stalePayloadNext : ImageOf ContextualOperand :=
  (image.write? childX (some (⟨1, 9⟩, .var "x"))).get (by decide +kernel)

theorem stale_stored_context_is_not_an_open_slot : contextualRows? stalePayloadNext = none := by
  decide +kernel

/-- A self-dependent replacement is outside the finite acyclic profile. The
logical write operation itself remains available; no global cycle ban is inferred. -/
theorem self_dependent_payload_has_no_rank (rankOf : String → Nat) :
    ¬ (∀ name ∈ TypeSubst.typeVars (.var (referenceName childX)),
      rankOf name < rankOf (referenceName childX)) := by
  intro below
  exact Nat.lt_irrefl _ (below _ (by simp [TypeSubst.typeVars]))

def overwritten : ImageOf ContextualOperand :=
  (next.write? childX (some (child, .symbol "B"))).get (by decide +kernel)

theorem actual_overwrite : next.write? childX (some (child, .symbol "B")) = some overwritten :=
  (Option.some_get _).symm

def overwrittenRows : List Row := afterRows.map
  (RowOf.afterWrite overwritten.writeClock childX (some (.symbol "B")))

theorem overwritten_snapshot : contextualRows? overwritten = some overwrittenRows :=
  contextualRows?_write actual_overwrite
    (by rw [qualify?_write actual_write]; simp) after_snapshot

theorem overwritten_assignments : assignments overwrittenRows =
    [(referenceName callerX, .var (referenceName childX)), (referenceName childX, .symbol "B")] := by
  simp [overwrittenRows, afterRows, RowOf.afterWrite]

theorem overwrite_does_not_absorb_old_readout :
    (normalize (assignments overwrittenRows)).apply
      ((normalize (assignments afterRows)).apply (.var (referenceName childX))) ≠
    (normalize (assignments overwrittenRows)).apply (.var (referenceName childX)) := by
  rw [overwritten_assignments, after_assignments]
  simp

theorem overwrite_does_not_strengthen_old_theory :
    ¬ (∀ valuation, TypeBindingSatisfied valuation ⟨assignments overwrittenRows, []⟩ →
      TypeBindingSatisfied valuation ⟨assignments afterRows, []⟩) := by
  intro strengthens
  have current : TypeBindingSatisfied (fun _ => .symbol "B")
      ⟨assignments overwrittenRows, []⟩ := by
    refine ⟨?_, ?_⟩
    · intro name value member
      rw [overwritten_assignments] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [applyTypeValuation]
    · intro left right member
      simp at member
  have previous := (strengthens _ current).1 (referenceName childX) (.symbol "A")
    (by rw [after_assignments]; simp)
  simp [applyTypeValuation] at previous


def symbolicPayload : ContextualOperand := (child, .expression [.symbol "call", .var "shared"])
def symbolicNext : ImageOf ContextualOperand :=
  (image.write? childX (some symbolicPayload)).get (by decide +kernel)
def symbolicValue : Atom := .expression [.symbol "call", .var (freeName "shared")]
def symbolicRows : List Row := beforeRows.map
  (RowOf.afterWrite symbolicNext.writeClock childX (some symbolicValue))

theorem symbolic_write : image.write? childX (some symbolicPayload) = some symbolicNext :=
  (Option.some_get _).symm

theorem symbolic_prepared : prepareScoped? ["shared"] symbolicNext pending =
    some (symbolicRows, qualified) := by
  apply prepareScoped?_write symbolic_write
  · simp [symbolicPayload, symbolicValue]
  · simp [operandScope, symbolicPayload, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · simp [prepareScoped?, operandScope, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem symbolic_assignments : assignments symbolicRows =
    [(referenceName callerX, .var (referenceName childX)),
      (referenceName childX, symbolicValue)] := by
  simp [symbolicRows, RowOf.afterWrite]

def symbolicRank (name : String) : Nat :=
  if name = referenceName callerX then 2 else if name = referenceName childX then 1 else 0

theorem symbolic_ranked : Ranked symbolicRank (assignments symbolicRows) := by
  rw [symbolic_assignments]
  intro key value member name occurs
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [TypeSubst.typeVars, List.mem_singleton] at occurs
    subst name
    simp [symbolicRank]
  · simp [symbolicValue, TypeSubst.typeVars, TypeSubst.typeVarsList] at occurs
    subst name
    simp [symbolicRank]
    decide +kernel

theorem symbolic_certificate : ReadoutCertificate ⟨assignments symbolicRows, []⟩
    (normalize (assignments symbolicRows)) :=
  prepareScoped?_certified symbolic_prepared symbolic_ranked

theorem repeated_symbolic_calls_remain_syntax_and_share_residual : readout? symbolicNext pending =
    some [.expression [.symbol "pair", symbolicValue, symbolicValue], symbolicValue] := by
  rw [readout?_prepared (prepareScoped?_success symbolic_prepared), symbolic_assignments]
  simp [symbolicValue]
  decide +kernel

def cyclicNext : ImageOf ContextualOperand :=
  (image.write? childX (some (child, .var "x"))).get (by decide +kernel)
def cyclicRows : List Row := beforeRows.map
  (RowOf.afterWrite cyclicNext.writeClock childX (some (.var (referenceName childX))))

theorem actual_cyclic_write : image.write? childX (some (child, .var "x")) = some cyclicNext :=
  (Option.some_get _).symm

theorem cyclic_write_still_has_scoped_syntax :
    prepareScoped? [] cyclicNext pending = some (cyclicRows, qualified) :=
  prepareScoped?_write actual_cyclic_write (by simp)
    (by simp [operandScope, TypeSubst.typeVars]) before_prepared

theorem actual_cyclic_write_fails_finite_loop_check :
    Bindings.hasLoop ⟨assignments cyclicRows, []⟩ = true := by
  have stored : assignments cyclicRows =
      [(referenceName callerX, .var (referenceName childX)),
        (referenceName childX, .var (referenceName childX))] := by
    simp [cyclicRows, RowOf.afterWrite]
  rw [stored]
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.WriteControls


namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation

/-- Full finite assignment support, including assigned keys. -/
private def support (entries : TypeSubst) (name : String) : Prop :=
  name ∈ entries.keys ∨ ∃ key value, (key, value) ∈ entries ∧ name ∈ TypeSubst.typeVars value

private theorem support_cons (key : String) (value : Atom) (entries : TypeSubst)
    (name : String) :
    support ((key, value) :: entries) name ↔
      name = key ∨ name ∈ TypeSubst.typeVars value ∨ support entries name := by
  simp only [support, TypeSubst.keys, List.map_cons, List.mem_cons]
  constructor
  · rintro ((same | old) | ⟨k,v,(pair | old),occurs⟩)
    · exact Or.inl same
    · exact Or.inr (Or.inr (Or.inl old))
    · cases pair
      exact Or.inr (Or.inl occurs)
    · exact Or.inr (Or.inr (Or.inr ⟨k,v,old,occurs⟩))
  · rintro (same | occurs | old | ⟨k,v,old,occurs⟩)
    · exact Or.inl (Or.inl same)
    · exact Or.inr ⟨key,value,Or.inl rfl,occurs⟩
    · exact Or.inl (Or.inr old)
    · exact Or.inr ⟨k,v,Or.inr old,occurs⟩

private theorem apply_support (entries : TypeSubst) (atom : Atom) (name : String)
    (occurs : name ∈ TypeSubst.typeVars (entries.apply atom)) :
    name ∈ TypeSubst.typeVars atom ∨ support entries name := by
  by_contra missing
  have outside := not_or.mp missing
  have values : ∀ key value, (key,value) ∈ entries →
      ∀ candidate ∈ TypeSubst.typeVars value, candidate ∉ [name] := by
    intro key value present candidate occursHere equal
    have same : candidate = name := List.mem_singleton.mp equal
    subst candidate
    exact outside.2 (Or.inr ⟨key,value,present,occursHere⟩)
  have unchanged := TypeSubst.apply_variable_avoids values atom
    (fun candidate present equal => outside.1 ((List.mem_singleton.mp equal) ▸ present))
    name occurs
  exact unchanged (by simp)

private theorem apply_preserves_unassigned (entries : TypeSubst) (name : String)
    (unassigned : name ∉ entries.keys) (atom : Atom) :
    name ∈ TypeSubst.typeVars atom → name ∈ TypeSubst.typeVars (entries.apply atom) := by
  induction atom using Atom.rec
      (motive_2 := fun atoms => name ∈ TypeSubst.typeVarsList atoms →
        name ∈ TypeSubst.typeVarsList (atoms.map entries.apply)) with
  | symbol value => simp [TypeSubst.typeVars]
  | grounded value => simp [TypeSubst.typeVars]
  | var variableName =>
      intro occurs
      have same : name = variableName := by simpa [TypeSubst.typeVars] using occurs
      subst variableName
      simp [TypeSubst.apply, TypeSubst.lookup_eq_none_of_not_mem_keys unassigned,
        TypeSubst.typeVars]
  | expression atoms ih => simpa only [TypeSubst.apply, TypeSubst.typeVars] using ih
  | nil =>
      rename_i impossible
      simp [TypeSubst.typeVarsList] at impossible
  | cons atom atoms first rest occurs =>
      simp only [TypeSubst.typeVarsList, List.map_cons, List.mem_append] at occurs ⊢
      exact Or.imp first rest occurs

private theorem bind_support {entries : TypeSubst} {key : String} (value : Atom)
    (fresh : key ∉ entries.keys) (name : String) :
    support (entries.bind key value) name ↔
      name = key ∨ name ∈ TypeSubst.typeVars value ∨ support entries name := by
  have erase : entries.erase key = entries := by
    apply List.filter_eq_self.mpr
    intro entry member
    have different : entry.1 ≠ key := by
      intro same
      exact fresh (List.mem_map.mpr ⟨entry,member,same⟩)
    simpa using different
  have keys : ∀ candidate, candidate ∈ (entries.bind key value).keys ↔
      candidate = key ∨ candidate ∈ entries.keys := by
    intro candidate
    rw [TypeSubst.keys_bind]
    simp only [List.mem_cons, List.mem_filter, bne_iff_ne]
    constructor
    · rintro (same | ⟨old,_⟩)
      · exact Or.inl same
      · exact Or.inr old
    · rintro (same | old)
      · exact Or.inl same
      · exact Or.inr ⟨old, fun same => fresh (same ▸ old)⟩
  constructor
  · rintro (assigned | ⟨stored,term,member,occurs⟩)
    · rcases (keys name).mp assigned with same | old
      · exact Or.inl same
      · exact Or.inr (Or.inr (Or.inl old))
    · simp only [TypeSubst.bind, erase, List.mem_cons] at member
      rcases member with same | older
      · cases same
        exact Or.inr (apply_support entries value name occurs)
      · obtain ⟨⟨oldKey,oldValue⟩,present,equal⟩ := List.mem_map.mp older
        cases equal
        rcases apply_support [(key,entries.apply value)] oldValue name occurs with raw | added
        · exact Or.inr (Or.inr (Or.inr ⟨oldKey,oldValue,present,raw⟩))
        · rw [support_cons] at added
          rcases added with same | read | empty
          · exact Or.inl same
          · exact Or.inr (apply_support entries value name read)
          · simp [support,TypeSubst.keys] at empty
  · rintro (same | raw | old)
    · exact Or.inl ((keys name).mpr (Or.inl same))
    · by_cases assigned : name ∈ entries.keys
      · exact Or.inl ((keys name).mpr (Or.inr assigned))
      · exact Or.inr ⟨key,entries.apply value,by simp [TypeSubst.bind],
          apply_preserves_unassigned entries name assigned value raw⟩
    · rcases old with assigned | ⟨oldKey,oldValue,present,occurs⟩
      · exact Or.inl ((keys name).mpr (Or.inr assigned))
      · by_cases same : name = key
        · exact Or.inl ((keys name).mpr (Or.inl same))
        · refine Or.inr ⟨oldKey,TypeSubst.applyAssignment key (entries.apply value) oldValue,?_,?_⟩
          · simp only [TypeSubst.bind,erase,List.mem_cons]
            exact Or.inr (List.mem_map.mpr ⟨(oldKey,oldValue),present,rfl⟩)
          · exact apply_preserves_unassigned [(key,entries.apply value)] name
              (by simpa [TypeSubst.keys]) oldValue occurs

private theorem normalizeFrom_support {entries incoming : TypeSubst}
    (unique : entries.keys.Nodup)
    (fresh : ∀ name ∈ entries.keys, name ∉ incoming.keys) (name : String) :
    support (normalizeFrom incoming entries) name ↔
      support incoming name ∨ support entries name := by
  induction entries generalizing incoming with
  | nil => simp [normalizeFrom,support,TypeSubst.keys]
  | cons entry rest ih =>
      rcases entry with ⟨key,value⟩
      have tailUnique := (List.nodup_cons.mp unique).2
      have keyAbsent := (List.nodup_cons.mp unique).1
      have freshKey : key ∉ incoming.keys := fresh key (by simp [TypeSubst.keys])
      have tailFresh : ∀ n ∈ TypeSubst.keys rest, n ∉ (incoming.bind key value).keys := by
        intro n member after
        rw [TypeSubst.keys_bind] at after
        rcases List.mem_cons.mp after with equal | old
        · exact keyAbsent (equal ▸ member)
        · exact fresh n (by
            simp only [TypeSubst.keys,List.map_cons,List.mem_cons] at member ⊢
            exact Or.inr member) (List.mem_filter.mp old).1
      change support (normalizeFrom (incoming.bind key value) rest) name ↔ _
      rw [ih tailUnique tailFresh,bind_support value freshKey,support_cons]
      tauto

/-- Normalizing unique actual assignments preserves every variable relevant
to freshening, including keys whose final value is closed. No model or expected
readout is assumed. -/
theorem normalize_support {entries : TypeSubst} (unique : entries.keys.Nodup)
    (name : String) :
    name ∈ specBindingVars ⟨normalize entries, []⟩ ↔
      name ∈ specBindingVars ⟨entries, []⟩ := by
  have support_eq (xs : TypeSubst) : name ∈ specBindingVars ⟨xs,[]⟩ ↔ support xs name := by
    simp only [specBindingVars,List.flatMap_nil,List.append_nil,List.mem_flatMap,
      List.mem_cons,support,TypeSubst.keys,List.mem_map]
    constructor
    · rintro ⟨⟨k,v⟩,member,equal | occurs⟩
      · exact Or.inl ⟨(k,v),member,equal.symm⟩
      · exact Or.inr ⟨k,v,member,occurs⟩
    · rintro (⟨⟨k,v⟩,member,equal⟩ | ⟨k,v,member,occurs⟩)
      · exact ⟨(k,v),member,Or.inl equal.symm⟩
      · exact ⟨(k,v),member,Or.inr occurs⟩
  rw [support_eq,support_eq]
  simpa [normalize,support,TypeSubst.keys] using
    normalizeFrom_support (incoming := []) unique (by simp [TypeSubst.keys]) name

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore


namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport
open Spec.Type RuntimeRefinement Theory

private abbrev read (valuation : String → Metta.Atom) (atom : Atom) : Metta.Atom :=
  applyClassSolution valuation (encodeModelAtom atom)

/-- A structural valuation satisfying a finite table absorbs its application.
The valuation may use ground constructors outside the native HE signature. -/
theorem presentation_he_model_absorbs {valuation : String → Metta.Atom}
    {table : TypeSubst} (satisfied : HEBindingSatisfied valuation ⟨table, []⟩)
    (atom : Atom) :
    applyClassSolution valuation (encodeModelAtom (table.apply atom)) =
      applyClassSolution valuation (encodeModelAtom atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (atoms.map (fun atom => read valuation (table.apply atom))) =
        atoms.map (read valuation)) with
  | symbol name => simp only [TypeSubst.apply]
  | grounded value => simp only [TypeSubst.apply]
  | var name =>
      cases found : table.lookup name with
      | none => simp [TypeSubst.apply, found]
      | some value =>
          simpa [TypeSubst.apply, found, encodeModelAtom, applyClassSolution] using
            (satisfied.1 name value (TypeSubst.lookup_eq_some_mem found)).symm
  | expression atoms ih =>
      simpa only [TypeSubst.apply, encodeModelAtom, encodeModelAtoms_eq_map,
        List.map_map, applyClassSolution, Metta.Atom.expr.injEq, read, Function.comp_def] using ih
  | nil => rfl
  | cons atom atoms first rest => exact congrArg₂ List.cons first rest

private theorem assignment_he_absorbs {valuation : String → Metta.Atom}
    {name : String} {value : Atom}
    (equation : valuation name = read valuation value) (atom : Atom) :
    read valuation (TypeSubst.applyAssignment name value atom) = read valuation atom := by
  apply presentation_he_model_absorbs
  exact ⟨by simpa using equation, by simp⟩

private theorem bind_he_model {valuation : String → Metta.Atom} {table : TypeSubst}
    {name : String} {value : Atom}
    (incoming : HEBindingSatisfied valuation ⟨table, []⟩)
    (equation : valuation name = read valuation value) :
    HEBindingSatisfied valuation ⟨table.bind name value, []⟩ := by
  have resolved : valuation name = read valuation (table.apply value) :=
    equation.trans (presentation_he_model_absorbs incoming value).symm
  refine ⟨?_, by simp⟩
  intro key stored member
  simp only [TypeSubst.bind, List.mem_cons] at member
  rcases member with head | tail
  · cases head
    exact resolved
  · obtain ⟨⟨key, stored⟩, member, equal⟩ := List.mem_map.mp tail
    cases equal
    change valuation key = read valuation (TypeSubst.applyAssignment name (table.apply value) stored)
    rw [assignment_he_absorbs resolved]
    exact incoming.1 _ _ (List.mem_filter.mp member).1

mutual

private theorem applied_he_model {valuation : String → Metta.Atom}
    {table output : TypeSubst} {left right : Atom}
    (derived : AppliedReducedTypeMatchRel table left right output)
    (incoming : HEBindingSatisfied valuation ⟨table, []⟩)
    (equation : read valuation left = read valuation right) :
    HEBindingSatisfied valuation ⟨output, []⟩ :=
  match derived with
  | .identical _ _ => incoming
  | .bindLeft _ => bind_he_model incoming (by simpa only [read, encodeModelAtom, applyClassSolution] using equation)
  | .bindRight _ _ => bind_he_model incoming (by simpa only [read, encodeModelAtom, applyClassSolution] using equation.symm)
  | .expression children =>
      applied_list_he_model children incoming (by
        simpa only [read, encodeModelAtom, encodeModelAtoms_eq_map, applyClassSolution,
          List.map_map, Metta.Atom.expr.injEq, Function.comp_def] using equation)

/-- The exact syntactic presentation step preserves every structural model of
its incoming table and its selected equation. -/
theorem applied_presentation_he_model {valuation : String → Metta.Atom}
    {table output : TypeSubst} {left right : Atom}
    (derived : AppliedTypePresentationMatchRel table left right output)
    (incoming : HEBindingSatisfied valuation ⟨table, []⟩)
    (equation : HEAtomEquationSatisfied valuation left right) :
    HEBindingSatisfied valuation ⟨output, []⟩ :=
  match derived with
  | .ordinary leftApply rightApply applied =>
      applied_he_model applied incoming (by
        unfold read
        rw [← leftApply, ← rightApply,
          presentation_he_model_absorbs incoming,
          presentation_he_model_absorbs incoming]
        exact equation)

private theorem applied_list_he_model {valuation : String → Metta.Atom}
    {table output : TypeSubst} {left right : List Atom}
    (derived : AppliedReducedTypeListMatchRel table left right output)
    (incoming : HEBindingSatisfied valuation ⟨table, []⟩)
    (equations : left.map (read valuation) = right.map (read valuation)) :
    HEBindingSatisfied valuation ⟨output, []⟩ :=
  match derived with
  | .nil _ => incoming
  | .cons head tail => by
      simp only [List.map_cons, List.cons.injEq] at equations
      exact applied_list_he_model tail
        (applied_presentation_he_model head incoming equations.1) equations.2

end

/-- An exact finite equation fold preserves models in the larger structural
atom signature; no executable matcher or evaluator enters this statement. -/
theorem EquationListPresentationRel.he_model {valuation : String → Metta.Atom}
    {equations : List (Atom × Atom)} {table output : TypeSubst}
    (fold : EquationListPresentationRel equations table output)
    (incoming : HEBindingSatisfied valuation ⟨table, []⟩)
    (satisfied : ∀ equation ∈ equations,
      HEAtomEquationSatisfied valuation equation.1 equation.2) :
    HEBindingSatisfied valuation ⟨output, []⟩ := by
  induction fold with
  | nil => exact incoming
  | cons head tail ih =>
      exact ih (applied_presentation_he_model head incoming
        (satisfied _ List.mem_cons_self))
        (fun equation member => satisfied equation (List.mem_cons_of_mem _ member))

/-- A whole binding presentation is satisfied by every structural model of
its original record, including values outside the native ground signature. -/
theorem EquationListPresentationRel.he_binding_model {valuation : String → Metta.Atom}
    {bindings : Bindings} {table : TypeSubst}
    (fold : EquationListPresentationRel (bindingAtomEquations bindings) [] table)
    (satisfied : HEBindingSatisfied valuation bindings) :
    HEBindingSatisfied valuation ⟨table, []⟩ := by
  apply fold.he_model (by simp [HEBindingSatisfied])
  intro equation member
  change equation ∈ bindings.assignments.map (fun entry => (Atom.var entry.1, entry.2)) ++
    bindings.equalities.map (fun edge => (Atom.var edge.1, Atom.var edge.2)) at member
  rcases List.mem_append.mp member with assignment | equality
  · obtain ⟨⟨name, value⟩, assigned, rfl⟩ := List.mem_map.mp assignment
    simpa only [HEAtomEquationSatisfied, encodeModelAtom, applyClassSolution] using
      satisfied.1 name value assigned
  · obtain ⟨⟨left, right⟩, edge, rfl⟩ := List.mem_map.mp equality
    simpa only [HEAtomEquationSatisfied, encodeModelAtom, applyClassSolution] using
      satisfied.2 left right edge

/-- Native solution implication for finite HE records is conservative under
extension of the structural value signature. The proof presents the source
record, then transports literal substituted equations, not runtime behavior. -/
theorem he_models_of_native_solution_implication {left right : Bindings}
    (implies : ∀ valuation, TypeBindingSatisfied valuation left →
      TypeBindingSatisfied valuation right)
    (valuation : String → Metta.Atom) (satisfied : HEBindingSatisfied valuation left) :
    HEBindingSatisfied valuation right := by
  obtain ⟨table, fold⟩ := exists_binding_presentation
    ⟨_, specTypeBindingSatisfied_of_heBindingSatisfied satisfied⟩
  have native := implies (presentedValuation table)
    ((fold.bindingTheory.2 _).mp
      (normal_presentedValuation_satisfied fold.bindingTheory.1))
  have structural := fold.he_binding_model satisfied
  constructor
  · intro name value member
    have equation := native.1 name value member
    change table.apply (.var name) = _ at equation
    rw [applyTypeValuation_presented_eq_apply] at equation
    have mapped := congrArg (read valuation) equation
    simpa only [read, presentation_he_model_absorbs structural,
      encodeModelAtom, applyClassSolution] using mapped
  · intro leftName rightName member
    have equation := native.2 leftName rightName member
    change table.apply (.var leftName) = table.apply (.var rightName) at equation
    have mapped := congrArg (read valuation) equation
    simpa only [read, presentation_he_model_absorbs structural,
      encodeModelAtom, applyClassSolution] using mapped

/-- Complete native solution equality also preserves all structural models
of the existing extended atom language. -/
theorem he_models_iff_of_native_solutions {left right : Bindings}
    (equivalent : ∀ valuation, TypeBindingSatisfied valuation left ↔
      TypeBindingSatisfied valuation right) (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation left ↔ HEBindingSatisfied valuation right :=
  ⟨he_models_of_native_solution_implication (fun v => (equivalent v).mp) valuation,
    he_models_of_native_solution_implication (fun v => (equivalent v).mpr) valuation⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport
open Spec.Bindings.ScopeObservation

/-- Complete native binding agreement preserves models in the structural
extension as well; no matcher or evaluator observation is assumed. -/
theorem BindingSourceAgreement.he_models {left right : Bindings}
    (same : BindingSourceAgreement left right) (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation left ↔ HEBindingSatisfied valuation right :=
  Spec.Type.Presentation.BindingTheory.he_models_iff_of_native_solutions
    same.solutions valuation

/-- Logical conjunction retains the full structural model interpretation of
both input records. Representative selection remains a separate judgment. -/
theorem Spec.Bindings.ScopeObservation.LogicalMergeRel.he_solutions
    {left right output : Bindings} (merged : LogicalMergeRel left right output)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation output ↔
      HEBindingSatisfied valuation left ∧ HEBindingSatisfied valuation right := by
  rw [merged.1.he_models valuation]
  simp only [HEBindingSatisfied, List.mem_append, or_imp, forall_and]
  tauto

/-- A logical successful conjunction has an actual finite structural model. -/
theorem Spec.Bindings.ScopeObservation.LogicalMergeRel.he_model
    {left right output : Bindings} (merged : LogicalMergeRel left right output) :
    ∃ valuation : String → Metta.Atom, HEBindingSatisfied valuation output := by
  obtain ⟨valuation, satisfied⟩ := merged.2
  exact ⟨_, heBindingSatisfied_of_specTypeBindingSatisfied satisfied⟩

namespace Spec.Type.Presentation.BindingTheory.StructuralModelControls

private def variableAlias : Bindings := ⟨[("left", .var "right")], []⟩
private def equalityAlias : Bindings := ⟨[], [("left", "right")]⟩

/-- The conservative lift includes values which have no native HE ground
constructor. This control uses the structural unit payload explicitly. -/
theorem extended_unit_alias_models :
    HEBindingSatisfied (fun _ => .gnd .unit) variableAlias ∧
      HEBindingSatisfied (fun _ => .gnd .unit) equalityAlias := by
  have same : ∀ valuation, RuntimeRefinement.TypeBindingSatisfied valuation variableAlias ↔
      RuntimeRefinement.TypeBindingSatisfied valuation equalityAlias := by
    intro valuation
    simp [variableAlias, equalityAlias, RuntimeRefinement.TypeBindingSatisfied,
      RuntimeRefinement.applyTypeValuation]
  have leftModel : HEBindingSatisfied (fun _ => .gnd .unit) variableAlias := by
    simp [variableAlias, HEBindingSatisfied, encodeModelAtom, applyClassSolution]
  exact ⟨leftModel, (he_models_iff_of_native_solutions same _).mp leftModel⟩

/-- Full theory, rather than satisfiability alone, is required: two finite
consistent records can require different ground values. -/
theorem different_ground_theories_not_implication :
    ¬ (∀ valuation, RuntimeRefinement.TypeBindingSatisfied valuation
      (⟨[("x", .symbol "A")], []⟩ : Bindings) →
      RuntimeRefinement.TypeBindingSatisfied valuation
        (⟨[("x", .symbol "B")], []⟩ : Bindings)) := by
  intro implies
  have falseModel := implies (fun _ => .symbol "A") (by
    simp [RuntimeRefinement.TypeBindingSatisfied, RuntimeRefinement.applyTypeValuation])
  have impossible := falseModel.1 "x" (.symbol "B") (by simp)
  simp [RuntimeRefinement.applyTypeValuation] at impossible

end Spec.Type.Presentation.BindingTheory.StructuralModelControls
end Mettapedia.Languages.MeTTa.HE

namespace Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation
/-- One independently earned output presentation absorbs the whole old pending
syntax. This is a readout certificate, not an evaluator-correspondence premise. -/
theorem Spec.Bindings.ScopeObservation.LogicalMergeRel.certifies_pending {left right output : Bindings} {oldTable : TypeSubst}
    (logical : LogicalMergeRel left right output) (old : ReadoutCertificate right oldTable) :
    ∃ nextTable, ReadoutCertificate output nextTable ∧
      ∀ pending : List Atom,
        (pending.map oldTable.apply).map nextTable.apply = pending.map nextTable.apply := by
  obtain ⟨nextTable, fold⟩ := exists_binding_presentation logical.2
  have next := ReadoutCertificate.of_fold fold
  exact ⟨nextTable, next, fun pending => old.pending_absorbed next
    (fun valuation satisfied => ((logical.solutions valuation).mp satisfied).2) pending⟩

end Mettapedia.Languages.MeTTa.HE
