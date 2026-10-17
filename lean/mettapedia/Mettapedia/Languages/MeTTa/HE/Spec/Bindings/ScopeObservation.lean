import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness
import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-!
# Scoped observation of private type bindings

Function applicability may introduce a finite theory over fresh type
variables.  The published evaluator threads the resulting binding record,
whereas an implementation may discharge that private theory into its selected
type policy.  The two states are not globally solution-theory equivalent: the
private theory has additional equations.  They are equivalent only at the
finite evaluator-visible scope.

This module states that observation boundary without mentioning an evaluator
or an executable binding representation.  A normal private presentation can
extend any incoming model while preserving every name outside its keys.  The
resulting scoped equivalence is therefore a theorem of freshness, rather than
an equality or quotient imposed on the two binding carriers.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.ExactNormal
open Spec.Type.Presentation.Freshness
open Spec.Type.RuntimeRefinement

/-! ## Valuation algebra -/

mutual

/-- Applying two type valuations successively is application of their
homomorphic composite. -/
theorem applyTypeValuation_comp
    (outer inner : String → Atom) : ∀ atom,
    applyTypeValuation outer (applyTypeValuation inner atom) =
      applyTypeValuation
        (fun name => applyTypeValuation outer (inner name)) atom := by
  intro atom
  cases atom with
  | symbol name => simp [applyTypeValuation]
  | var name => simp [applyTypeValuation]
  | grounded value => simp [applyTypeValuation]
  | expression atoms =>
      simp only [applyTypeValuation, Atom.expression.injEq]
      exact applyTypeValuationList_comp outer inner atoms

/-- List companion of `applyTypeValuation_comp`. -/
theorem applyTypeValuationList_comp
    (outer inner : String → Atom) : ∀ atoms : List Atom,
    (atoms.map (applyTypeValuation inner)).map
        (applyTypeValuation outer) =
      atoms.map (applyTypeValuation
        (fun name => applyTypeValuation outer (inner name))) := by
  intro atoms
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · exact applyTypeValuation_comp outer inner atom
      · exact applyTypeValuationList_comp outer inner atoms

end

mutual

/-- Homomorphic type substitution depends only on the valuation at variables
occurring in the observed atom. -/
theorem applyTypeValuation_congr_of_typeVars
    {left right : String → Atom} (atom : Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVars atom →
      left name = right name) :
    applyTypeValuation left atom = applyTypeValuation right atom := by
  cases atom with
  | symbol name => simp [applyTypeValuation]
  | var name =>
      simpa [applyTypeValuation] using
        agrees name (by simp [TypeSubst.typeVars])
  | grounded value => simp [applyTypeValuation]
  | expression atoms =>
      simp only [applyTypeValuation, Atom.expression.injEq]
      apply applyTypeValuationList_congr_of_typeVars
      intro name member
      exact agrees name (by simpa [TypeSubst.typeVars] using member)

/-- List companion of `applyTypeValuation_congr_of_typeVars`. -/
theorem applyTypeValuationList_congr_of_typeVars
    {left right : String → Atom} (atoms : List Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVarsList atoms →
      left name = right name) :
    atoms.map (applyTypeValuation left) =
      atoms.map (applyTypeValuation right) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply applyTypeValuation_congr_of_typeVars atom
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply applyTypeValuationList_congr_of_typeVars atoms
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

end

/-- Every post-substitution of a type-presentation model is again a model.
This is the substitution-closure property of syntactic equality. -/
theorem TypeSubstSatisfied.postcompose
    {model : String → Atom} {substitution : TypeSubst}
    (satisfied : TypeSubstSatisfied model substitution)
    (post : String → Atom) :
    TypeSubstSatisfied
      (fun name => applyTypeValuation post (model name)) substitution := by
  intro name value member
  calc
    applyTypeValuation post (model name) =
        applyTypeValuation post
          (applyTypeValuation model value) :=
      congrArg (applyTypeValuation post)
        (satisfied name value member)
    _ = applyTypeValuation
          (fun other => applyTypeValuation post (model other)) value :=
      applyTypeValuation_comp post model value

/-- Extend a public valuation through a private finite presentation.  The
presentation supplies the principal shape; the public valuation supplies the
remaining free variables. -/
def extendThroughPresentation
    (base : String → Atom) (substitution : TypeSubst) : String → Atom :=
  fun name =>
    applyTypeValuation base (presentedValuation substitution name)

/-- A normal presentation's extension satisfies its private equations. -/
theorem extendThroughPresentation_satisfied
    {substitution : TypeSubst} (normal : substitution.Normal)
    (base : String → Atom) :
    TypeSubstSatisfied
      (extendThroughPresentation base substitution) substitution := by
  exact TypeSubstSatisfied.postcompose
    (normal_presentedValuation_satisfied normal) base

/-- Outside the private key set, extension is literally the public
valuation. -/
theorem extendThroughPresentation_eq_of_not_mem_keys
    {base : String → Atom} {substitution : TypeSubst} {name : String}
    (fresh : name ∉ substitution.keys) :
    extendThroughPresentation base substitution name = base name := by
  simp [extendThroughPresentation, presentedValuation, TypeSubst.apply,
    TypeSubst.lookup_eq_none_of_not_mem_keys fresh,
    applyTypeValuation, Option.getD]

/-! ## Scoped binding observation -/

/-- Every variable name mentioned by a spec binding theory, including
assignment keys, variables in assignment values, and equality endpoints. -/
def specBindingVars (bindings : Bindings) : List String :=
  bindings.assignments.flatMap
      (fun entry => entry.1 :: TypeSubst.typeVars entry.2) ++
    bindings.equalities.flatMap (fun entry => [entry.1, entry.2])

/-- Two valuations agree on a finite observable name scope. -/
def ValuationsAgreeOn
    (scope : List String) (left right : String → Atom) : Prop :=
  ∀ name ∈ scope, left name = right name

/-- A change of the two relation-list layouts, with every assignment and
explicit equality occurrence retained. This is a representation relation;
it does not identify arbitrary binding theories with equal solution sets. -/
structure BindingRecordPerm (left right : Bindings) : Prop where
  assignments : left.assignments.Perm right.assignments
  equalities : left.equalities.Perm right.equalities

namespace BindingRecordPerm

@[refl] theorem refl (bindings : Bindings) : BindingRecordPerm bindings bindings :=
  ⟨.refl _, .refl _⟩

theorem symm {left right : Bindings} (related : BindingRecordPerm left right) :
    BindingRecordPerm right left := ⟨related.assignments.symm, related.equalities.symm⟩

theorem trans {left middle right : Bindings} (first : BindingRecordPerm left middle)
    (second : BindingRecordPerm middle right) : BindingRecordPerm left right :=
  ⟨first.assignments.trans second.assignments, first.equalities.trans second.equalities⟩

/-- Relation order does not change pointwise satisfaction of the bindings. -/
theorem satisfied_iff {left right : Bindings} (related : BindingRecordPerm left right)
    (valuation : String → Atom) :
    TypeBindingSatisfied valuation left ↔ TypeBindingSatisfied valuation right := by
  constructor
  · intro satisfied
    exact ⟨fun key value member => satisfied.1 key value (related.assignments.mem_iff.mpr member),
      fun first second member => satisfied.2 first second (related.equalities.mem_iff.mpr member)⟩
  · intro satisfied
    exact ⟨fun key value member => satisfied.1 key value (related.assignments.mem_iff.mp member),
      fun first second member => satisfied.2 first second (related.equalities.mem_iff.mp member)⟩

end BindingRecordPerm

/-- Two spec binding theories have the same model observations on a finite
scope.  Each model may extend differently outside the scope; that is exactly
what permits private type variables without identifying the global theories. -/
structure BindingTheoryEquivAt
    (scope : List String) (left right : Bindings) : Prop where
  leftToRight : ∀ leftModel,
    TypeBindingSatisfied leftModel left →
      ∃ rightModel,
        TypeBindingSatisfied rightModel right ∧
          ValuationsAgreeOn scope leftModel rightModel
  rightToLeft : ∀ rightModel,
    TypeBindingSatisfied rightModel right →
      ∃ leftModel,
        TypeBindingSatisfied leftModel left ∧
          ValuationsAgreeOn scope leftModel rightModel

/-- Every relation-list permutation preserves the existing scoped binding
observer, at every scope and without changing a valuation. -/
theorem BindingRecordPerm.theoryEquivAt {left right : Bindings}
    (related : BindingRecordPerm left right) (scope : List String) :
    BindingTheoryEquivAt scope left right := by
  constructor
  · intro model satisfied
    exact ⟨model, (related.satisfied_iff model).mp satisfied, fun _ _ => rfl⟩
  · intro model satisfied
    exact ⟨model, (related.satisfied_iff model).mpr satisfied, fun _ _ => rfl⟩

namespace BindingTheoryEquivAt

/-- Scoped binding observation is reflexive. -/
@[refl] theorem refl (scope : List String) (bindings : Bindings) :
    BindingTheoryEquivAt scope bindings bindings := by
  constructor <;> intro model satisfied <;>
    exact ⟨model, satisfied, fun _ _ => rfl⟩

/-- Scoped binding observation is symmetric. -/
theorem symm {scope : List String} {left right : Bindings}
    (equiv : BindingTheoryEquivAt scope left right) :
    BindingTheoryEquivAt scope right left := by
  constructor
  · intro rightModel rightSatisfied
    obtain ⟨leftModel, leftSatisfied, agrees⟩ :=
      equiv.rightToLeft rightModel rightSatisfied
    exact ⟨leftModel, leftSatisfied,
      fun name member => (agrees name member).symm⟩
  · intro leftModel leftSatisfied
    obtain ⟨rightModel, rightSatisfied, agrees⟩ :=
      equiv.leftToRight leftModel leftSatisfied
    exact ⟨rightModel, rightSatisfied,
      fun name member => (agrees name member).symm⟩

end BindingTheoryEquivAt

private theorem assignment_key_mem_specBindingVars
    {bindings : Bindings} {name : String} {value : Atom}
    (member : (name, value) ∈ bindings.assignments) :
    name ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨(name, value), member, by simp⟩

private theorem assignment_value_var_mem_specBindingVars
    {bindings : Bindings} {name varName : String} {value : Atom}
    (member : (name, value) ∈ bindings.assignments)
    (variableMember : varName ∈ TypeSubst.typeVars value) :
    varName ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨(name, value), member, by simp [variableMember]⟩

private theorem equality_left_mem_specBindingVars
    {bindings : Bindings} {left right : String}
    (member : (left, right) ∈ bindings.equalities) :
    left ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(left, right), member, by simp⟩

private theorem equality_right_mem_specBindingVars
    {bindings : Bindings} {left right : String}
    (member : (left, right) ∈ bindings.equalities) :
    right ∈ specBindingVars bindings := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(left, right), member, by simp⟩

/-- One-way transport of binding satisfaction across agreement on every name
mentioned by the binding record. -/
private theorem specTypeBindingSatisfied_of_agrees
    {left right : String → Atom} {bindings : Bindings}
    (agrees : ValuationsAgreeOn (specBindingVars bindings) left right) :
    TypeBindingSatisfied left bindings →
      TypeBindingSatisfied right bindings := by
  rintro ⟨assignments, equalities⟩
  constructor
  · intro name value member
    calc
      right name = left name :=
        (agrees name
          (assignment_key_mem_specBindingVars member)).symm
      _ = applyTypeValuation left value :=
        assignments name value member
      _ = applyTypeValuation right value := by
        apply applyTypeValuation_congr_of_typeVars
        intro varName variableMember
        exact agrees varName
          (assignment_value_var_mem_specBindingVars
            member variableMember)
  · intro first second member
    calc
      right first = left first :=
        (agrees first
          (equality_left_mem_specBindingVars member)).symm
      _ = left second := equalities first second member
      _ = right second :=
        agrees second (equality_right_mem_specBindingVars member)

/-- Binding satisfaction depends only on the valuation at names mentioned by
the binding record. -/
theorem specTypeBindingSatisfied_congr_of_bindingVars
    {left right : String → Atom} {bindings : Bindings}
    (agrees : ValuationsAgreeOn (specBindingVars bindings) left right) :
    TypeBindingSatisfied left bindings ↔
      TypeBindingSatisfied right bindings := by
  constructor
  · exact specTypeBindingSatisfied_of_agrees agrees
  · exact specTypeBindingSatisfied_of_agrees
      (fun name member => (agrees name member).symm)

namespace BindingTheoryEquivAt

/-- Intermediate private models can be composed without identifying either
record or the witnesses outside the declared observation scope. -/
theorem trans {scope : List String} {first middle last : Bindings}
    (left : BindingTheoryEquivAt scope first middle)
    (right : BindingTheoryEquivAt scope middle last) :
    BindingTheoryEquivAt scope first last := by
  constructor
  · intro firstModel firstSatisfied
    obtain ⟨middleModel, middleSatisfied, firstAgrees⟩ :=
      left.leftToRight firstModel firstSatisfied
    obtain ⟨lastModel, lastSatisfied, lastAgrees⟩ :=
      right.leftToRight middleModel middleSatisfied
    exact ⟨lastModel, lastSatisfied,
      fun name member => (firstAgrees name member).trans (lastAgrees name member)⟩
  · intro lastModel lastSatisfied
    obtain ⟨middleModel, middleSatisfied, lastAgrees⟩ :=
      right.rightToLeft lastModel lastSatisfied
    obtain ⟨firstModel, firstSatisfied, firstAgrees⟩ :=
      left.rightToLeft middleModel middleSatisfied
    exact ⟨firstModel, firstSatisfied,
      fun name member => (firstAgrees name member).trans (lastAgrees name member)⟩

/-- A comparison proved at a larger public scope is valid at each of its
subscopes. Shrinking the scope is explicit, rather than erasing a constraint. -/
theorem restrict {scope smaller : List String} {left right : Bindings}
    (related : BindingTheoryEquivAt scope left right)
    (included : ∀ name ∈ smaller, name ∈ scope) :
    BindingTheoryEquivAt smaller left right := by
  constructor
  · intro model satisfied
    obtain ⟨other, otherSatisfied, agrees⟩ := related.leftToRight model satisfied
    exact ⟨other, otherSatisfied, fun name member => agrees name (included name member)⟩
  · intro model satisfied
    obtain ⟨other, otherSatisfied, agrees⟩ := related.rightToLeft model satisfied
    exact ⟨other, otherSatisfied, fun name member => agrees name (included name member)⟩

/-- Equality of the complete solution theories supplies the same model on
both sides, at any observation scope. -/
theorem of_solution_iff {left right : Bindings}
    (same : ∀ valuation, TypeBindingSatisfied valuation left ↔
      TypeBindingSatisfied valuation right) (scope : List String) :
    BindingTheoryEquivAt scope left right := by
  constructor
  · intro model satisfied
    exact ⟨model, (same model).mp satisfied, fun _ _ => rfl⟩
  · intro model satisfied
    exact ⟨model, (same model).mpr satisfied, fun _ _ => rfl⟩

end BindingTheoryEquivAt

/-- Literal extension adds conjunctions of constraints. Their occurrences
remain in the stored record, even when the model conditions are redundant. -/
theorem bindingSatisfied_append_iff (valuation : String → Atom) (left right : Bindings) :
    TypeBindingSatisfied valuation
      ⟨left.assignments ++ right.assignments, left.equalities ++ right.equalities⟩ ↔
      TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right := by
  constructor
  · rintro ⟨values, equalities⟩
    exact ⟨⟨fun name value member => values name value (List.mem_append_left _ member),
      fun first second member => equalities first second (List.mem_append_left _ member)⟩,
      ⟨fun name value member => values name value (List.mem_append_right _ member),
      fun first second member => equalities first second (List.mem_append_right _ member)⟩⟩
  · rintro ⟨⟨leftValues, leftEqualities⟩, ⟨rightValues, rightEqualities⟩⟩
    exact ⟨fun name value member => (List.mem_append.mp member).elim
      (leftValues name value) (rightValues name value),
      fun first second member => (List.mem_append.mp member).elim
        (leftEqualities first second) (rightEqualities first second)⟩

/-- Scoped comparison composes with constraints whose entire support is in
that scope. Constraints mentioning hidden names require a new boundary proof. -/
theorem BindingTheoryEquivAt.append {scope : List String} {left right : Bindings}
    (related : BindingTheoryEquivAt scope left right) (extension : Bindings)
    (supported : ∀ name ∈ specBindingVars extension, name ∈ scope) :
    BindingTheoryEquivAt scope
      ⟨left.assignments ++ extension.assignments, left.equalities ++ extension.equalities⟩
      ⟨right.assignments ++ extension.assignments, right.equalities ++ extension.equalities⟩ := by
  constructor
  · intro model satisfied
    obtain ⟨baseSatisfied, extensionSatisfied⟩ :=
      (bindingSatisfied_append_iff model left extension).mp satisfied
    obtain ⟨other, otherSatisfied, agrees⟩ := related.leftToRight model baseSatisfied
    refine ⟨other, (bindingSatisfied_append_iff other right extension).mpr
      ⟨otherSatisfied, ?_⟩, agrees⟩
    exact (specTypeBindingSatisfied_congr_of_bindingVars
      (fun name member => agrees name (supported name member))).mp extensionSatisfied
  · intro model satisfied
    obtain ⟨baseSatisfied, extensionSatisfied⟩ :=
      (bindingSatisfied_append_iff model right extension).mp satisfied
    obtain ⟨other, otherSatisfied, agrees⟩ := related.rightToLeft model baseSatisfied
    refine ⟨other, (bindingSatisfied_append_iff other left extension).mpr
      ⟨otherSatisfied, ?_⟩, agrees⟩
    exact (specTypeBindingSatisfied_congr_of_bindingVars
      (fun name member => agrees name (supported name member))).mpr extensionSatisfied

/-- Extending equal complete solution theories by the same constraints keeps
them equal. Freshness is required separately by a rule's hygiene contract. -/
theorem solution_iff_append {left right : Bindings}
    (same : ∀ valuation, TypeBindingSatisfied valuation left ↔
      TypeBindingSatisfied valuation right) (extension : Bindings) (valuation : String → Atom) :
    TypeBindingSatisfied valuation
        ⟨left.assignments ++ extension.assignments, left.equalities ++ extension.equalities⟩ ↔
      TypeBindingSatisfied valuation
        ⟨right.assignments ++ extension.assignments, right.equalities ++ extension.equalities⟩ := by
  rw [bindingSatisfied_append_iff, bindingSatisfied_append_iff, same valuation]

/-- Support of a literal theory extension is the union of both complete
supports; no normalization of relation lists is involved. -/
theorem mem_specBindingVars_append (left right : Bindings) (name : String) :
    name ∈ specBindingVars
        ⟨left.assignments ++ right.assignments, left.equalities ++ right.equalities⟩ ↔
      name ∈ specBindingVars left ∨ name ∈ specBindingVars right := by
  simp only [specBindingVars, List.flatMap_append, List.mem_append]
  tauto

/-- Reusing the same fresh theory preserves equality of the hygiene support
when two caller representations already have the same complete support. -/
theorem support_iff_append {left right : Bindings}
    (same : ∀ name, name ∈ specBindingVars left ↔ name ∈ specBindingVars right)
    (extension : Bindings) (name : String) :
    name ∈ specBindingVars
        ⟨left.assignments ++ extension.assignments, left.equalities ++ extension.equalities⟩ ↔
      name ∈ specBindingVars
        ⟨right.assignments ++ extension.assignments, right.equalities ++ extension.equalities⟩ := by
  rw [mem_specBindingVars_append, mem_specBindingVars_append, same name]

/-- Reordering a concrete binding record preserves the complete name support
used by hygienic freshening, including variables inside assignment values. -/
theorem BindingRecordPerm.support_iff {left right : Bindings}
    (related : BindingRecordPerm left right) (name : String) :
    name ∈ specBindingVars left ↔ name ∈ specBindingVars right := by
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (⟨entry, member, occurs⟩ | ⟨edge, member, occurs⟩)
    · exact Or.inl ⟨entry, related.assignments.mem_iff.mp member, occurs⟩
    · exact Or.inr ⟨edge, related.equalities.mem_iff.mp member, occurs⟩
  · rintro (⟨entry, member, occurs⟩ | ⟨edge, member, occurs⟩)
    · exact Or.inl ⟨entry, related.assignments.mem_iff.mpr member, occurs⟩
    · exact Or.inr ⟨edge, related.equalities.mem_iff.mpr member, occurs⟩


/-- The extension through a private presentation preserves any incoming
binding theory whose mentioned names avoid the presentation keys. -/
theorem extendThroughPresentation_preserves_binding
    {base : String → Atom} {substitution : TypeSubst}
    {bindings : Bindings}
    (fresh : ∀ name, name ∈ specBindingVars bindings →
      name ∉ substitution.keys)
    (satisfied : TypeBindingSatisfied base bindings) :
    TypeBindingSatisfied
      (extendThroughPresentation base substitution) bindings := by
  exact (specTypeBindingSatisfied_congr_of_bindingVars
    (left := base)
    (right := extendThroughPresentation base substitution)
    (fun name member =>
      (extendThroughPresentation_eq_of_not_mem_keys
        (fresh name member)).symm)).mp satisfied

/-- Exact solution-theory conjunction of an incoming spec binding record
with one finite type presentation.  This relation deliberately carries no
freshness or observation claim: a presentation may bind a caller-visible
variable, as the published applicability relation permits. -/
def PresentationExtensionRel
    (incoming : Bindings) (substitution : TypeSubst)
    (output : Bindings) : Prop :=
  ∀ valuation,
    TypeBindingSatisfied valuation output ↔
      TypeBindingSatisfied valuation incoming ∧
        TypeSubstSatisfied valuation substitution

/-- The complete semantic boundary for adjoining one private finite type
presentation to an evaluator binding state.  The output carrier is left
abstract: consumers may use any binding representation with the stated
solution theory, but must prove both freshness obligations and normality.

Keeping these four facts in one witness prevents a candidate scan from
mixing the presentation produced by one applicability check with the binding
output of another. -/
structure PrivatePresentationExtensionRel
    (scope : List String) (incoming : Bindings)
    (substitution : TypeSubst) (output : Bindings) : Prop where
  normal : substitution.Normal
  scopeFresh : ∀ name, name ∈ scope →
    name ∉ substitution.keys
  bindingFresh : ∀ name, name ∈ specBindingVars incoming →
    name ∉ substitution.keys
  solutions : ∀ valuation,
    TypeBindingSatisfied valuation output ↔
      TypeBindingSatisfied valuation incoming ∧
        TypeSubstSatisfied valuation substitution

/-- **Private-theory observation theorem.**  If `output` denotes exactly the
incoming binding theory conjoined with a normal private presentation, and the
private keys avoid both the incoming theory and the observation scope, then
`incoming` and `output` have identical observations on that scope. -/
theorem privatePresentation_observationally_inert
    {scope : List String} {incoming output : Bindings}
    {substitution : TypeSubst}
    (normal : substitution.Normal)
    (scopeFresh : ∀ name, name ∈ scope →
      name ∉ substitution.keys)
    (bindingFresh : ∀ name, name ∈ specBindingVars incoming →
      name ∉ substitution.keys)
    (solutions : ∀ valuation,
      TypeBindingSatisfied valuation output ↔
        TypeBindingSatisfied valuation incoming ∧
          TypeSubstSatisfied valuation substitution) :
    BindingTheoryEquivAt scope incoming output := by
  constructor
  · intro incomingModel incomingSatisfied
    let outputModel :=
      extendThroughPresentation incomingModel substitution
    have outputIncoming :
        TypeBindingSatisfied outputModel incoming :=
      extendThroughPresentation_preserves_binding
        bindingFresh incomingSatisfied
    have outputPrivate : TypeSubstSatisfied outputModel substitution :=
      extendThroughPresentation_satisfied normal incomingModel
    refine ⟨outputModel,
      (solutions outputModel).mpr ⟨outputIncoming, outputPrivate⟩, ?_⟩
    intro name member
    exact (extendThroughPresentation_eq_of_not_mem_keys
      (scopeFresh name member)).symm
  · intro outputModel outputSatisfied
    refine ⟨outputModel, (solutions outputModel).mp outputSatisfied |>.1,
      fun _ _ => rfl⟩

/-- A private-presentation extension is observationally inert at precisely
the scope named by its witness. -/
theorem PrivatePresentationExtensionRel.observationallyInert
    {scope : List String} {incoming output : Bindings}
    {substitution : TypeSubst}
    (extension : PrivatePresentationExtensionRel
      scope incoming substitution output) :
    BindingTheoryEquivAt scope incoming output := by
  exact privatePresentation_observationally_inert
    extension.normal extension.scopeFresh extension.bindingFresh
    extension.solutions

/-- Forgetting privacy from a private extension retains its exact
solution-theory conjunction. -/
theorem PrivatePresentationExtensionRel.toPresentationExtension
    {scope : List String} {incoming output : Bindings}
    {substitution : TypeSubst}
    (extension : PrivatePresentationExtensionRel
      scope incoming substitution output) :
    PresentationExtensionRel incoming substitution output :=
  extension.solutions

/-! ## Boundary canaries -/

private def privateT : TypeSubst := [("type#t", .symbol "A")]

private def publicX : Bindings :=
  ⟨[("x", .symbol "B")], []⟩

/-- Conjoining a finite assignment presentation with an existing spec
binding record denotes conjunction of their two equation theories. -/
theorem appendPrivatePresentation_solutions
    (valuation : String → Atom) (bindings : Bindings)
    (substitution : TypeSubst) :
    TypeBindingSatisfied valuation
        ⟨bindings.assignments ++ substitution, bindings.equalities⟩ ↔
      TypeBindingSatisfied valuation bindings ∧
        TypeSubstSatisfied valuation substitution := by
  constructor
  · rintro ⟨assignments, equalities⟩
    constructor
    · exact ⟨fun name value member =>
          assignments name value (List.mem_append_left _ member),
        equalities⟩
    · intro name value member
      exact assignments name value (List.mem_append_right _ member)
  · rintro ⟨⟨assignments, equalities⟩, privateAssignments⟩
    constructor
    · intro name value member
      rcases List.mem_append.mp member with oldMember | privateMember
      · exact assignments name value oldMember
      · exact privateAssignments name value privateMember
    · exact equalities

/-- Appending the presentation assignments to the incoming assignment list
is a concrete carrier for their exact solution-theory conjunction. -/
theorem presentationExtension_append
    (bindings : Bindings) (substitution : TypeSubst) :
    PresentationExtensionRel bindings substitution
      ⟨bindings.assignments ++ substitution, bindings.equalities⟩ :=
  fun valuation =>
    appendPrivatePresentation_solutions valuation bindings substitution

/-- Any normal presentation avoiding the complete public/caller boundary can
be adjoined to the caller binding theory.  This is the general construction
used after branch-valued applicability: it depends only on the selected
presentation's invariants, not on a particular linear scan that produced it. -/
theorem privatePresentationExtension_of_normal_avoids
    {scope : List String} {incoming : Bindings}
    {substitution : TypeSubst}
    (normal : substitution.Normal)
    (avoids : substitution.Avoids
      (scope ++ specBindingVars incoming)) :
    PrivatePresentationExtensionRel scope incoming substitution
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  refine
    { normal := normal
      scopeFresh := ?_
      bindingFresh := ?_
      solutions := fun valuation =>
        appendPrivatePresentation_solutions valuation incoming substitution }
  · intro name scopeMember keyMember
    exact avoids.keys name keyMember
      (List.mem_append_left _ scopeMember)
  · intro name bindingMember keyMember
    exact avoids.keys name keyMember
      (List.mem_append_right _ bindingMember)

/-- An empty-seed presentation fold over alpha-fresh types localizes over an
arbitrary caller binding theory.  The output is the caller theory conjoined
with the private finite presentation; freshness makes that conjunction
satisfiable and observationally inert at the public scope.

This theorem is deliberately freshness-conditioned.  Without that condition
an incoming assignment may instantiate a type variable differently from the
empty-seed fold, so the corresponding seeded match need not succeed. -/
theorem PresentationArgumentListMatchRel.privateExtension
    {scope : List String} {incoming : Bindings}
    {expected actual : List Atom} {substitution : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual [] substitution)
    (expectedFresh : AtomsAvoid expected
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid actual
      (scope ++ specBindingVars incoming)) :
    PrivatePresentationExtensionRel scope incoming substitution
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  have outputNormal : substitution.Normal :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      derivation TypeSubst.normal_empty
  have outputAvoids : substitution.Avoids
      (scope ++ specBindingVars incoming) :=
    presentationArgumentList_output_avoids derivation
      (TypeSubst.avoids_empty _) expectedFresh actualFresh
  constructor
  · exact outputNormal
  · intro name scopeMember keyMember
    exact outputAvoids.keys name keyMember
      (List.mem_append_left _ scopeMember)
  · intro name bindingMember keyMember
    exact outputAvoids.keys name keyMember
      (List.mem_append_right _ bindingMember)
  · intro valuation
    exact appendPrivatePresentation_solutions
      valuation incoming substitution

/-- The localization theorem immediately yields the evaluator-visible
observation boundary consumed by runtime correspondence. -/
theorem PresentationArgumentListMatchRel.scopedInert
    {scope : List String} {incoming : Bindings}
    {expected actual : List Atom} {substitution : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual [] substitution)
    (expectedFresh : AtomsAvoid expected
      (scope ++ specBindingVars incoming))
    (actualFresh : AtomsAvoid actual
      (scope ++ specBindingVars incoming)) :
    BindingTheoryEquivAt scope incoming
      ⟨incoming.assignments ++ substitution, incoming.equalities⟩ := by
  exact
    (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.PresentationArgumentListMatchRel.privateExtension
      derivation expectedFresh actualFresh).observationallyInert

/-- Positive: a private type equation can be conjoined without changing the
public `x` observation. -/
theorem private_type_binding_is_inert_at_public_x :
    BindingTheoryEquivAt ["x"] publicX
      ⟨publicX.assignments ++ privateT, []⟩ := by
  apply privatePresentation_observationally_inert
      (substitution := privateT)
  · simp [privateT, TypeSubst.Normal, TypeSubst.keys,
      TypeSubst.typeVars]
  · simp [privateT, TypeSubst.keys]
  · intro name member
    simp [specBindingVars, publicX, TypeSubst.typeVars] at member
    subst name
    simp [privateT, TypeSubst.keys]
  · intro valuation
    exact appendPrivatePresentation_solutions valuation publicX privateT

/-- Negative: freshness is essential.  Constraining the observed `x` to `A`
is not observationally inert at `x`. -/
theorem observed_private_key_is_not_inert :
    ¬BindingTheoryEquivAt ["x"] Bindings.empty
      ⟨[("x", .symbol "A")], []⟩ := by
  intro equiv
  let publicModel : String → Atom :=
    fun name => if name = "x" then .symbol "B" else .var name
  have emptySatisfied :
      TypeBindingSatisfied publicModel Bindings.empty := by
    simp [TypeBindingSatisfied, Bindings.empty]
  obtain ⟨privateModel, privateSatisfied, agrees⟩ :=
    equiv.leftToRight publicModel emptySatisfied
  have forced := privateSatisfied.1 "x" (.symbol "A") (by simp)
  have publicXValue : publicModel "x" = .symbol "B" := by
    simp [publicModel]
  have sameX := agrees "x" (by simp)
  simp [applyTypeValuation] at forced
  rw [← sameX, publicXValue] at forced
  contradiction

namespace Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement

def redundantEdge : Bindings := ⟨[], [("private", "private")]⟩

/-- A tautological equality changes the hygiene support but not a single
model. Solution equivalence alone therefore cannot license the freshener. -/
theorem same_solutions_different_support :
    (∀ valuation, TypeBindingSatisfied valuation Bindings.empty ↔
      TypeBindingSatisfied valuation redundantEdge) ∧
    ("private" ∉ specBindingVars Bindings.empty ∧
      "private" ∈ specBindingVars redundantEdge) := by
  constructor
  · intro valuation
    simp [TypeBindingSatisfied, Bindings.empty, redundantEdge]
  · decide

def privateValue : Bindings := ⟨[("private", .symbol "A")], []⟩

theorem empty_scope_comparison :
    BindingTheoryEquivAt [] Bindings.empty privateValue := by
  constructor
  · intro model satisfied
    exact ⟨fun _ => .symbol "A", by simp [TypeBindingSatisfied, privateValue,
      applyTypeValuation], by intro name member; cases member⟩
  · intro model satisfied
    exact ⟨model, by simp [TypeBindingSatisfied, Bindings.empty],
      by intro name member; cases member⟩

/-- An empty public scope does not make the two complete theories equal. -/
theorem local_scope_is_not_full_theory :
    ¬(∀ valuation, TypeBindingSatisfied valuation Bindings.empty ↔
      TypeBindingSatisfied valuation privateValue) := by
  intro same
  have bound := (same (fun name => .var name)).mp
    (by simp [TypeBindingSatisfied, Bindings.empty])
  have impossible := bound.1 "private" (.symbol "A") (by simp [privateValue])
  simp only [applyTypeValuation] at impossible
  cases impossible

def conflictingPrivateValue : Bindings := ⟨[("private", .symbol "B")], []⟩

/-- Adding a constraint on an unobserved name can destroy a previously valid
scoped comparison. The new supported-extension hypothesis is necessary. -/
theorem hidden_extension_breaks_comparison :
    ¬BindingTheoryEquivAt [] conflictingPrivateValue
      ⟨privateValue.assignments ++ conflictingPrivateValue.assignments,
        privateValue.equalities ++ conflictingPrivateValue.equalities⟩ := by
  intro related
  have leftSatisfied : TypeBindingSatisfied (fun _ => .symbol "B") conflictingPrivateValue := by
    simp [TypeBindingSatisfied, conflictingPrivateValue, applyTypeValuation]
  obtain ⟨model, satisfied, _⟩ := related.leftToRight _ leftSatisfied
  obtain ⟨left, right⟩ :=
    (bindingSatisfied_append_iff model privateValue conflictingPrivateValue).mp satisfied
  have first := left.1 "private" (.symbol "A") (by simp [privateValue])
  have second := right.1 "private" (.symbol "B") (by simp [conflictingPrivateValue])
  have impossible : (Atom.symbol "A") = .symbol "B" := by
    simpa only [applyTypeValuation] using first.symm.trans second
  have different : ("A" : String) ≠ "B" := by decide
  exact different (Atom.symbol.inj impossible)

theorem public_extension_composes :
    BindingTheoryEquivAt ["private"] privateValue
      ⟨redundantEdge.assignments ++ privateValue.assignments,
        redundantEdge.equalities ++ privateValue.equalities⟩ := by
  have related := BindingTheoryEquivAt.of_solution_iff
    same_solutions_different_support.1 ["private"]
  simpa only [Bindings.empty, List.nil_append] using related.append privateValue
    (by intro name member; simpa [privateValue, specBindingVars,
      Spec.Type.Presentation.TypeSubst.typeVars] using member)

end Controls

end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

/-! ## Simultaneous binding and matcher renaming -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation
open Spec.Type.Presentation.ScopeObservation

/-- Rename complete binding rows, retaining order, multiplicity and equality
orientation. The same action reaches every variable in a stored value. -/
def renameBindings (rename : String → String) (bindings : Bindings) : Bindings :=
  ⟨bindings.assignments.map (fun entry => (rename entry.1, renameTypeVars rename entry.2)),
    bindings.equalities.map (fun edge => (rename edge.1, rename edge.2))⟩

@[simp] theorem renameBindings_empty (rename : String → String) :
    renameBindings rename Bindings.empty = Bindings.empty := rfl

@[simp] theorem renameBindings_id (bindings : Bindings) :
    renameBindings id bindings = bindings := by
  cases bindings
  simp [renameBindings, renameTypeVars_id]

theorem renameBindings_comp (outer inner : String → String) (bindings : Bindings) :
    renameBindings outer (renameBindings inner bindings) =
      renameBindings (outer ∘ inner) bindings := by
  cases bindings
  simp [renameBindings, List.map_map, Function.comp_def, renameTypeVars_comp]

@[simp] theorem renameBindings_perm_inverse (permutation : Equiv.Perm String)
    (bindings : Bindings) :
    renameBindings permutation.symm (renameBindings permutation bindings) = bindings := by
  rw [renameBindings_comp]
  have inverse : (permutation.symm : String → String) ∘ permutation = id := by
    funext name
    simp
  rw [inverse, renameBindings_id]

theorem renameBindings_perm_injective (permutation : Equiv.Perm String) :
    Function.Injective (renameBindings permutation) := by
  intro left right same
  simpa only [renameBindings_perm_inverse] using
    congrArg (renameBindings permutation.symm) same

theorem renameBindings_typeBindingSatisfied (rename : String → String)
    (bindings : Bindings) (valuation : String → Atom) :
    TypeBindingSatisfied valuation (renameBindings rename bindings) ↔
      TypeBindingSatisfied (valuation ∘ rename) bindings := by
  constructor
  · intro satisfied
    constructor
    · intro name value member
      have renamed := satisfied.1 (rename name) (renameTypeVars rename value)
        (List.mem_map.mpr ⟨(name,value), member, rfl⟩)
      simpa only [ApplicationEquivariance.applyTypeValuation_renameTypeVars,
        Function.comp_apply] using renamed
    · intro left right member
      exact satisfied.2 (rename left) (rename right)
        (List.mem_map.mpr ⟨(left,right), member, rfl⟩)
  · intro satisfied
    constructor
    · intro name value member
      change (name, value) ∈ bindings.assignments.map
        (fun entry => (rename entry.1, renameTypeVars rename entry.2)) at member
      obtain ⟨⟨key, stored⟩, original, same⟩ := List.mem_map.mp member
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      simpa only [ApplicationEquivariance.applyTypeValuation_renameTypeVars,
        Function.comp_apply] using satisfied.1 key stored original
    · intro left right member
      change (left, right) ∈ bindings.equalities.map
        (fun edge => (rename edge.1, rename edge.2)) at member
      obtain ⟨⟨first, second⟩, original, same⟩ := List.mem_map.mp member
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact satisfied.2 first second original

end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement

@[simp] theorem names_contains_permutation (permutation : Equiv.Perm String)
    (names : List String) (name : String) :
    (names.map permutation).contains (permutation name) = names.contains name := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  simp only [List.mem_map, permutation.injective.eq_iff, exists_eq_right]

theorem renameBindings_lookup (permutation : Equiv.Perm String)
    (bindings : Bindings) (name : String) :
    (renameBindings permutation bindings).lookup (permutation name) =
      (bindings.lookup name).map (renameTypeVars permutation) := by
  cases bindings with
  | mk assignments equalities =>
      simp only [renameBindings, Bindings.lookup]
      induction assignments with
      | nil => rfl
      | cons entry rest ih =>
          obtain ⟨key, value⟩ := entry
          have same : (permutation name == permutation key) = (name == key) := by
            rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
            exact permutation.injective.eq_iff
          simp only [List.map_cons, List.lookup_cons, same]
          split <;> simp_all

theorem renameBindings_isBound (permutation : Equiv.Perm String)
    (bindings : Bindings) (name : String) :
    (renameBindings permutation bindings).isBound (permutation name) =
      bindings.isBound name := by
  simp [Bindings.isBound, renameBindings_lookup]

theorem renameBindings_addEquality (rename : String → String)
    (bindings : Bindings) (left right : String) :
    renameBindings rename (bindings.addEquality left right) =
      (renameBindings rename bindings).addEquality (rename left) (rename right) := by
  cases bindings
  simp [renameBindings, Bindings.addEquality, List.map_append]

theorem renameBindings_assign (permutation : Equiv.Perm String)
    (bindings : Bindings) (name : String) (value : Atom) :
    renameBindings permutation (bindings.assign name value) =
      (renameBindings permutation bindings).assign
        (permutation name) (renameTypeVars permutation value) := by
  simp only [Bindings.assign, renameBindings_isBound]
  split
  · cases bindings with
    | mk assignments equalities =>
      apply congrArg (fun rows : List (String × Atom) => Bindings.mk rows
        (equalities.map (fun edge => (permutation edge.1, permutation edge.2))))
      simp only [renameBindings, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro entry _
      obtain ⟨key, stored⟩ := entry
      have same : (permutation key == permutation name) = (key == name) := by
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        exact permutation.injective.eq_iff
      simp only [same]
      split <;> rfl
  · cases bindings
    simp [renameBindings, List.map_append]

private theorem eqStep_one_rename (permutation : Equiv.Perm String)
    (names : List String) (left right : String) :
    (let names := if (names.map permutation).contains (permutation left) &&
          !(names.map permutation).contains (permutation right) then
          names.map permutation ++ [permutation right] else names.map permutation
      if names.contains (permutation right) && !names.contains (permutation left) then
        names ++ [permutation left] else names) =
    (let names := if names.contains left && !names.contains right then
          names ++ [right] else names
      if names.contains right && !names.contains left then names ++ [left] else names).map
        permutation := by
  by_cases leftMember : left ∈ names <;>
    by_cases rightMember : right ∈ names <;>
    by_cases same : right = left <;>
    simp_all [List.mem_map, permutation.injective.eq_iff]

theorem eqStep_rename (permutation : Equiv.Perm String)
    (edges : List (String × String)) (names : List String) :
    Bindings.eqStep (edges.map (fun edge => (permutation edge.1, permutation edge.2)))
        (names.map permutation) = (Bindings.eqStep edges names).map permutation := by
  induction edges generalizing names with
  | nil => rfl
  | cons edge rest ih =>
      obtain ⟨left, right⟩ := edge
      simp only [Bindings.eqStep, List.map_cons, List.foldl_cons]
      rw [eqStep_one_rename]
      exact ih _

theorem eqClassAux_rename (permutation : Equiv.Perm String)
    (edges : List (String × String)) (fuel : Nat) (names : List String) :
    Bindings.eqClassAux (edges.map (fun edge => (permutation edge.1, permutation edge.2)))
        fuel (names.map permutation) = (Bindings.eqClassAux edges fuel names).map permutation := by
  induction fuel generalizing names with
  | zero => rfl
  | succ fuel ih =>
      simp only [Bindings.eqClassAux, eqStep_rename]
      exact ih _

theorem renameBindings_eqClass (permutation : Equiv.Perm String)
    (bindings : Bindings) (name : String) :
    (renameBindings permutation bindings).eqClass (permutation name) =
      (bindings.eqClass name).map permutation := by
  simp only [Bindings.eqClass, renameBindings, List.length_map]
  exact eqClassAux_rename permutation _ _ [name]

private theorem eqOrder_one_rename (permutation : Equiv.Perm String)
    (names : List String) (left right : String) :
    (let names := if (names.map permutation).contains (permutation left) then
          names.map permutation else names.map permutation ++ [permutation left]
      if names.contains (permutation right) then names else names ++ [permutation right]) =
    (let names := if names.contains left then names else names ++ [left]
      if names.contains right then names else names ++ [right]).map permutation := by
  by_cases leftMember : left ∈ names <;>
    by_cases rightMember : right ∈ names <;>
    by_cases same : right = left <;>
    simp_all [List.mem_map, permutation.injective.eq_iff]

theorem renameBindings_eqVarsInOrder (permutation : Equiv.Perm String)
    (bindings : Bindings) :
    (renameBindings permutation bindings).eqVarsInOrder =
      bindings.eqVarsInOrder.map permutation := by
  have general (edges : List (String × String)) (names : List String) :
      (edges.map (fun edge => (permutation edge.1, permutation edge.2))).foldl
          (fun names edge =>
            let names := if names.contains edge.1 then names else names ++ [edge.1]
            if names.contains edge.2 then names else names ++ [edge.2])
          (names.map permutation) =
      (edges.foldl (fun names edge =>
            let names := if names.contains edge.1 then names else names ++ [edge.1]
            if names.contains edge.2 then names else names ++ [edge.2]) names).map
          permutation := by
    induction edges generalizing names with
    | nil => rfl
    | cons edge rest ih =>
        obtain ⟨left, right⟩ := edge
        simp only [List.map_cons, List.foldl_cons]
        rw [eqOrder_one_rename]
        exact ih _
  exact general bindings.equalities []

theorem renameBindings_eqClassOrdered (permutation : Equiv.Perm String)
    (bindings : Bindings) (name : String) :
    (renameBindings permutation bindings).eqClassOrdered (permutation name) =
      (bindings.eqClassOrdered name).map permutation := by
  simp only [Bindings.eqClassOrdered, renameBindings_eqVarsInOrder,
    renameBindings_eqClass]
  have filtered :
      (bindings.eqVarsInOrder.map permutation).filter
          (fun other => ((bindings.eqClass name).map permutation).contains other) =
        (bindings.eqVarsInOrder.filter (fun other => (bindings.eqClass name).contains other)).map
          permutation := by
    induction bindings.eqVarsInOrder with
    | nil => rfl
    | cons head rest ih =>
        simp only [List.map_cons, List.filter_cons, names_contains_permutation]
        split <;> simp_all
  rw [filtered]
  cases bindings.eqVarsInOrder.filter (fun other => (bindings.eqClass name).contains other) <;> rfl

theorem renameBindings_classValues (permutation : Equiv.Perm String)
    (bindings : Bindings) (name : String) :
    (renameBindings permutation bindings).classValues (permutation name) =
      (bindings.classValues name).map (renameTypeVars permutation) := by
  simp only [Bindings.classValues, renameBindings_eqClassOrdered]
  induction bindings.eqClassOrdered name with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.map_cons, List.filterMap_cons, renameBindings_lookup]
      cases bindings.lookup head <;> simp_all

end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

namespace Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

def Constraint.rename (rename : String → String) : Constraint → Constraint
  | .value name atom => .value (rename name) (renameTypeVars rename atom)
  | .equality left right => .equality (rename left) (rename right)

@[simp] theorem Constraint.rename_inverse (permutation : Equiv.Perm String)
    (constraint : Constraint) :
    Constraint.rename permutation.symm (Constraint.rename permutation constraint) = constraint := by
  cases constraint <;> simp [Constraint.rename]

theorem Constraint.rename_injective (permutation : Equiv.Perm String) :
    Function.Injective (Constraint.rename permutation) :=
  Function.LeftInverse.injective (Constraint.rename_inverse permutation)

private theorem eraseDups_map_injective {α β : Type*}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (rename : α → β) (injective : Function.Injective rename) (values : List α) :
    (values.map rename).eraseDups = values.eraseDups.map rename := by
  cases values with
  | nil => rfl
  | cons first rest =>
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons, List.map_cons]
      have filtered :
          (rest.map rename).filter (fun value => !(value == rename first)) =
            (rest.filter (fun value => !(value == first))).map rename := by
        rw [List.filter_map]
        congr 2
        funext value
        apply congrArg Bool.not
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        exact injective.eq_iff
      rw [filtered, eraseDups_map_injective rename injective]
termination_by values.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem constraints_renameBindings (permutation : Equiv.Perm String)
    (bindings : Bindings) :
    constraints (renameBindings permutation bindings) =
      (constraints bindings).map (Constraint.rename permutation) := by
  unfold constraints
  have raw :
      (renameBindings permutation bindings).assignments.map
          (fun entry => Constraint.value entry.1 entry.2) ++
        (renameBindings permutation bindings).equalities.map
          (fun entry => Constraint.equality entry.1 entry.2) =
      (bindings.assignments.map (fun entry => Constraint.value entry.1 entry.2) ++
        bindings.equalities.map (fun entry => Constraint.equality entry.1 entry.2)).map
          (Constraint.rename permutation) := by
    simp [renameBindings, List.map_append, List.map_map, Function.comp_def, Constraint.rename]
  rw [raw, eraseDups_map_injective _ (Constraint.rename_injective permutation)]

/-- Opaque custom matchers and the admissibility boundary are reindexed
explicitly. No unchanged foreign service is presumed equivariant. -/
def Parameters.rename (permutation : Equiv.Perm String) (parameters : Parameters) : Parameters where
  hasCustomMatcher := parameters.hasCustomMatcher
  customMatch := fun grounded atom output => parameters.customMatch grounded
    (renameTypeVars permutation.symm atom) (renameBindings permutation.symm output)
  admissible := fun output => parameters.admissible (renameBindings permutation.symm output)

@[simp] theorem Parameters.rename_admissible (permutation : Equiv.Perm String)
    (parameters : Parameters) (bindings : Bindings) :
    (parameters.rename permutation).admissible (renameBindings permutation bindings) ↔
      parameters.admissible bindings := by simp [Parameters.rename]

@[simp] theorem Parameters.rename_customMatch (permutation : Equiv.Perm String)
    (parameters : Parameters) (grounded : OSLFCore.GroundedValue) (atom : Atom)
    (bindings : Bindings) :
    (parameters.rename permutation).customMatch grounded (renameTypeVars permutation atom)
        (renameBindings permutation bindings) ↔ parameters.customMatch grounded atom bindings := by
  simp [Parameters.rename]

@[simp] theorem isVariableB_rename (rename : String → String) (atom : Atom) :
    isVariableB (renameTypeVars rename atom) = isVariableB atom := by
  cases atom <;> simp [renameTypeVars, isVariableB]

@[simp] theorem Parameters.rename_atomHasCustomMatcher (permutation : Equiv.Perm String)
    (parameters : Parameters) (atom : Atom) :
    (parameters.rename permutation).atomHasCustomMatcher (renameTypeVars permutation atom) ↔
      parameters.atomHasCustomMatcher atom := by
  cases atom <;> simp [renameTypeVars, Parameters.atomHasCustomMatcher, Parameters.rename]

theorem ValuesAgree.rename (permutation : Equiv.Perm String) (values : List Atom) :
    ValuesAgree (values.map (renameTypeVars permutation)) ↔ ValuesAgree values := by
  cases values with
  | nil => rfl
  | cons first rest =>
      simp only [List.map_cons, ValuesAgree, List.mem_map, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, (renameTypeVars_perm_injective permutation).eq_iff]

theorem AtomOccurs.rename (permutation : Equiv.Perm String) {atom : Atom} {name : String}
    (occurs : AtomOccurs atom name) :
    AtomOccurs (renameTypeVars permutation atom) (permutation name) := by
  induction occurs with
  | var name => simpa only [renameTypeVars] using AtomOccurs.var (permutation name)
  | expression member _ ih =>
      simpa only [renameTypeVars] using
        AtomOccurs.expression (List.mem_map.mpr ⟨_, member, rfl⟩) ih

theorem AtomOccurs.rename_iff (permutation : Equiv.Perm String) (atom : Atom) (name : String) :
    AtomOccurs (renameTypeVars permutation atom) (permutation name) ↔ AtomOccurs atom name := by
  constructor
  · intro occurs
    simpa only [renameTypeVars_perm_inverse, Equiv.symm_apply_apply] using
      occurs.rename permutation.symm
  · exact fun occurs => occurs.rename permutation

theorem ClassDepends.rename (permutation : Equiv.Perm String) {bindings : Bindings}
    {source target : String} (dependency : ClassDepends bindings source target) :
    ClassDepends (renameBindings permutation bindings) (permutation source) (permutation target) := by
  obtain ⟨key, value, name, stored, sourceMember, occurs, targetMember, proper⟩ := dependency
  refine ⟨permutation key, renameTypeVars permutation value, permutation name,
    List.mem_map.mpr ⟨(key, value), stored, rfl⟩, ?_, occurs.rename permutation, ?_, ?_⟩
  · rw [renameBindings_eqClass]
    exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩
  · rw [renameBindings_eqClass]
    exact List.mem_map.mpr ⟨target, targetMember, rfl⟩
  · rintro ⟨same, different, classMember⟩
    apply proper
    refine ⟨?_, fun equality => different (congrArg permutation equality), ?_⟩
    · apply renameTypeVars_perm_injective permutation
      simpa only [renameTypeVars] using same
    · simpa only [renameBindings_eqClass, List.mem_map,
        permutation.injective.eq_iff, exists_eq_right] using classMember

theorem ClassDepends.rename_iff (permutation : Equiv.Perm String)
    (bindings : Bindings) (source target : String) :
    ClassDepends (renameBindings permutation bindings) (permutation source) (permutation target) ↔
      ClassDepends bindings source target := by
  constructor
  · intro dependency
    simpa only [renameBindings_perm_inverse, Equiv.symm_apply_apply] using
      dependency.rename permutation.symm
  · exact fun dependency => dependency.rename permutation

theorem SemanticLoopFree.rename (permutation : Equiv.Perm String)
    {bindings : Bindings} (free : SemanticLoopFree bindings) :
    SemanticLoopFree (renameBindings permutation bindings) := by
  intro name cycle
  have original := cycle.lift permutation.symm
    (fun _ _ edge => ClassDepends.rename permutation.symm edge)
  simp only [renameBindings_perm_inverse] at original
  exact free (permutation.symm name) original

theorem SemanticLoopFree.rename_iff (permutation : Equiv.Perm String) (bindings : Bindings) :
    SemanticLoopFree (renameBindings permutation bindings) ↔ SemanticLoopFree bindings := by
  constructor
  · intro free
    simpa only [renameBindings_perm_inverse] using free.rename permutation.symm
  · exact fun free => free.rename permutation

end Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.RenamingControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation

private def distinctValues : TypeSubst := [("x", .symbol "A"), ("y", .symbol "B")]

/-- One permutation preserves every use of the repeated variable. -/
theorem swapped_repeated_readout :
    (distinctValues.renameVars (Equiv.swap "x" "y")).apply
        (renameTypeVars (Equiv.swap "x" "y")
          (.expression [.var "x", .var "y", .var "x"])) =
      .expression [.symbol "A", .symbol "B", .symbol "A"] := by
  simp [distinctValues, TypeSubst.renameVars, TypeSubst.apply, TypeSubst.lookup,
    renameTypeVars, Equiv.swap_apply_def]

/-- A noninjective name map can change first-hit substitution lookup. -/
theorem collapsing_names_changes_readout :
    (distinctValues.renameVars (fun _ => "z")).apply (.var "z") ≠
      renameTypeVars (fun _ => "z") (distinctValues.apply (.var "y")) := by
  simp [distinctValues, TypeSubst.renameVars, TypeSubst.apply, TypeSubst.lookup, renameTypeVars]

private def redundantAlias : Bindings :=
  ⟨[("x", .var "y")], [("x", "y")]⟩

theorem redundant_alias_is_acyclic :
    Spec.Match.Merge.SemanticLoopFree redundantAlias := by
  have noEdge : ∀ source target,
      ¬Spec.Match.Merge.ClassDepends redundantAlias source target := by
    intro source target dependency
    obtain ⟨key, atom, name, stored, _sourceMember, occurs, _targetMember, proper⟩ := dependency
    have storedShape : key = "x" ∧ atom = .var "y" := by
      simpa only [redundantAlias, List.mem_singleton, Prod.mk.injEq] using stored
    obtain ⟨rfl, rfl⟩ := storedShape
    cases occurs
    apply proper
    refine ⟨rfl, by decide, ?_⟩
    simp [redundantAlias, Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep]
  intro name cycle
  cases cycle with
  | single edge => exact noEdge _ _ edge
  | tail _ edge => exact noEdge _ _ edge

/-- Collapsing an alias onto itself creates a genuine self-assignment cycle. -/
theorem collapsing_names_creates_cycle :
    ¬Spec.Match.Merge.SemanticLoopFree (renameBindings (fun _ => "z") redundantAlias) := by
  intro free
  apply free "z"
  apply Relation.TransGen.single
  refine ⟨"z", .var "z", "z", ?_, ?_, .var "z", ?_, ?_⟩
  · simp [renameBindings, redundantAlias, renameTypeVars]
  · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
  · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
  · simp

end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.RenamingControls

namespace Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

private abbrev MatchMotive (p : Parameters) (ρ : Equiv.Perm String)
    (left right : Atom) (out : Bindings) (_ : MatchRel p left right out) : Prop :=
  MatchRel (p.rename ρ) (renameTypeVars ρ left) (renameTypeVars ρ right) (renameBindings ρ out)

private abbrev ListMotive (p : Parameters) (ρ : Equiv.Perm String)
    (left right : List Atom) (seed out : Bindings) (_ : MatchListAccRel p left right seed out) : Prop :=
  MatchListAccRel (p.rename ρ) (left.map (renameTypeVars ρ)) (right.map (renameTypeVars ρ))
    (renameBindings ρ seed) (renameBindings ρ out)

private abbrev BindingMotive (p : Parameters) (ρ : Equiv.Perm String)
    (seed : Bindings) (name : String) (atom : Atom) (out : Bindings)
    (_ : AddVarBindingRel p seed name atom out) : Prop :=
  AddVarBindingRel (p.rename ρ) (renameBindings ρ seed) (ρ name) (renameTypeVars ρ atom)
    (renameBindings ρ out)

private abbrev EqualityMotive (p : Parameters) (ρ : Equiv.Perm String)
    (seed : Bindings) (left right : String) (out : Bindings)
    (_ : AddVarEqualityRel p seed left right out) : Prop :=
  AddVarEqualityRel (p.rename ρ) (renameBindings ρ seed) (ρ left) (ρ right) (renameBindings ρ out)

private abbrev ConstraintsMotive (p : Parameters) (ρ : Equiv.Perm String)
    (seed : Bindings) (order : List Constraint) (out : Bindings)
    (_ : MergeConstraintsRel p seed order out) : Prop :=
  MergeConstraintsRel (p.rename ρ) (renameBindings ρ seed) (order.map (Constraint.rename ρ))
    (renameBindings ρ out)

private abbrev MergeMotive (p : Parameters) (ρ : Equiv.Perm String)
    (left right out : Bindings) (_ : MergeRel p left right out) : Prop :=
  MergeRel (p.rename ρ) (renameBindings ρ left) (renameBindings ρ right) (renameBindings ρ out)

private theorem map_sym (p : Parameters) (ρ : Equiv.Perm String)
    (name : String) (admitted : p.admissible Bindings.empty) :
    MatchMotive p ρ _ _ _ (.symSym name admitted) := by
  simpa only [MatchMotive, renameTypeVars, renameBindings_empty] using
    MatchRel.symSym (p := p.rename ρ) name
      ((Parameters.rename_admissible ρ p Bindings.empty).mpr admitted)

private theorem map_vars (p : Parameters) (ρ : Equiv.Perm String)
    (left right : String) (admitted : p.admissible (Bindings.empty.addEquality left right)) :
    MatchMotive p ρ _ _ _ (.varVar left right admitted) := by
  unfold MatchMotive
  rw [renameBindings_addEquality, renameBindings_empty]
  simp only [renameTypeVars]
  apply MatchRel.varVar
  simpa only [Parameters.rename, renameBindings_addEquality, renameBindings_empty,
    Equiv.symm_apply_apply] using admitted

private theorem map_varAtom (p : Parameters) (ρ : Equiv.Perm String)
    {name : String} {atom : Atom} (nonvariable : isVariableB atom = false)
    (admitted : p.admissible (Bindings.empty.assign name atom)) :
    MatchMotive p ρ _ _ _ (.varNonVar nonvariable admitted) := by
  unfold MatchMotive
  rw [renameBindings_assign, renameBindings_empty]
  simp only [renameTypeVars]
  apply MatchRel.varNonVar (by simpa only [isVariableB_rename] using nonvariable)
  simpa only [renameBindings_assign, renameBindings_empty] using
    (Parameters.rename_admissible ρ p (Bindings.empty.assign name atom)).mpr admitted

private theorem map_atomVar (p : Parameters) (ρ : Equiv.Perm String)
    {name : String} {atom : Atom} (nonvariable : isVariableB atom = false)
    (admitted : p.admissible (Bindings.empty.assign name atom)) :
    MatchMotive p ρ _ _ _ (.nonVarVar nonvariable admitted) := by
  unfold MatchMotive
  rw [renameBindings_assign, renameBindings_empty]
  simp only [renameTypeVars]
  apply MatchRel.nonVarVar (by simpa only [isVariableB_rename] using nonvariable)
  simpa only [renameBindings_assign, renameBindings_empty] using
    (Parameters.rename_admissible ρ p (Bindings.empty.assign name atom)).mpr admitted

private theorem map_expression (p : Parameters) (ρ : Equiv.Perm String)
    {left right : List Atom} {out : Bindings}
    (children : MatchListAccRel p left right Bindings.empty out)
    (admitted : p.admissible out) (ih : ListMotive p ρ _ _ _ _ children) :
    MatchMotive p ρ _ _ _ (.expression children admitted) := by
  simpa only [MatchMotive, renameTypeVars] using
    MatchRel.expression (by simpa only [ListMotive, renameBindings_empty] using ih)
      ((Parameters.rename_admissible ρ p out).mpr admitted)

private theorem map_groundLeft (p : Parameters) (ρ : Equiv.Perm String)
    {grounded : GroundedValue} {right : Atom} {out : Bindings}
    (nonvariable : isVariableB right = false) (custom : p.hasCustomMatcher grounded)
    (matched : p.customMatch grounded right out) (admitted : p.admissible out) :
    MatchMotive p ρ _ _ _ (.groundedLeftCustom nonvariable custom matched admitted) := by
  simpa only [MatchMotive, renameTypeVars] using
    MatchRel.groundedLeftCustom (p := p.rename ρ)
      (by simpa only [isVariableB_rename] using nonvariable) custom
      ((Parameters.rename_customMatch ρ p grounded right out).mpr matched)
      ((Parameters.rename_admissible ρ p out).mpr admitted)

private theorem map_groundRight (p : Parameters) (ρ : Equiv.Perm String)
    {left : Atom} {grounded : GroundedValue} {out : Bindings}
    (nonvariable : isVariableB left = false) (noCustom : ¬p.atomHasCustomMatcher left)
    (custom : p.hasCustomMatcher grounded) (matched : p.customMatch grounded left out)
    (admitted : p.admissible out) :
    MatchMotive p ρ _ _ _ (.groundedRightCustom nonvariable noCustom custom matched admitted) := by
  simpa only [MatchMotive, renameTypeVars] using
    MatchRel.groundedRightCustom (p := p.rename ρ)
      (by simpa only [isVariableB_rename] using nonvariable)
      (fun present => noCustom ((Parameters.rename_atomHasCustomMatcher ρ p left).mp present))
      custom ((Parameters.rename_customMatch ρ p grounded left out).mpr matched)
      ((Parameters.rename_admissible ρ p out).mpr admitted)

private theorem map_groundFallback (p : Parameters) (ρ : Equiv.Perm String)
    {left right : GroundedValue} (leftNo : ¬p.hasCustomMatcher left)
    (rightNo : ¬p.hasCustomMatcher right) (admitted : p.admissible Bindings.empty) :
    MatchMotive p ρ _ _ _ (.groundedFallback leftNo rightNo admitted) := by
  simpa only [MatchMotive, renameTypeVars, renameBindings_empty] using
    MatchRel.groundedFallback (p := p.rename ρ) leftNo rightNo
      ((Parameters.rename_admissible ρ p Bindings.empty).mpr admitted)

private theorem map_listNil (p : Parameters) (ρ : Equiv.Perm String) {seed : Bindings} :
    ListMotive p ρ [] [] seed seed .nil := .nil

private theorem map_listCons (p : Parameters) (ρ : Equiv.Perm String)
    {left right : Atom} {lefts rights : List Atom} {seed matched next out : Bindings}
    (head : MatchRel p left right matched) (merged : MergeRel p seed matched next)
    (tail : MatchListAccRel p lefts rights next out)
    (headIH : MatchMotive p ρ _ _ _ head) (mergeIH : MergeMotive p ρ _ _ _ merged)
    (tailIH : ListMotive p ρ _ _ _ _ tail) :
    ListMotive p ρ _ _ _ _ (.cons head merged tail) := .cons headIH mergeIH tailIH

private theorem map_fresh (p : Parameters) (ρ : Equiv.Perm String)
    {seed : Bindings} {name : String} {atom : Atom} (empty : seed.classValues name = []) :
    BindingMotive p ρ _ _ _ _ (.fresh (value := atom) empty) := by
  unfold BindingMotive
  rw [renameBindings_assign]
  apply AddVarBindingRel.fresh
  rw [renameBindings_classValues, empty]
  rfl

private theorem map_same (p : Parameters) (ρ : Equiv.Perm String)
    {seed : Bindings} {name : String} {atom first : Atom} {rest : List Atom}
    (values : (first :: rest).Perm (seed.classValues name))
    (agree : ValuesAgree (first :: rest)) (same : atom = first) :
    BindingMotive p ρ _ _ _ _ (.same values agree same) := by
  apply AddVarBindingRel.same
  · rw [renameBindings_classValues]
    exact values.map (renameTypeVars ρ)
  · exact (ValuesAgree.rename ρ _).mpr agree
  · exact congrArg (renameTypeVars ρ) same

private theorem map_conflict (p : Parameters) (ρ : Equiv.Perm String)
    {seed : Bindings} {name : String} {atom first : Atom} {rest : List Atom}
    {matched out : Bindings} (values : (first :: rest).Perm (seed.classValues name))
    (agree : ValuesAgree (first :: rest)) (different : atom ≠ first)
    (matchDerivation : MatchRel p first atom matched) (merged : MergeRel p seed matched out)
    (matchIH : MatchMotive p ρ _ _ _ matchDerivation) (mergeIH : MergeMotive p ρ _ _ _ merged) :
    BindingMotive p ρ _ _ _ _ (.conflict values agree different matchDerivation merged) := by
  apply AddVarBindingRel.conflict
  · rw [renameBindings_classValues]
    exact values.map (renameTypeVars ρ)
  · exact (ValuesAgree.rename ρ _).mpr agree
  · exact fun same => different (renameTypeVars_perm_injective ρ same)
  · exact matchIH
  · exact mergeIH

private theorem map_reconcile (p : Parameters) (ρ : Equiv.Perm String)
    {seed : Bindings} {name : String} {atom first : Atom} {rest : List Atom}
    {matched out : Bindings} (values : (first :: rest).Perm (seed.classValues name))
    (disagree : ¬ValuesAgree (first :: rest))
    (matchDerivation : MatchListAccRel p (List.replicate (rest.length + 1) first)
      (rest ++ [atom]) Bindings.empty matched) (merged : MergeRel p seed matched out)
    (matchIH : ListMotive p ρ _ _ _ _ matchDerivation) (mergeIH : MergeMotive p ρ _ _ _ merged) :
    BindingMotive p ρ _ _ _ _ (.reconcile values disagree matchDerivation merged) := by
  apply AddVarBindingRel.reconcile
  · rw [renameBindings_classValues]
    exact values.map (renameTypeVars ρ)
  · exact fun agree => disagree ((ValuesAgree.rename ρ _).mp agree)
  · simpa only [ListMotive, List.map_replicate, List.map_append, List.map_cons,
      List.map_nil, List.length_map, renameBindings_empty] using matchIH
  · exact mergeIH

private theorem map_equalityConsistent (p : Parameters) (ρ : Equiv.Perm String)
    {seed : Bindings} {left right : String} {values : List Atom}
    (selected : (seed.addEquality left right).classValues left = values)
    (agree : ValuesAgree values) :
    EqualityMotive p ρ _ _ _ _ (.consistent selected agree) := by
  unfold EqualityMotive
  rw [renameBindings_addEquality]
  apply AddVarEqualityRel.consistent (values := values.map (renameTypeVars ρ))
  · rw [← renameBindings_addEquality, renameBindings_classValues, selected]
  · exact (ValuesAgree.rename ρ _).mpr agree

private theorem map_equalityReconcile (p : Parameters) (ρ : Equiv.Perm String)
    {seed : Bindings} {left right : String} {first : Atom} {rest : List Atom}
    {matched out : Bindings}
    (values : (first :: rest).Perm ((seed.addEquality left right).classValues left))
    (disagree : ¬ValuesAgree (first :: rest))
    (matchDerivation : MatchListAccRel p (List.replicate rest.length first) rest Bindings.empty matched)
    (merged : MergeRel p (seed.addEquality left right) matched out)
    (matchIH : ListMotive p ρ _ _ _ _ matchDerivation) (mergeIH : MergeMotive p ρ _ _ _ merged) :
    EqualityMotive p ρ _ _ _ _ (.reconcile values disagree matchDerivation merged) := by
  apply AddVarEqualityRel.reconcile
  · rw [← renameBindings_addEquality, renameBindings_classValues]
    exact values.map (renameTypeVars ρ)
  · exact fun agree => disagree ((ValuesAgree.rename ρ _).mp agree)
  · simpa only [ListMotive, List.map_replicate, List.length_map, renameBindings_empty] using matchIH
  · simpa only [MergeMotive, renameBindings_addEquality] using mergeIH

private theorem map_constraintsNil (p : Parameters) (ρ : Equiv.Perm String) {seed : Bindings} :
    ConstraintsMotive p ρ seed [] seed .nil := .nil

private theorem map_constraintsValue (p : Parameters) (ρ : Equiv.Perm String)
    {seed next out : Bindings} {name : String} {atom : Atom} {rest : List Constraint}
    (head : AddVarBindingRel p seed name atom next) (tail : MergeConstraintsRel p next rest out)
    (headIH : BindingMotive p ρ _ _ _ _ head) (tailIH : ConstraintsMotive p ρ _ _ _ tail) :
    ConstraintsMotive p ρ _ _ _ (.value head tail) := .value headIH tailIH

private theorem map_constraintsEquality (p : Parameters) (ρ : Equiv.Perm String)
    {seed next out : Bindings} {left right : String} {rest : List Constraint}
    (head : AddVarEqualityRel p seed left right next) (tail : MergeConstraintsRel p next rest out)
    (headIH : EqualityMotive p ρ _ _ _ _ head) (tailIH : ConstraintsMotive p ρ _ _ _ tail) :
    ConstraintsMotive p ρ _ _ _ (.equality head tail) := .equality headIH tailIH

private theorem map_merge (p : Parameters) (ρ : Equiv.Perm String)
    {left right out : Bindings} {order : List Constraint}
    (permuted : order.Perm (constraints right)) (fold : MergeConstraintsRel p left order out)
    (ih : ConstraintsMotive p ρ _ _ _ fold) :
    MergeMotive p ρ _ _ _ (.mk permuted fold) := by
  apply MergeRel.mk _ ih
  rw [constraints_renameBindings]
  exact permuted.map (Constraint.rename ρ)

/-- Simultaneous variable permutation preserves the complete MatchRel derivation. -/
theorem MatchRel.rename (ρ : Equiv.Perm String) {p : Parameters}
    {left right : Atom} {out : Bindings} (derivation : MatchRel p left right out) :
    MatchRel (p.rename ρ) (renameTypeVars ρ left) (renameTypeVars ρ right) (renameBindings ρ out) :=
  MatchRel.rec
    (motive_1 := MatchMotive p ρ)
    (motive_2 := ListMotive p ρ)
    (motive_3 := BindingMotive p ρ)
    (motive_4 := EqualityMotive p ρ)
    (motive_5 := ConstraintsMotive p ρ)
    (motive_6 := MergeMotive p ρ)
    (map_sym p ρ)
    (map_vars p ρ)
    (map_varAtom p ρ)
    (map_atomVar p ρ)
    (map_expression p ρ)
    (map_groundLeft p ρ)
    (map_groundRight p ρ)
    (map_groundFallback p ρ)
    (map_listNil p ρ)
    (map_listCons p ρ)
    (map_fresh p ρ)
    (map_same p ρ)
    (map_conflict p ρ)
    (map_reconcile p ρ)
    (map_equalityConsistent p ρ)
    (map_equalityReconcile p ρ)
    (map_constraintsNil p ρ)
    (map_constraintsValue p ρ)
    (map_constraintsEquality p ρ)
    (map_merge p ρ)
    derivation

/-- Simultaneous variable permutation preserves the complete MatchListAccRel derivation. -/
theorem MatchListAccRel.rename (ρ : Equiv.Perm String) {p : Parameters}
    {left right : List Atom} {seed out : Bindings} (derivation : MatchListAccRel p left right seed out) :
    MatchListAccRel (p.rename ρ) (left.map (renameTypeVars ρ)) (right.map (renameTypeVars ρ))
      (renameBindings ρ seed) (renameBindings ρ out) :=
  MatchListAccRel.rec
    (motive_1 := MatchMotive p ρ)
    (motive_2 := ListMotive p ρ)
    (motive_3 := BindingMotive p ρ)
    (motive_4 := EqualityMotive p ρ)
    (motive_5 := ConstraintsMotive p ρ)
    (motive_6 := MergeMotive p ρ)
    (map_sym p ρ)
    (map_vars p ρ)
    (map_varAtom p ρ)
    (map_atomVar p ρ)
    (map_expression p ρ)
    (map_groundLeft p ρ)
    (map_groundRight p ρ)
    (map_groundFallback p ρ)
    (map_listNil p ρ)
    (map_listCons p ρ)
    (map_fresh p ρ)
    (map_same p ρ)
    (map_conflict p ρ)
    (map_reconcile p ρ)
    (map_equalityConsistent p ρ)
    (map_equalityReconcile p ρ)
    (map_constraintsNil p ρ)
    (map_constraintsValue p ρ)
    (map_constraintsEquality p ρ)
    (map_merge p ρ)
    derivation

/-- Simultaneous variable permutation preserves the complete AddVarBindingRel derivation. -/
theorem AddVarBindingRel.rename (ρ : Equiv.Perm String) {p : Parameters}
    {seed : Bindings} {name : String} {atom : Atom} {out : Bindings} (derivation : AddVarBindingRel p seed name atom out) :
    AddVarBindingRel (p.rename ρ) (renameBindings ρ seed) (ρ name) (renameTypeVars ρ atom)
      (renameBindings ρ out) :=
  AddVarBindingRel.rec
    (motive_1 := MatchMotive p ρ)
    (motive_2 := ListMotive p ρ)
    (motive_3 := BindingMotive p ρ)
    (motive_4 := EqualityMotive p ρ)
    (motive_5 := ConstraintsMotive p ρ)
    (motive_6 := MergeMotive p ρ)
    (map_sym p ρ)
    (map_vars p ρ)
    (map_varAtom p ρ)
    (map_atomVar p ρ)
    (map_expression p ρ)
    (map_groundLeft p ρ)
    (map_groundRight p ρ)
    (map_groundFallback p ρ)
    (map_listNil p ρ)
    (map_listCons p ρ)
    (map_fresh p ρ)
    (map_same p ρ)
    (map_conflict p ρ)
    (map_reconcile p ρ)
    (map_equalityConsistent p ρ)
    (map_equalityReconcile p ρ)
    (map_constraintsNil p ρ)
    (map_constraintsValue p ρ)
    (map_constraintsEquality p ρ)
    (map_merge p ρ)
    derivation

/-- Simultaneous variable permutation preserves the complete AddVarEqualityRel derivation. -/
theorem AddVarEqualityRel.rename (ρ : Equiv.Perm String) {p : Parameters}
    {seed : Bindings} {left right : String} {out : Bindings} (derivation : AddVarEqualityRel p seed left right out) :
    AddVarEqualityRel (p.rename ρ) (renameBindings ρ seed) (ρ left) (ρ right) (renameBindings ρ out) :=
  AddVarEqualityRel.rec
    (motive_1 := MatchMotive p ρ)
    (motive_2 := ListMotive p ρ)
    (motive_3 := BindingMotive p ρ)
    (motive_4 := EqualityMotive p ρ)
    (motive_5 := ConstraintsMotive p ρ)
    (motive_6 := MergeMotive p ρ)
    (map_sym p ρ)
    (map_vars p ρ)
    (map_varAtom p ρ)
    (map_atomVar p ρ)
    (map_expression p ρ)
    (map_groundLeft p ρ)
    (map_groundRight p ρ)
    (map_groundFallback p ρ)
    (map_listNil p ρ)
    (map_listCons p ρ)
    (map_fresh p ρ)
    (map_same p ρ)
    (map_conflict p ρ)
    (map_reconcile p ρ)
    (map_equalityConsistent p ρ)
    (map_equalityReconcile p ρ)
    (map_constraintsNil p ρ)
    (map_constraintsValue p ρ)
    (map_constraintsEquality p ρ)
    (map_merge p ρ)
    derivation

/-- Simultaneous variable permutation preserves the complete MergeConstraintsRel derivation. -/
theorem MergeConstraintsRel.rename (ρ : Equiv.Perm String) {p : Parameters}
    {seed : Bindings} {order : List Constraint} {out : Bindings} (derivation : MergeConstraintsRel p seed order out) :
    MergeConstraintsRel (p.rename ρ) (renameBindings ρ seed) (order.map (Constraint.rename ρ))
      (renameBindings ρ out) :=
  MergeConstraintsRel.rec
    (motive_1 := MatchMotive p ρ)
    (motive_2 := ListMotive p ρ)
    (motive_3 := BindingMotive p ρ)
    (motive_4 := EqualityMotive p ρ)
    (motive_5 := ConstraintsMotive p ρ)
    (motive_6 := MergeMotive p ρ)
    (map_sym p ρ)
    (map_vars p ρ)
    (map_varAtom p ρ)
    (map_atomVar p ρ)
    (map_expression p ρ)
    (map_groundLeft p ρ)
    (map_groundRight p ρ)
    (map_groundFallback p ρ)
    (map_listNil p ρ)
    (map_listCons p ρ)
    (map_fresh p ρ)
    (map_same p ρ)
    (map_conflict p ρ)
    (map_reconcile p ρ)
    (map_equalityConsistent p ρ)
    (map_equalityReconcile p ρ)
    (map_constraintsNil p ρ)
    (map_constraintsValue p ρ)
    (map_constraintsEquality p ρ)
    (map_merge p ρ)
    derivation

/-- Simultaneous variable permutation preserves the complete MergeRel derivation. -/
theorem MergeRel.rename (ρ : Equiv.Perm String) {p : Parameters}
    {left right out : Bindings} (derivation : MergeRel p left right out) :
    MergeRel (p.rename ρ) (renameBindings ρ left) (renameBindings ρ right) (renameBindings ρ out) :=
  MergeRel.rec
    (motive_1 := MatchMotive p ρ)
    (motive_2 := ListMotive p ρ)
    (motive_3 := BindingMotive p ρ)
    (motive_4 := EqualityMotive p ρ)
    (motive_5 := ConstraintsMotive p ρ)
    (motive_6 := MergeMotive p ρ)
    (map_sym p ρ)
    (map_vars p ρ)
    (map_varAtom p ρ)
    (map_atomVar p ρ)
    (map_expression p ρ)
    (map_groundLeft p ρ)
    (map_groundRight p ρ)
    (map_groundFallback p ρ)
    (map_listNil p ρ)
    (map_listCons p ρ)
    (map_fresh p ρ)
    (map_same p ρ)
    (map_conflict p ρ)
    (map_reconcile p ρ)
    (map_equalityConsistent p ρ)
    (map_equalityReconcile p ρ)
    (map_constraintsNil p ρ)
    (map_constraintsValue p ρ)
    (map_constraintsEquality p ρ)
    (map_merge p ρ)
    derivation


@[simp] theorem Parameters.rename_inverse (ρ : Equiv.Perm String) (p : Parameters) :
    (p.rename ρ).rename ρ.symm = p := by
  cases p
  simp [Parameters.rename]

@[simp] theorem Parameters.rename_equalityGroundedSemantic (ρ : Equiv.Perm String) :
    equalityGroundedSemantic.rename ρ = equalityGroundedSemantic := by
  have atomEq (atom : Atom) (grounded : GroundedValue) :
      renameTypeVars ρ.symm atom = .grounded grounded ↔ atom = .grounded grounded := by
    cases atom <;> simp [renameTypeVars]
  have bindingsEq (bindings : Bindings) :
      renameBindings ρ.symm bindings = Bindings.empty ↔ bindings = Bindings.empty := by
    simpa only [renameBindings_empty] using
      (renameBindings_perm_injective ρ.symm).eq_iff (a := bindings) (b := Bindings.empty)
  unfold Parameters.rename equalityGroundedSemantic
  congr 1
  · funext grounded atom out
    exact propext (and_congr (atomEq atom grounded) (bindingsEq out))
  · funext bindings
    exact propext (SemanticLoopFree.rename_iff ρ.symm bindings)

end Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge

namespace Mettapedia.Languages.MeTTa.HE.EquationFreshening
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge Spec.Type.RuntimeRefinement

mutual

/-- Observation under a renamed atom is observation under the reindexed
valuation. Values returned by the valuation are left untouched. -/
theorem applyClassSolution_renameTypeVars (valuation : String → Metta.Atom)
    (rename : String → String) (atom : Atom) :
    applyClassSolution valuation (toLeaTTaAtom (renameTypeVars rename atom)) =
      applyClassSolution (valuation ∘ rename) (toLeaTTaAtom atom) := by
  cases atom with
  | symbol => simp [renameTypeVars, toLeaTTaAtom, applyClassSolution]
  | var => simp [renameTypeVars, toLeaTTaAtom, applyClassSolution, Function.comp_apply]
  | grounded => simp [renameTypeVars, toLeaTTaAtom, applyClassSolution]
  | expression atoms =>
      simpa only [renameTypeVars, toLeaTTaAtom, applyClassSolution] using
        congrArg Metta.Atom.expr (applyClassSolution_renameTypeVarsList valuation rename atoms)

/-- List companion of valuation reindexing through a structural renaming. -/
theorem applyClassSolution_renameTypeVarsList (valuation : String → Metta.Atom)
    (rename : String → String) (atoms : List Atom) :
    (toLeaTTaAtoms (atoms.map (renameTypeVars rename))).map (applyClassSolution valuation) =
      (toLeaTTaAtoms atoms).map (applyClassSolution (valuation ∘ rename)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simpa only [List.map_cons, toLeaTTaAtoms] using
        congrArg₂ List.cons (applyClassSolution_renameTypeVars valuation rename atom)
          (applyClassSolution_renameTypeVarsList valuation rename atoms)

end

end Mettapedia.Languages.MeTTa.HE.EquationFreshening

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement

/-- A permutation fixing every finite model of a satisfiable binding theory
fixes each name outside the entire constraint support literally. -/
theorem model_fixed_fixes_outside {bindings : Bindings} (p : Equiv.Perm String)
    (model : ∃ valuation, TypeBindingSatisfied valuation bindings)
    (fixed : ∀ valuation, TypeBindingSatisfied valuation bindings →
      ∀ name, valuation (p name) = valuation name)
    (name : String) (outside : name∉specBindingVars bindings) : p name=name := by
  classical
  obtain ⟨valuation,satisfied⟩ := model
  by_contra different
  let first := Function.update valuation name (.symbol "A")
  let second := Function.update valuation name (.symbol "B")
  have firstModel : TypeBindingSatisfied first bindings :=
    (specTypeBindingSatisfied_congr_of_bindingVars (fun key member => by
      have distinct : key≠name := fun same=>outside (same ▸ member)
      simp [first,Function.update_of_ne distinct])).mp satisfied
  have secondModel : TypeBindingSatisfied second bindings :=
    (specTypeBindingSatisfied_congr_of_bindingVars (fun key member => by
      have distinct : key≠name := fun same=>outside (same ▸ member)
      simp [second,Function.update_of_ne distinct])).mp satisfied
  have a := fixed first firstModel name
  have b := fixed second secondModel name
  simp only [first,second,Function.update_self,Function.update_of_ne different] at a b
  have impossible := a.symm.trans b
  exact (by decide : ("A" : String) ≠ "B") (Atom.symbol.inj impossible)

/-- The full syntactic support is transported as one ordered list. -/
theorem specBindingVars_renameBindings (rename : String→String) (bindings : Bindings) :
    specBindingVars (renameBindings rename bindings) = (specBindingVars bindings).map rename := by
  simp only [specBindingVars,renameBindings,List.flatMap_map,List.map_append,List.map_flatMap]
  congr 1
  · apply List.flatMap_congr
    intro pair _
    simp [Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]

/-- Model-fixed coordinate changes preserve exact freshness support, not
just the set of models. Satisfiability is essential to this conclusion. -/
theorem renameBindings_support_of_model_fixed {bindings : Bindings} (p : Equiv.Perm String)
    (model : ∃ valuation, TypeBindingSatisfied valuation bindings)
    (fixed : ∀ valuation, TypeBindingSatisfied valuation bindings →
      ∀ name, valuation (p name) = valuation name) (name : String) :
    name∈specBindingVars (renameBindings p bindings) ↔ name∈specBindingVars bindings := by
  rw [specBindingVars_renameBindings]
  constructor
  · rintro member
    obtain ⟨old,present,rfl⟩:=List.mem_map.mp member
    by_contra absent
    have same := model_fixed_fixes_outside p model fixed (p old) absent
    exact absent ((p.injective same).symm ▸ present)
  · intro present
    apply List.mem_map.mpr
    refine ⟨p.symm name,?_,p.apply_symm_apply name⟩
    by_contra absent
    have same := model_fixed_fixes_outside p model fixed (p.symm name) absent
    exact absent ((by simpa using same : name=p.symm name) ▸ present)

/-- All pending syntax can be observed under one model-fixed action. This is
an interpretation law; it does not erase name-inspecting service policies. -/
theorem applyTypeValuation_model_fixed (p : Equiv.Perm String) (valuation : String→Atom)
    (fixed : ∀ name,valuation (p name)=valuation name) (atom : Atom) :
    applyTypeValuation valuation (renameTypeVars p atom)=applyTypeValuation valuation atom := by
  rw [ApplicationEquivariance.applyTypeValuation_renameTypeVars]
  have same : valuation ∘ p=valuation := funext fixed
  rw [same]

end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation

/-- A permutation fixing each model valuation preserves the entire binding
theory in both directions. The reverse uses bijectivity of the permutation. -/
theorem renameBindings_theory_of_model_fixed (bindings : Bindings)
    (permutation : Equiv.Perm String)
    (fixed : ∀ valuation, TypeBindingSatisfied valuation bindings →
      ∀ name, valuation (permutation name) = valuation name)
    (valuation : String → Atom) :
    TypeBindingSatisfied valuation (renameBindings permutation bindings) ↔
      TypeBindingSatisfied valuation bindings := by
  rw [renameBindings_typeBindingSatisfied]
  constructor
  · intro satisfied
    have same : valuation ∘ permutation = valuation := by
      funext name
      have equality := fixed (valuation ∘ permutation) satisfied (permutation.symm name)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using equality
    simpa only [same] using satisfied
  · intro satisfied
    have same : valuation ∘ permutation = valuation :=
      funext (fixed valuation satisfied)
    simpa only [same] using satisfied

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection


namespace Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-- Exact theory agreement while all private variables remain live. Variable
support is recorded separately because a tautological alias still affects
freshening. Structural admissibility is a per-record fact, not a field here. -/
structure BindingSourceAgreement (native independent : Bindings) : Prop where
  solutions : ∀ valuation,
    TypeBindingSatisfied valuation native ↔ TypeBindingSatisfied valuation independent
  support : ∀ name,name∈specBindingVars native ↔ name∈specBindingVars independent

namespace BindingSourceAgreement
@[refl] theorem refl (bindings : Bindings) : BindingSourceAgreement bindings bindings :=
  ⟨fun _=>Iff.rfl,fun _=>Iff.rfl⟩

theorem symm {left right : Bindings} (related : BindingSourceAgreement left right) :
    BindingSourceAgreement right left := ⟨fun v=>(related.solutions v).symm,fun n=>(related.support n).symm⟩

theorem trans {left middle right : Bindings} (first : BindingSourceAgreement left middle)
    (second : BindingSourceAgreement middle right) : BindingSourceAgreement left right :=
  ⟨fun v=>(first.solutions v).trans (second.solutions v),
    fun n=>(first.support n).trans (second.support n)⟩

theorem of_recordPerm {left right : Bindings} (related : BindingRecordPerm left right) :
    BindingSourceAgreement left right := ⟨related.satisfied_iff,related.support_iff⟩

theorem theoryEquivAt {left right : Bindings} (related : BindingSourceAgreement left right)
    (scope : List String) : BindingTheoryEquivAt scope left right :=
  BindingTheoryEquivAt.of_solution_iff related.solutions scope

end BindingSourceAgreement
end Mettapedia.Languages.MeTTa.HE

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation Spec.Match.Merge

theorem aliasConstraints_assignment {bindings : Bindings} {key : String} {value : Atom} :
    (key, value) ∈ (aliasConstraints bindings).assignments ↔
      (key, value) ∈ bindings.assignments ∧ isVariableB value = false := by
  simp [aliasConstraints]

theorem aliasConstraints_equality {bindings : Bindings} {left right : String} :
    (left, right) ∈ (aliasConstraints bindings).equalities ↔
      (left, right) ∈ bindings.equalities ∨ (left, .var right) ∈ bindings.assignments := by
  simp only [aliasConstraints, List.mem_append, List.mem_filterMap]
  apply or_congr_right
  constructor
  · rintro ⟨⟨key, value⟩, stored, exposed⟩
    cases value <;> simp_all
  · intro stored
    exact ⟨(left, .var right), stored, rfl⟩

/-- This changes the constraint carrier, not its full set of models. -/
theorem aliasConstraints_models (bindings : Bindings) (valuation : String → Atom) :
    TypeBindingSatisfied valuation (aliasConstraints bindings) ↔
      TypeBindingSatisfied valuation bindings := by
  constructor
  · rintro ⟨assignments, equalities⟩
    constructor
    · intro key value stored
      cases value with
      | var other =>
          simpa only [applyTypeValuation] using
            equalities key other (aliasConstraints_equality.mpr (Or.inr stored))
      | symbol symbol => exact assignments key _ (aliasConstraints_assignment.mpr ⟨stored, rfl⟩)
      | grounded grounded => exact assignments key _ (aliasConstraints_assignment.mpr ⟨stored, rfl⟩)
      | expression values => exact assignments key _ (aliasConstraints_assignment.mpr ⟨stored, rfl⟩)
    · intro left right stored
      exact equalities left right (aliasConstraints_equality.mpr (Or.inl stored))
  · rintro ⟨assignments, equalities⟩
    constructor
    · intro key value stored
      exact assignments key value (aliasConstraints_assignment.mp stored).1
    · intro left right stored
      rcases aliasConstraints_equality.mp stored with equality | bare
      · exact equalities left right equality
      · simpa only [applyTypeValuation] using assignments left (.var right) bare

theorem aliasConstraints_nonvariable (bindings : Bindings) :
    ∀ key value, (key, value) ∈ (aliasConstraints bindings).assignments →
      isVariableB value = false := by
  intro key value stored
  exact (aliasConstraints_assignment.mp stored).2

private theorem support_characterization (bindings : Bindings) (name : String) :
    name ∈ specBindingVars bindings ↔
      (∃ key value, (key, value) ∈ bindings.assignments ∧
        (name = key ∨ name ∈ TypeSubst.typeVars value)) ∨
      ∃ left right, (left, right) ∈ bindings.equalities ∧ (name = left ∨ name = right) := by
  simp only [specBindingVars, List.mem_append,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨⟨key, value⟩, stored, here⟩ | ⟨⟨left, right⟩, stored, here⟩)
    · exact Or.inl ⟨key, value, stored, here⟩
    · exact Or.inr ⟨left, right, stored, here⟩
  · rintro (⟨key, value, stored, here⟩ | ⟨left, right, stored, here⟩)
    · exact Or.inl ⟨(key, value), stored, here⟩
    · exact Or.inr ⟨(left, right), stored, here⟩

/-- Both endpoints of an alias remain visible to freshness and scope checks. -/
theorem aliasConstraints_support (bindings : Bindings) (name : String) :
    name ∈ specBindingVars (aliasConstraints bindings) ↔ name ∈ specBindingVars bindings := by
  rw [support_characterization, support_characterization]
  constructor
  · rintro (⟨key, value, stored, occurs⟩ | ⟨left, right, stored, occurs⟩)
    · exact Or.inl ⟨key, value, (aliasConstraints_assignment.mp stored).1, occurs⟩
    · rcases aliasConstraints_equality.mp stored with equality | bare
      · exact Or.inr ⟨left, right, equality, occurs⟩
      · exact Or.inl ⟨left, .var right, bare, by simpa [TypeSubst.typeVars] using occurs⟩
  · rintro (⟨key, value, stored, occurs⟩ | ⟨left, right, stored, occurs⟩)
    · cases value with
      | var other =>
          exact Or.inr ⟨key, other, aliasConstraints_equality.mpr (Or.inr stored),
            by simpa [TypeSubst.typeVars] using occurs⟩
      | symbol symbol => exact Or.inl ⟨key, _, aliasConstraints_assignment.mpr ⟨stored, rfl⟩, occurs⟩
      | grounded grounded => exact Or.inl ⟨key, _, aliasConstraints_assignment.mpr ⟨stored, rfl⟩, occurs⟩
      | expression values => exact Or.inl ⟨key, _, aliasConstraints_assignment.mpr ⟨stored, rfl⟩, occurs⟩
    · exact Or.inr ⟨left, right, aliasConstraints_equality.mpr (Or.inl stored), occurs⟩

theorem aliasConstraints_eq_self {bindings : Bindings}
    (nonvariable : ∀ key value, (key, value) ∈ bindings.assignments → isVariableB value = false) :
    aliasConstraints bindings = bindings := by
  have keep : bindings.assignments.filter (fun entry => !isVariableB entry.2) = bindings.assignments := by
    apply List.filter_eq_self.mpr
    intro entry stored
    simp [nonvariable entry.1 entry.2 stored]
  have remove : bindings.assignments.filterMap (fun entry =>
      match entry.2 with | .var other => some (entry.1, other) | _ => none) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro entry stored
    have shape := nonvariable entry.1 entry.2 stored
    cases valueEq : entry.2 <;> simp_all [isVariableB]
  exact congrArg₂ Bindings.mk keep
    ((congrArg (fun rows => bindings.equalities ++ rows) remove).trans (List.append_nil _))

theorem aliasConstraints_idempotent (bindings : Bindings) :
    aliasConstraints (aliasConstraints bindings) = aliasConstraints bindings :=
  aliasConstraints_eq_self (aliasConstraints_nonvariable bindings)

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

namespace Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation

/-- One structural action reaches all constraint names and values together. -/
theorem rename (f : String → String) {left right : Bindings}
    (agreement : BindingSourceAgreement left right) :
    BindingSourceAgreement (renameBindings f left) (renameBindings f right) := by
  constructor
  · intro valuation
    simpa only [renameBindings_typeBindingSatisfied] using agreement.solutions (valuation ∘ f)
  · intro name
    simp only [specBindingVars_renameBindings, List.mem_map]
    constructor
    · rintro ⟨original, present, same⟩
      exact ⟨original, (agreement.support original).mp present, same⟩
    · rintro ⟨original, present, same⟩
      exact ⟨original, (agreement.support original).mpr present, same⟩

end Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement

namespace Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement

/-- Successful logical conjunction of two finite constraint records. Exact
name support preserves freshness even for tautological constraints. Literal
representative selection belongs to the separate retained readout certificate. -/
def LogicalMergeRel (left right output : HE.Bindings) : Prop :=
  BindingSourceAgreement output
    ⟨left.assignments ++ right.assignments, left.equalities ++ right.equalities⟩ ∧
  ∃ valuation : String → Atom, TypeBindingSatisfied valuation output

namespace LogicalMergeRel

theorem solutions {left right output : HE.Bindings}
    (merged : LogicalMergeRel left right output) (valuation : String → Atom) :
    TypeBindingSatisfied valuation output ↔
      TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right :=
  (merged.1.solutions valuation).trans (bindingSatisfied_append_iff valuation left right)

theorem support {left right output : HE.Bindings}
    (merged : LogicalMergeRel left right output) (name : String) :
    name ∈ specBindingVars output ↔
      name ∈ specBindingVars left ∨ name ∈ specBindingVars right :=
  (merged.1.support name).trans (mem_specBindingVars_append left right name)

theorem common_model {left right output : HE.Bindings}
    (merged : LogicalMergeRel left right output) :
    ∃ valuation : String → Atom,
      TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right := by
  obtain ⟨valuation, model⟩ := merged.2
  exact ⟨valuation, (merged.solutions valuation).mp model⟩

/-- The finite concatenated constraints give an actual logical output whenever
both inputs have a common finite model. This does not choose a readout table. -/
theorem append_of_common_model {left right : HE.Bindings}
    (common : ∃ valuation : String → Atom,
      TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right) :
    LogicalMergeRel left right
      ⟨left.assignments ++ right.assignments, left.equalities ++ right.equalities⟩ := by
  obtain ⟨valuation, leftModel, rightModel⟩ := common
  exact ⟨BindingSourceAgreement.refl _, valuation,
    (bindingSatisfied_append_iff valuation left right).mpr ⟨leftModel, rightModel⟩⟩

theorem exists_iff_common_model (left right : HE.Bindings) :
    (∃ output, LogicalMergeRel left right output) ↔
      ∃ valuation : String → Atom,
        TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right := by
  constructor
  · rintro ⟨output, merged⟩
    exact merged.common_model
  · intro common
    exact ⟨_, append_of_common_model common⟩

/-- Full theory and support suffice for an input representation change.
No nonvariable-row or canonical-reader property is used. -/
theorem congr_inputs {left left' right right' output : HE.Bindings}
    (leftRelated : BindingSourceAgreement left left')
    (rightRelated : BindingSourceAgreement right right') :
    LogicalMergeRel left right output ↔ LogicalMergeRel left' right' output := by
  suffices forward : ∀ {l l' r r' : HE.Bindings}, BindingSourceAgreement l l' →
      BindingSourceAgreement r r' → LogicalMergeRel l r output → LogicalMergeRel l' r' output from
    ⟨forward leftRelated rightRelated, forward leftRelated.symm rightRelated.symm⟩
  intro l l' r r' leftSame rightSame logical
  refine ⟨⟨?_, ?_⟩, logical.2⟩
  · intro valuation
    rw [logical.1.solutions valuation, bindingSatisfied_append_iff,
      bindingSatisfied_append_iff, leftSame.solutions valuation, rightSame.solutions valuation]
  · intro name
    rw [logical.1.support name, mem_specBindingVars_append, mem_specBindingVars_append,
      leftSame.support name, rightSame.support name]

theorem outputs_agree {left right first second : HE.Bindings}
    (a : LogicalMergeRel left right first) (b : LogicalMergeRel left right second) :
    BindingSourceAgreement first second := a.1.trans b.1.symm

/-- Constraint conjunction is symmetric. This states no literal row-order
or concrete reader equality. -/
theorem comm {left right output : HE.Bindings}
    (merged : LogicalMergeRel left right output) : LogicalMergeRel right left output := by
  refine ⟨⟨?_, ?_⟩, merged.2⟩
  · intro valuation
    rw [bindingSatisfied_append_iff, merged.solutions valuation, and_comm]
  · intro name
    rw [mem_specBindingVars_append, merged.support name, or_comm]

/-- A genuine finite model transports through a simultaneous permutation. -/
theorem renamed_satisfiable (p : Equiv.Perm String) {bindings : HE.Bindings}
    (finite : ∃ valuation : String → Atom, TypeBindingSatisfied valuation bindings) :
    ∃ valuation : String → Atom, TypeBindingSatisfied valuation (renameBindings p bindings) := by
  obtain ⟨valuation, satisfied⟩ := finite
  refine ⟨valuation ∘ p.symm, (renameBindings_typeBindingSatisfied _ _ _).mpr ?_⟩
  have inverse : (valuation ∘ p.symm) ∘ p = valuation := by funext name; simp
  simpa only [inverse] using satisfied

theorem rename (p : Equiv.Perm String) {left right output : HE.Bindings}
    (merged : LogicalMergeRel left right output) :
    LogicalMergeRel (renameBindings p left) (renameBindings p right)
      (renameBindings p output) := by
  refine ⟨?_, renamed_satisfiable p merged.2⟩
  simpa only [renameBindings, List.map_append] using merged.1.rename p

theorem rename_iff (p : Equiv.Perm String) (left right output : HE.Bindings) :
    LogicalMergeRel (renameBindings p left) (renameBindings p right)
      (renameBindings p output) ↔ LogicalMergeRel left right output := by
  constructor
  · intro derived
    simpa only [renameBindings_perm_inverse] using derived.rename p.symm
  · exact rename p

end LogicalMergeRel
end Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation


namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open LeaTTaBridge Spec.Type.RuntimeRefinement

mutual

/-- Translating a native valuation after applying it is the same as applying
its pointwise translation in the LeaTTa model language. -/
theorem toLeaTTaAtom_applyTypeValuation
    (valuation : String → Atom) (atom : Atom) :
    toLeaTTaAtom (applyTypeValuation valuation atom) =
      applyClassSolution (fun name => toLeaTTaAtom (valuation name))
        (toLeaTTaAtom atom) := by
  cases atom with
  | symbol | var | grounded =>
      simp [applyTypeValuation, toLeaTTaAtom, applyClassSolution]
  | expression atoms =>
      rw [applyTypeValuation, toLeaTTaAtom, toLeaTTaAtom,
        applyClassSolution]
      exact congrArg Metta.Atom.expr
        (toLeaTTaAtoms_applyTypeValuation valuation atoms)
termination_by 2 * sizeOf atom

/-- List companion of `toLeaTTaAtom_applyTypeValuation`. -/
theorem toLeaTTaAtoms_applyTypeValuation
    (valuation : String → Atom) (atoms : List Atom) :
    toLeaTTaAtoms (atoms.map (applyTypeValuation valuation)) =
      (toLeaTTaAtoms atoms).map
        (applyClassSolution (fun name => toLeaTTaAtom (valuation name))) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (toLeaTTaAtom_applyTypeValuation valuation atom)
        (toLeaTTaAtoms_applyTypeValuation valuation atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end

mutual

/-- Decoding commutes with semantic substitution for every LeaTTa atom, not
only atoms known to lie in the native translation image. -/
theorem fromLeaTTaAtom_applyClassSolution_any
    (valuation : String → Metta.Atom) (atom : Metta.Atom) :
    fromLeaTTaAtom (applyClassSolution valuation atom) =
      applyTypeValuation (fun name => fromLeaTTaAtom (valuation name))
        (fromLeaTTaAtom atom) := by
  cases atom with
  | sym | var | gnd =>
      simp [applyClassSolution, fromLeaTTaAtom, applyTypeValuation]
  | expr atoms =>
      simp only [applyClassSolution, fromLeaTTaAtom,
        applyTypeValuation.eq_def]
      exact congrArg Atom.expression
        (fromLeaTTaAtoms_applyClassSolution_any valuation atoms)

/-- List companion of `fromLeaTTaAtom_applyClassSolution_any`. -/
theorem fromLeaTTaAtoms_applyClassSolution_any
    (valuation : String → Metta.Atom) (atoms : List Metta.Atom) :
    fromLeaTTaAtoms (atoms.map (applyClassSolution valuation)) =
      (fromLeaTTaAtoms atoms).map
        (applyTypeValuation (fun name => fromLeaTTaAtom (valuation name))) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (fromLeaTTaAtom_applyClassSolution_any valuation atom)
        (fromLeaTTaAtoms_applyClassSolution_any valuation atoms)

end


mutual

/-- Decoding a substituted translated atom is the same as applying the
pointwise decoded valuation natively.  The LeaTTa valuation itself need not
lie in the image of the translation. -/
theorem fromLeaTTaAtom_applyClassSolution
    (valuation : String → Metta.Atom) (atom : Atom) :
    fromLeaTTaAtom
        (applyClassSolution valuation (toLeaTTaAtom atom)) =
      applyTypeValuation (fun name => fromLeaTTaAtom (valuation name)) atom := by
  cases atom with
  | symbol | var | grounded =>
      simp [applyTypeValuation, toLeaTTaAtom, applyClassSolution,
        fromLeaTTaAtom]
  | expression atoms =>
      rw [toLeaTTaAtom, applyClassSolution, fromLeaTTaAtom,
        applyTypeValuation]
      exact congrArg Atom.expression
        (fromLeaTTaAtoms_applyClassSolution valuation atoms)
termination_by 2 * sizeOf atom

/-- List companion of `fromLeaTTaAtom_applyClassSolution`. -/
theorem fromLeaTTaAtoms_applyClassSolution
    (valuation : String → Metta.Atom) (atoms : List Atom) :
    fromLeaTTaAtoms
        ((toLeaTTaAtoms atoms).map (applyClassSolution valuation)) =
      atoms.map
        (applyTypeValuation (fun name => fromLeaTTaAtom (valuation name))) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      exact congrArg₂ List.cons
        (fromLeaTTaAtom_applyClassSolution valuation atom)
        (fromLeaTTaAtoms_applyClassSolution valuation atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end


/-- Native satisfaction maps into the established LeaTTa-valued observation
language by translating a valuation pointwise. -/
theorem heBindingSatisfied_of_specTypeBindingSatisfied
    {valuation : String → Atom} {bindings : Bindings}
    (hsatisfied : TypeBindingSatisfied valuation bindings) :
    HEBindingSatisfied (fun name => toLeaTTaAtom (valuation name))
      bindings := by
  constructor
  · intro name value hmem
    have h := hsatisfied.1 name value hmem
    exact (congrArg toLeaTTaAtom h).trans
      (toLeaTTaAtom_applyTypeValuation valuation value)
  · intro left right hmem
    exact congrArg toLeaTTaAtom (hsatisfied.2 left right hmem)

/-- Every model in the established LeaTTa-valued observation language
decodes to an honest native model of the same spec binding record. -/
theorem specTypeBindingSatisfied_of_heBindingSatisfied
    {valuation : String → Metta.Atom} {bindings : Bindings}
    (hsatisfied : HEBindingSatisfied valuation bindings) :
    TypeBindingSatisfied
      (fun name => fromLeaTTaAtom (valuation name)) bindings := by
  constructor
  · intro name value hmem
    have h := hsatisfied.1 name value hmem
    have := congrArg fromLeaTTaAtom h
    simpa [fromLeaTTaAtom_applyClassSolution] using this
  · intro left right hmem
    exact congrArg fromLeaTTaAtom (hsatisfied.2 left right hmem)

/-- For a pointwise translated native valuation, the established observation
language and native type-binding satisfaction coincide exactly. -/
theorem specTypeBindingSatisfied_iff_heBindingSatisfied_translated
    (valuation : String → Atom) (bindings : Bindings) :
    TypeBindingSatisfied valuation bindings ↔
      HEBindingSatisfied
        (fun name => toLeaTTaAtom (valuation name)) bindings := by
  constructor
  · exact heBindingSatisfied_of_specTypeBindingSatisfied
  · intro hsatisfied
    constructor
    · intro name value hmem
      apply Function.LeftInverse.injective fromLeaTTaAtom_toLeaTTaAtom
      rw [toLeaTTaAtom_applyTypeValuation]
      exact hsatisfied.1 name value hmem
    · intro left right hmem
      apply Function.LeftInverse.injective fromLeaTTaAtom_toLeaTTaAtom
      exact hsatisfied.2 left right hmem


end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

namespace Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Bindings.ScopeObservation

theorem class_value_support {bindings : Bindings} {key : String} {value : Atom}
    (stored : value∈bindings.classValues key) {name : String}
    (inside : name∈TypeSubst.typeVars value) : name∈specBindingVars bindings := by
  obtain ⟨storedKey,_,found⟩ := List.mem_filterMap.mp stored
  obtain ⟨before,after,eq,_⟩ := List.lookup_eq_some_iff.mp found
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨(storedKey,value), by rw [eq]; simp, List.mem_cons_of_mem _ inside⟩

theorem class_key_support {bindings : Bindings} {key : String} {value : Atom}
    (stored : value ∈ bindings.classValues key) : key ∈ specBindingVars bindings := by
  obtain ⟨storedKey, inClass, found⟩ := List.mem_filterMap.mp stored
  obtain ⟨before, after, assignments, _⟩ := List.lookup_eq_some_iff.mp found
  have present : (storedKey, value) ∈ bindings.assignments := by rw [assignments]; simp
  have keyPresent : storedKey ∈ specBindingVars bindings := by
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨(storedKey, value), present, List.mem_cons_self⟩
  by_cases same : key = storedKey
  · exact same ▸ keyPresent
  have reached := (EqualityClosure.mem_eqClass_iff_reachable.mp
    (EqualityClosure.mem_eqClassOrdered_iff.mp inClass)).symm
  apply reached.elim
  intro walk
  have supported := EqualityClosure.walk_support_subset_start_edgeNodes walk walk.end_mem_support
  rcases List.mem_cons.mp supported with sameKey | edge
  · exact (same sameKey).elim
  · simp only [EqualityClosure.edgeNodes, List.mem_flatMap] at edge
    obtain ⟨⟨left, right⟩, storedEdge, endpoint⟩ := edge
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨(left, right), storedEdge, endpoint⟩


end Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge


namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.SourceSupport
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge

private def constraintNames : Constraint → List String
  | .value key value => key::TypeSubst.typeVars value
  | .equality left right => [left,right]

private theorem in_typeVarsList {atoms : List Atom} {name : String} :
    name∈TypeSubst.typeVarsList atoms ↔ ∃ atom∈atoms,name∈TypeSubst.typeVars atom :=
  ⟨Freshness.exists_mem_of_mem_typeVarsList,
    fun ⟨_atom,member,inside⟩=>Freshness.typeVars_mem_typeVarsList_of_mem member name inside⟩

private theorem fresh_assign (bindings : Bindings) (key : String) (value : Atom)
    (empty : bindings.classValues key=[]) (name : String) :
    name∈specBindingVars (bindings.assign key value) ↔
      name∈specBindingVars bindings ∨ name=key ∨ name∈TypeSubst.typeVars value := by
  have unbound := LeaTTaBridge.isBound_eq_false_of_classValues_nil empty
  simp only [specBindingVars,Bindings.assign,unbound,Bool.false_eq_true,↓reduceIte,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append,
    List.mem_cons]
  tauto

private theorem added_equality (bindings : Bindings) (left right name : String) :
    name∈specBindingVars (bindings.addEquality left right) ↔
      name∈specBindingVars bindings ∨ name=left ∨ name=right := by
  simp only [specBindingVars,Bindings.addEquality,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem constraints_names (bindings : Bindings) (name : String) :
    (∃ c∈constraints bindings,name∈constraintNames c) ↔ name∈specBindingVars bindings := by
  simp only [constraints,List.mem_eraseDups]
  rw [← List.mem_flatMap]
  simp only [List.flatMap_append,List.flatMap_map]
  rfl

mutual
/-- Every independent matcher derivation retains the entire input support,
including a reflexive variable equation. Semantic solution equality alone
would not imply this syntactic freshness statement. -/
theorem match_support {left right : Atom} {out : Bindings}
    (derived : MatchRel equalityGroundedSemantic left right out) (name : String) :
    name∈specBindingVars out ↔ name∈TypeSubst.typeVars left ∨ name∈TypeSubst.typeVars right :=
  match derived with
  | .symSym _ _ => by simp [specBindingVars,Bindings.empty,TypeSubst.typeVars]
  | .varVar _ _ _ => by simp [specBindingVars,Bindings.empty,Bindings.addEquality,TypeSubst.typeVars]
  | .varNonVar _ _ => by
    simp [specBindingVars,Bindings.empty,Bindings.assign,Bindings.isBound,Bindings.lookup,TypeSubst.typeVars]
  | .nonVarVar _ _ => by
    simp [specBindingVars,Bindings.empty,Bindings.assign,Bindings.isBound,Bindings.lookup,TypeSubst.typeVars,or_comm]
  | .expression list _ => by
    simpa [specBindingVars,Bindings.empty,TypeSubst.typeVars] using list_support list name
  | .groundedLeftCustom _ _ shape _ => by
    obtain ⟨rfl,rfl⟩:=shape
    simp [specBindingVars,Bindings.empty,TypeSubst.typeVars]
  | .groundedRightCustom _ _ _ shape _ => by
    obtain ⟨rfl,rfl⟩:=shape
    simp [specBindingVars,Bindings.empty,TypeSubst.typeVars]
  | .groundedFallback impossible _ _ => False.elim (impossible trivial)
termination_by structural derived

theorem list_support {left right : List Atom} {seed out : Bindings}
    (derived : MatchListAccRel equalityGroundedSemantic left right seed out) (name : String) :
    name∈specBindingVars out ↔ name∈specBindingVars seed ∨
      name∈TypeSubst.typeVarsList left ∨ name∈TypeSubst.typeVarsList right :=
  match derived with
  | .nil => by simp [TypeSubst.typeVarsList]
  | .cons head merged tail => by
    rw [list_support tail name,merge_support merged name,match_support head name]
    simp only [TypeSubst.typeVarsList,List.mem_append]
    tauto
termination_by structural derived

theorem binding_support {seed out : Bindings} {key : String} {value : Atom}
    (derived : AddVarBindingRel equalityGroundedSemantic seed key value out) (name : String) :
    name∈specBindingVars out ↔ name∈specBindingVars seed ∨ name=key ∨ name∈TypeSubst.typeVars value :=
  match derived with
  | .fresh empty => fresh_assign seed key value empty name
  | .same values _ same => by
    subst value
    have stored := values.mem_iff.mp List.mem_cons_self
    have keyStored := FreshPrivateMerge.class_key_support stored
    have subset := @FreshPrivateMerge.class_value_support _ _ _ stored name
    constructor
    · exact Or.inl
    · rintro (old | rfl | occurs)
      · exact old
      · exact keyStored
      · exact subset occurs
  | .conflict values _ _ head merged => by
    have stored := values.mem_iff.mp List.mem_cons_self
    have keyStored := FreshPrivateMerge.class_key_support stored
    have subset := @FreshPrivateMerge.class_value_support _ _ _ stored name
    rw [merge_support merged name,match_support head name]
    constructor
    · rintro (old | first | added)
      · exact Or.inl old
      · exact Or.inl (subset first)
      · exact Or.inr (Or.inr added)
    · rintro (old | rfl | added)
      · exact Or.inl old
      · exact Or.inl keyStored
      · exact Or.inr (Or.inr added)
  | @AddVarBindingRel.reconcile _ _ _ _ first rest _ _ values _ matched merged => by
    have stored := values.mem_iff.mp List.mem_cons_self
    have keyStored := FreshPrivateMerge.class_key_support stored
    rw [merge_support merged name,list_support matched name]
    simp only [show specBindingVars Bindings.empty = [] from rfl, List.not_mem_nil, false_or]
    constructor
    · rintro (old | repeated | fromRight)
      · exact Or.inl old
      · obtain ⟨atom,member,occurs⟩:=in_typeVarsList.mp repeated
        have same : atom=first := (List.mem_replicate.mp member).2
        exact Or.inl (FreshPrivateMerge.class_value_support stored (same ▸ occurs))
      · obtain ⟨atom,member,occurs⟩:=in_typeVarsList.mp fromRight
        rcases List.mem_append.mp member with earlier | added
        · exact Or.inl (FreshPrivateMerge.class_value_support
            (values.mem_iff.mp (List.mem_cons_of_mem _ earlier)) occurs)
        · obtain rfl:=List.mem_singleton.mp added
          exact Or.inr (Or.inr occurs)
    · rintro (old | rfl | added)
      · exact Or.inl old
      · exact Or.inl keyStored
      · exact Or.inr (Or.inr (in_typeVarsList.mpr ⟨value,by simp,added⟩))
termination_by structural derived

theorem equality_support {seed out : Bindings} {left right : String}
    (derived : AddVarEqualityRel equalityGroundedSemantic seed left right out) (name : String) :
    name∈specBindingVars out ↔ name∈specBindingVars seed ∨ name=left ∨ name=right :=
  match derived with
  | .consistent _ _ => added_equality seed left right name
  | @AddVarEqualityRel.reconcile _ _ _ _ first rest _ _ values _ matched merged => by
    have stored := values.mem_iff.mp List.mem_cons_self
    rw [merge_support merged name,list_support matched name]
    simp only [show specBindingVars Bindings.empty = [] from rfl, List.not_mem_nil, false_or]
    constructor
    · rintro (old | repeated | fromRight)
      · exact (added_equality _ _ _ _).mp old
      · obtain ⟨atom,member,occurs⟩:=in_typeVarsList.mp repeated
        have same : atom=first := (List.mem_replicate.mp member).2
        exact (added_equality _ _ _ _).mp
          (FreshPrivateMerge.class_value_support stored (same ▸ occurs))
      · obtain ⟨atom,member,occurs⟩:=in_typeVarsList.mp fromRight
        exact (added_equality _ _ _ _).mp (FreshPrivateMerge.class_value_support
          (values.mem_iff.mp (List.mem_cons_of_mem _ member)) occurs)
    · exact fun prior=>Or.inl ((added_equality _ _ _ _).mpr prior)
termination_by structural derived

theorem constraints_support {seed out : Bindings} {items : List Constraint}
    (derived : MergeConstraintsRel equalityGroundedSemantic seed items out) (name : String) :
    name∈specBindingVars out ↔ name∈specBindingVars seed ∨
      ∃ item∈items,name∈constraintNames item :=
  match derived with
  | .nil => by simp
  | .value added rest => by
    rw [constraints_support rest name,binding_support added name]
    simp only [List.mem_cons,exists_eq_or_imp,constraintNames,List.mem_cons]
    tauto
  | .equality added rest => by
    rw [constraints_support rest name,equality_support added name]
    simp only [List.mem_cons,exists_eq_or_imp,constraintNames,List.mem_cons,List.not_mem_nil,or_false]
    tauto
termination_by structural derived

theorem merge_support {left right out : Bindings}
    (derived : MergeRel equalityGroundedSemantic left right out) (name : String) :
    name∈specBindingVars out ↔ name∈specBindingVars left ∨ name∈specBindingVars right :=
  match derived with
  | .mk order folded => by
    rw [constraints_support folded name]
    simp only [order.mem_iff,constraints_names]
termination_by structural derived
end

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection.SourceSupport


namespace Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.MergeRel
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation Spec.Type.RuntimeRefinement LeaTTaTypeConformance

/-- Independent merging preserves exactly the conjunction and complete support
of its inputs, without any executable-query or representative premise. -/
theorem bindingSourceAgreement {left right output : Bindings}
    (derived : MergeRel equalityGroundedSemantic left right output) :
    BindingSourceAgreement output
      ⟨left.assignments ++ right.assignments, left.equalities ++ right.equalities⟩ := by
  constructor
  · intro valuation
    rw [bindingSatisfied_append_iff]
    simp only [specTypeBindingSatisfied_iff_heBindingSatisfied_translated]
    exact Spec.Match.SolutionTheory.mergeRel_solution_iff derived _
  · intro name
    rw [mem_specBindingVars_append]
    exact QueryBindingProjection.SourceSupport.merge_support derived name

theorem logicalMerge {left right output : Bindings}
    (derived : MergeRel equalityGroundedSemantic left right output)
    (model : ∃ valuation : String → Atom, TypeBindingSatisfied valuation output) :
    LogicalMergeRel left right output := ⟨derived.bindingSourceAgreement, model⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.MergeRel
