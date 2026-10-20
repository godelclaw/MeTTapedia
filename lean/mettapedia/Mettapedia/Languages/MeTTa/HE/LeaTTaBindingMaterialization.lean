import Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
import Mettapedia.Languages.MeTTa.HE.ScopedEquationQuery
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha
import Mettapedia.Languages.MeTTa.HE.LeaTTaQueryObservationalAnchor
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# From binding observations to materialized invocation

A reachable runtime binding record has its own canonical resolver as a
model. Consequently, equality in every model determines equal instantiated
syntax. The existing minimal interpreter applies that instantiation before
native dispatch; its invocation operation therefore respects the observation.
This is stronger than a raw dispatch relation on unresolved arguments.
The concrete LeaTTa binding projection, its paired query invariant and the
materialization comparisons live here above the independent HE readout laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaTypeConformance

/-- The actual runtime resolver is one of the models quantified by the
specification's binding observation. Its satisfaction follows from the
existing reachable-state invariant. -/
theorem LeaQueryOpBindingInvariant.materializes_observation
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    {left right : Atom}
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation left right) :
    Metta.instantiate runtime (encodeModelAtom left) =
      Metta.instantiate runtime (encodeModelAtom right) := by
  rw [← applyClassSolution_lea_eq_instantiate,
    ← applyClassSolution_lea_eq_instantiate]
  exact observed (leaClassSolution runtime)
    ((invariant.solutionTheory _).mpr invariant.runtime.canonical.1)

/-- Closed observed data has exactly its original syntax after actual
instantiation, rather than merely an equal observation in the carried frame. -/
theorem LeaQueryOpBindingInvariant.materializes_closed
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    {atom expected : Atom} (closed : (encodeModelAtom expected).vars = [])
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation atom expected) :
    Metta.instantiate runtime (encodeModelAtom atom) = encodeModelAtom expected := by
  rw [invariant.materializes_observation observed,
    ← applyClassSolution_lea_eq_instantiate]
  calc
    _ = applyClassSolution (fun name => .var name) (encodeModelAtom expected) := by
      apply applyClassSolution_congr_on_atom_vars
      intro name member
      simp only [closed, List.not_mem_nil] at member
    _ = _ := Spec.Match.ModelTheory.applyClassSolution_identity _

/-- Actual `evalOp` substitutes bindings before inspecting the head or
arguments. Equality after this substitution is an invocation congruence. -/
theorem evalOp_eq_of_instantiate_eq
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) (bindings : Metta.Bindings)
    {left right : Metta.Atom}
    (same : Metta.instantiate bindings left = Metta.instantiate bindings right) :
    Metta.Minimal.evalOp environment state continuation left bindings =
      Metta.Minimal.evalOp environment state continuation right bindings := by
  unfold Metta.Minimal.evalOp
  rw [same]

/-- Binding observations may be used at the actual interpreter's invocation
boundary, because that boundary materializes the arguments first. -/
theorem LeaQueryOpBindingInvariant.evalOp_observation
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) {left right : Atom}
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation left right) :
    Metta.Minimal.evalOp environment state continuation (encodeModelAtom left) runtime =
      Metta.Minimal.evalOp environment state continuation (encodeModelAtom right) runtime :=
  evalOp_eq_of_instantiate_eq environment state continuation runtime
    (invariant.materializes_observation observed)

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

namespace Mettapedia.Languages.MeTTa.HE.QueryBindingProjection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge LeaTTaTypeConformance LeaTTaSpecConformance
open Spec.Eval.Steps
open Spec.Type.Presentation (TypeSubst)
open Spec.Type.Presentation.BindingTheory (BindingMaterializationRel)

def project (bindings : Metta.Bindings) : Bindings :=
  ⟨bindings.filterMap (fun relation => match relation with
      | .val name value => some (name, decodeModelAtom value)
      | .eq _ _ => none), leaEqualityEdges bindings⟩

theorem assignment_mem_iff (bindings : Metta.Bindings) (name : String) (value : Atom) :
    (name, value) ∈ (project bindings).assignments ↔
      ∃ original, Metta.BindingRel.val name original ∈ bindings ∧ decodeModelAtom original = value := by
  constructor
  · intro member
    obtain ⟨relation, relationMember, converted⟩ := List.mem_filterMap.mp member
    cases relation with
    | val key original =>
        simp only [Option.some.injEq, Prod.mk.injEq] at converted
        obtain ⟨rfl, rfl⟩ := converted
        exact ⟨original, relationMember, rfl⟩
    | eq left right => simp at converted
  · rintro ⟨original, member, rfl⟩
    exact List.mem_filterMap.mpr ⟨.val name original, member, rfl⟩

theorem equality_mem_iff (bindings : Metta.Bindings) (left right : String) :
    (left, right) ∈ (project bindings).equalities ↔ .eq left right ∈ bindings :=
  mem_leaEqualityEdges_iff

/-- Complete solution-theory correspondence is derived from concrete fields. -/
theorem solutionTheory (bindings : Metta.Bindings) (image : LeaBindingsHEImage bindings) :
    LeaBindingSolutionTheoryEquiv (project bindings) bindings := by
  intro valuation
  constructor
  · intro satisfied
    constructor
    · intro key original member
      have assignment := satisfied.1 key (decodeModelAtom original)
        ((assignment_mem_iff bindings key _).mpr ⟨original, member, rfl⟩)
      rw [encodeModelAtom_decodeModelAtom_of_heImage (image key original member)] at assignment
      exact assignment
    · intro left right member
      exact satisfied.2 left right ((equality_mem_iff bindings left right).mpr member)
  · intro satisfied
    constructor
    · intro key value member
      obtain ⟨original, originalMember, rfl⟩ := (assignment_mem_iff bindings key value).mp member
      rw [encodeModelAtom_decodeModelAtom_of_heImage (image key original originalMember)]
      exact satisfied.1 key original originalMember
    · intro left right member
      exact satisfied.2 left right ((equality_mem_iff bindings left right).mp member)

theorem assignmentsNonVariable (bindings : Metta.Bindings)
    (image : LeaBindingsHEImage bindings) (normalized : LeaAssignmentsNonVariable bindings) :
    HEAssignmentsNonVariable (project bindings) := by
  intro key target member
  obtain ⟨original, originalMember, decoded⟩ := (assignment_mem_iff bindings key _).mp member
  have translated := congrArg encodeModelAtom decoded
  rw [encodeModelAtom_decodeModelAtom_of_heImage (image key original originalMember)] at translated
  exact normalized key target (by simpa only [encodeModelAtom, translated] using originalMember)

theorem paired (bindings : Metta.Bindings) (image : LeaBindingsHEImage bindings)
    (runtime : LeaRuntimeBindingInvariant bindings) :
    ScopedEquationQuery.BindingInvariant (project bindings) bindings :=
  ⟨⟨solutionTheory bindings image,
      assignmentsNonVariable bindings image runtime.assignmentsNonVariable, runtime⟩, image⟩

theorem paired_empty : ScopedEquationQuery.BindingInvariant (project []) [] :=
  paired [] leaBindingsHEImage_empty leaRuntimeBindingInvariant_empty

theorem value_name_mem {bindings : Metta.Bindings} {key name : String} {value : Metta.Atom}
    (member : .val key value ∈ bindings) (occurrence : name = key ∨ name ∈ value.vars) :
    name ∈ bindings.vars := by
  simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨.val key value, member, by simpa only [List.mem_cons] using occurrence⟩

theorem equality_name_mem {bindings : Metta.Bindings} {left right name : String}
    (member : .eq left right ∈ bindings) (occurrence : name = left ∨ name = right) :
    name ∈ bindings.vars := by
  simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨.eq left right, member, by simpa using occurrence⟩

/-- The projected presentation adds no variable outside the concrete record. -/
theorem binding_name_mem {bindings : Metta.Bindings} {name : String}
    (image : LeaBindingsHEImage bindings)
    (member : name ∈ EquationScope.bindingNames (project bindings)) : name ∈ bindings.vars := by
  simp only [EquationScope.bindingNames, List.mem_append, List.mem_flatMap] at member
  rcases member with assignment | equality
  · obtain ⟨⟨key, value⟩, stored, occurrence⟩ := assignment
    obtain ⟨original, originalMember, rfl⟩ := (assignment_mem_iff bindings key value).mp stored
    simp only [List.mem_cons] at occurrence
    rw [encodeModelAtom_decodeModelAtom_of_heImage (image key original originalMember)] at occurrence
    exact value_name_mem originalMember occurrence
  · obtain ⟨⟨left, right⟩, stored, occurrence⟩ := equality
    apply equality_name_mem ((equality_mem_iff bindings left right).mp stored)
    simpa using occurrence

/-- Each query output provides a logical derivation and a constructed next
projected state with the same complete solution theory as that derivation. -/
theorem ruleResults_sound {space : Space} {live : List Atom} {query lhs rhs : Atom}
    {incoming : Metta.Bindings} {counter : Nat} {hit : ScopedEquationQuery.Hit}
    (stored : .expression [.symbol "=", lhs, rhs] ∈ space.atoms)
    (image : LeaBindingsHEImage incoming) (runtime : LeaRuntimeBindingInvariant incoming)
    (member : hit ∈ ScopedEquationQuery.ruleResults live query (project incoming) incoming counter lhs rhs) :
    ∃ output,
      EquationQueryCandidateRel space live query (project incoming) hit.value output ∧
        ScopedEquationQuery.BindingInvariant (project hit.bindings) hit.bindings ∧
        ∀ valuation,
          HEBindingSatisfied valuation output ↔ HEBindingSatisfied valuation (project hit.bindings) := by
  obtain ⟨output, derivation, next⟩ :=
    ScopedEquationQuery.ruleResults_sound stored (paired incoming image runtime) member
  have projectedNext := paired hit.bindings next.image next.semantic.runtime
  refine ⟨output, derivation, projectedNext, ?_⟩
  intro valuation
  exact (next.semantic.solutionTheory valuation).trans
    (projectedNext.semantic.solutionTheory valuation).symm


/-! ## Separate executable query-binding projection -/

/-- The operational observation square for two concrete binding backends.
Logical theory equivalence transports the satisfying model; both actual
application algorithms preserve its observation at any HE fuel. -/
theorem application_observation {spec : Bindings} {native : Metta.Bindings}
    (equivalent : LeaBindingSolutionTheoryEquiv spec native)
    {valuation : String → Metta.Atom} (satisfied : HEBindingSatisfied valuation spec)
    (atom : Atom) (fuel : Nat) :
    applyClassSolution valuation (encodeModelAtom (spec.applyFull atom fuel)) =
      applyClassSolution valuation (Metta.instantiate native (encodeModelAtom atom)) :=
  (applyFull_semantically_inert satisfied atom fuel).trans
    (instantiate_semantically_inert ((equivalent valuation).mp satisfied) (encodeModelAtom atom)).symm

/-- Concrete projection earns the application observation square directly
from its field-level solution-theory theorem. -/
theorem projected_application_observation (bindings : Metta.Bindings)
    (image : LeaBindingsHEImage bindings) {valuation : String → Metta.Atom}
    (satisfied : HEBindingSatisfied valuation (project bindings)) (atom : Atom) (fuel : Nat) :
    applyClassSolution valuation (encodeModelAtom ((project bindings).applyFull atom fuel)) =
      applyClassSolution valuation (Metta.instantiate bindings (encodeModelAtom atom)) :=
  application_observation (solutionTheory bindings image) satisfied atom fuel


/-- Reachable native bindings turn model observation into equality after the
actual materialization boundary, reusing the existing canonical-model law. -/
theorem application_materialization {spec : Bindings} {native : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec native) (atom : Atom) (fuel : Nat) :
    Metta.instantiate native (encodeModelAtom (spec.applyFull atom fuel)) =
      Metta.instantiate native (encodeModelAtom atom) :=
  invariant.materializes_observation fun _ satisfied => applyFull_semantically_inert satisfied atom fuel

/-- The actual minimal invocation substitutes before dispatch. Consequently
it respects bounded HE application even when the unmaterialized syntax has a
different shape. No congruence of arbitrary raw dispatch is asserted. -/
theorem application_invocation {spec : Bindings} {native : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec native)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) (atom : Atom) (fuel : Nat) :
    Metta.Minimal.evalOp environment state continuation
      (encodeModelAtom (spec.applyFull atom fuel)) native =
    Metta.Minimal.evalOp environment state continuation (encodeModelAtom atom) native :=
  evalOp_eq_of_instantiate_eq environment state continuation native
    (application_materialization invariant atom fuel)

/-! ## Independent normal presentations at materialized boundaries -/

/-- An independently normal finite presentation of the complete binding
theory has the same materialized shape as the actual principal runtime
resolver, up to a renaming of residual variables. -/
theorem normal_materialization_alpha {spec : Bindings} {native : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec native)
    {presentation : TypeSubst} (normal : presentation.Normal)
    (exactTheory : ∀ valuation,
      Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation spec)
    (atom : Atom) :
    Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel (presentation.apply atom)
      (decodeModelAtom (Metta.instantiate native (encodeModelAtom atom))) :=
  LeaTTaTypePresentationPrincipalAlpha.observedTypeAlpha_of_bindingTheory normal
    exactTheory invariant.solutionTheory invariant.runtime atom

/-- A reachable paired binding frame earns source satisfiability from its
actual canonical runtime model. No normal source-record format is assumed. -/
theorem binding_theory_satisfiable {spec : Bindings} {native : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec native) :
    ∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation spec := by
  have model : HEBindingSatisfied (leaClassSolution native) spec :=
    (invariant.solutionTheory _).mpr invariant.runtime.canonical.1
  exact ⟨_, specTypeBindingSatisfied_of_heBindingSatisfied model⟩

/-- A reachable spec/runtime pair earns an independent normal finite
presentation from the spec equations themselves. Its actual materialization
comparison is then derived from principality, rather than assumed as a field
or defined by the runtime result. -/
theorem exists_normal_materialization {spec : Bindings} {native : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec native) :
    ∃ presentation : TypeSubst,
      presentation.Normal ∧
      (∀ valuation, Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation spec) ∧
      ∀ atom : Atom,
        Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel (presentation.apply atom)
          (decodeModelAtom (Metta.instantiate native (encodeModelAtom atom))) := by
  obtain ⟨presentation, fold⟩ :=
    Spec.Type.Presentation.BindingTheory.exists_binding_presentation (binding_theory_satisfiable invariant)
  exact ⟨presentation, fold.bindingTheory.1, fold.bindingTheory.2,
    normal_materialization_alpha invariant fold.bindingTheory.1 fold.bindingTheory.2⟩

/-- Every independently generated finished-operand materialization agrees
with actual reachable runtime materialization up to residual-variable renaming.
The source relation itself has no native resolver premise. -/
theorem binding_materialization_alpha {spec : Bindings} {native : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec native) {raw normalized : Atom}
    (materialized : BindingMaterializationRel spec raw normalized) :
    Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel normalized
      (decodeModelAtom (Metta.instantiate native (encodeModelAtom raw))) := by
  obtain ⟨presentation, fold, rfl⟩ := materialized
  exact normal_materialization_alpha invariant fold.bindingTheory.1 fold.bindingTheory.2 raw

/-- Construct the independent operand relation from the actual paired frame,
then derive its native comparison. The relation is not defined by the native
result, and no correspondence certificate is supplied by the caller. -/
theorem exists_binding_materialization {spec : Bindings} {native : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec native) (raw : Atom) :
    ∃ normalized, BindingMaterializationRel spec raw normalized ∧
      Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel normalized
        (decodeModelAtom (Metta.instantiate native (encodeModelAtom raw))) := by
  obtain ⟨normalized, materialized⟩ :=
    BindingMaterializationRel.exists_of_satisfiable (binding_theory_satisfiable invariant) raw
  exact ⟨normalized, materialized, binding_materialization_alpha invariant materialized⟩

/-- Projection of the current concrete binding record earns the same
source-generated handler materialization at every finite operand depth. -/
theorem projected_binding_materialization (native : Metta.Bindings)
    (image : LeaBindingsHEImage native) (runtime : LeaRuntimeBindingInvariant native) (raw : Atom) :
    ∃ normalized, BindingMaterializationRel (project native) raw normalized ∧
      Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel normalized
        (decodeModelAtom (Metta.instantiate native (encodeModelAtom raw))) :=
  exists_binding_materialization (paired native image runtime).semantic raw

/-- The concrete query projection constructs the semantic invariant used by
the normal presentation theorem. No presentation or correspondence is an
extra caller-supplied certificate. -/
theorem projected_normal_materialization (native : Metta.Bindings)
    (image : LeaBindingsHEImage native) (runtime : LeaRuntimeBindingInvariant native) :
    ∃ presentation : TypeSubst,
      presentation.Normal ∧
      (∀ valuation, Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation (project native)) ∧
      ∀ atom : Atom,
        Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel (presentation.apply atom)
          (decodeModelAtom (Metta.instantiate native (encodeModelAtom atom))) :=
  exists_normal_materialization (paired native image runtime).semantic

namespace Controls

private def aliased : Metta.Bindings := [.eq "x" "y", .val "y" (.sym "answer")]
private def model (name : String) : Metta.Atom :=
  if name = "x" ∨ name = "y" then .sym "answer" else .var name

private theorem aliased_image : LeaBindingsHEImage aliased := by
  intro name value member
  have same : name = "y" ∧ value = .sym "answer" := by simpa [aliased] using member
  obtain ⟨rfl, rfl⟩ := same
  exact leaAtomHEImage_sym "answer"

private theorem model_satisfies : HEBindingSatisfied model (project aliased) := by
  constructor
  · intro name value member
    have same : name = "y" ∧ value = .symbol "answer" := by
      simpa only [project, aliased, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton, Prod.mk.injEq, decodeModelAtom] using member
    obtain ⟨rfl, rfl⟩ := same
    simp [model, encodeModelAtom, applyClassSolution]
  · intro name other member
    have same : name = "x" ∧ other = "y" := by
      simpa only [project, aliased, leaEqualityEdges, List.mem_singleton, Prod.mk.injEq] using member
    obtain ⟨rfl, rfl⟩ := same
    simp [model]

/-- A concrete nontrivial equality class earns observation agreement for
arbitrary atoms, including every finite nesting, at every application fuel. -/
theorem alias_application_observed (atom : Atom) (fuel : Nat) :
    applyClassSolution model (encodeModelAtom ((project aliased).applyFull atom fuel)) =
      applyClassSolution model (Metta.instantiate aliased (encodeModelAtom atom)) :=
  projected_application_observation aliased aliased_image model_satisfies atom fuel

private def direct : Metta.Bindings := [.val "x" (.sym "answer")]

/-- Equal model observations do not make insufficient-fuel syntax into a
fully materialized structural operand. -/
theorem insufficient_fuel_is_not_materialization :
    (project direct).applyFull (.var "x") 0 = .var "x" ∧
    decodeModelAtom (Metta.instantiate direct (.var "x")) = .symbol "answer" ∧
    (project direct).applyFull (.var "x") 0 ≠
      decodeModelAtom (Metta.instantiate direct (.var "x")) := by
  have materialized := Metta.instantiate_singleton_val_var_of_not_mem "x" (.sym "answer")
    (by simp [Metta.Atom.vars])
  have decoded : decodeModelAtom (Metta.instantiate direct (.var "x")) = .symbol "answer" := by
    rw [show direct = [.val "x" (.sym "answer")] from rfl, materialized]
    rfl
  refine ⟨rfl, decoded, ?_⟩
  rw [decoded]
  change (Atom.var "x") ≠ .symbol "answer"
  decide

private def functionValue : Atom :=
  .expression [.symbol "function", .expression [.symbol "return", .symbol "answer"]]
private def functionBindings : Metta.Bindings := [.val "f" (encodeModelAtom functionValue)]

/-- Function dispatch is a finer observer than model equality: an unresolved
variable and its materialized function block have different dispatch shapes. -/
theorem observation_does_not_authorize_function_dispatch :
    (project functionBindings).applyFull (.var "f") 0 = .var "f" ∧
    decodeModelAtom (Metta.instantiate functionBindings (.var "f")) = functionValue ∧
    getMetaType ((project functionBindings).applyFull (.var "f") 0) = Atom.variableType ∧
    getMetaType (decodeModelAtom (Metta.instantiate functionBindings (.var "f"))) = Atom.expressionType := by
  have fresh : "f" ∉ (encodeModelAtom functionValue).vars := by
    simp [functionValue, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars]
  have materialized := Metta.instantiate_singleton_val_var_of_not_mem "f"
    (encodeModelAtom functionValue) fresh
  simp only [functionBindings, materialized, decodeModelAtom_encodeModelAtom, Bindings.applyFull]
  simp [functionValue, getMetaType]

private theorem function_image : LeaBindingsHEImage functionBindings := by
  intro name value member
  have same : name = "f" ∧ value = encodeModelAtom functionValue := by
    simpa [functionBindings] using member
  obtain ⟨rfl, rfl⟩ := same
  exact leaAtomHEImage_encodeModelAtom functionValue

private theorem function_runtime : LeaRuntimeBindingInvariant functionBindings := by
  have noFloat : LeaBindingsNoFloat functionBindings := by
    intro name value member
    have same : name = "f" ∧ value = encodeModelAtom functionValue := by
      simpa [functionBindings] using member
    obtain ⟨rfl, rfl⟩ := same
    exact encodeModelAtom_noFloat functionValue
  have merged : Metta.Bindings.merge [] functionBindings = [functionBindings] := by rfl
  have loopFree : functionBindings.hasLoop = false := by
    exact Metta.Bindings.hasLoop_singleton_val_of_not_mem "f" (encodeModelAtom functionValue)
      (by simp [functionValue, encodeModelAtom, encodeModelAtoms, Metta.Atom.vars])
  exact leaRuntimeBindingInvariant_empty.merge noFloat
    (by change functionBindings ∈ Metta.Bindings.merge [] functionBindings
        rw [merged]; exact List.mem_singleton_self _) loopFree

/-- The independent one-pass presentation exposes the function hidden by an
unresolved alias. Its exact source theory and runtime principality are earned
from concrete fields and the actual merge, rather than supplied as premises. -/
theorem bound_function_has_normal_source_presentation :
    let presentation : TypeSubst := [("f", functionValue)]
    presentation.Normal ∧
      (∀ valuation, Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation (project functionBindings)) ∧
      presentation.apply (.var "f") = functionValue ∧
      Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel
        (presentation.apply (.var "f"))
        (decodeModelAtom (Metta.instantiate functionBindings (.var "f"))) := by
  intro presentation
  have normal : presentation.Normal := by
    simp [presentation, functionValue, TypeSubst.Normal, TypeSubst.keys,
      TypeSubst.typeVars, TypeSubst.typeVarsList]
  have theory : ∀ valuation,
      Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation presentation ↔
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation (project functionBindings) := by
    intro valuation
    simp [Spec.Type.Presentation.Theory.TypeSubstSatisfied,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied, presentation, project, functionBindings,
      decodeModelAtom_encodeModelAtom, leaEqualityEdges]
  have image := function_image
  have exposed : presentation.apply (.var "f") = functionValue := by
    simp [presentation, TypeSubst.apply, TypeSubst.lookup]
  exact ⟨normal, theory, exposed,
    normal_materialization_alpha (paired functionBindings image function_runtime).semantic
      normal theory (.var "f")⟩

/-- The actual valid native function-alias frame also has the independent
finished-operand relation, with the same source binding projection and actual
principal materialization. This is not an unresolved-syntax dispatch claim. -/
theorem bound_function_has_materialization_derivation :
    BindingMaterializationRel (project functionBindings) (.var "f") functionValue ∧
    Spec.Type.Presentation.Alpha.ObservedTypeAlphaRel functionValue
      (decodeModelAtom (Metta.instantiate functionBindings (.var "f"))) ∧
    (Atom.var "f") ≠ functionValue := by
  have materialized : BindingMaterializationRel (project functionBindings) (.var "f") functionValue := by
    have independent := BindingMaterializationRel.single_assignment "f" functionValue (.var "f")
      (by simp [functionValue, TypeSubst.typeVars, TypeSubst.typeVarsList])
    simpa [project, functionBindings, leaEqualityEdges, decodeModelAtom_encodeModelAtom,
      TypeSubst.apply, TypeSubst.lookup] using independent
  exact ⟨materialized,
    binding_materialization_alpha (paired functionBindings function_image function_runtime).semantic materialized,
    by simp [functionValue]⟩

end Controls

end Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
