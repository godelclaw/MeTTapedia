import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Gluing
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Semantics
import Mettapedia.GSLT.Scope.Interaction
import Mettapedia.GSLT.Logic.ObserverPresheaf
import Mettapedia.GSLT.Scope.Holonomy
import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.OSLF.Syntax.FreeBindingEquationModel

/-!
# Semantic gluing over a shared binding signature

Modules contribute contextual equation schemas over one fixed binding
signature. Their models are the existing substitution-compatible equation
models. Restriction retains the complete binding algebra, including its
carrier, operators and substitution. Agreement at the shared ancestor
therefore retains these parameters even when that ancestor has no equations.

This is the equation-presentation boundary. Signature-changing elaboration,
rewrites and runtime realization have separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluing

open Mettapedia.OSLF.Binding
open Mettapedia.Logic.TheoryModel
open Mettapedia.GSLT.Core.NonFactorization

universe u

variable {Origin Label Body : Type}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]
  {S : Signature} {M : List (MetaArity S)}

/-- The finite declaration list supplies schemas to the established model
interface. Repetition and enumeration order do not change satisfaction. -/
noncomputable def equations (schema : Body → EqAxiom S M) (p : Presentation Origin Label Body) :
    List (EqAxiom S M) :=
  p.val.toList.map (fun entry => schema entry.body)

/-- List satisfaction is pointwise contextual schema satisfaction. -/
theorem satisfies_iff_members (A : BindingCloneAlgebra.Algebra.{u} S)
    (equations : List (EqAxiom S M)) :
    BindingEquationInterpretation.Satisfies A equations ↔
      ∀ equation ∈ equations, BindingEquationInterpretation.Satisfies A [equation] := by
  constructor
  · intro satisfies equation member
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
    intro singletonIndex Γ Δ body ambient ordinary
    have indexZero : singletonIndex = 0 := Fin.eq_zero singletonIndex
    subst singletonIndex
    exact satisfies i body ambient ordinary
  · intro singles i Γ Δ body ambient ordinary
    exact singles (equations.get i) (List.get_mem equations i) 0 body ambient ordinary

/-- Actual equation satisfaction, including arbitrary captured contextual
metavariables and independent ambient and ordinary environments. -/
def equationSat (schema : Body → EqAxiom S M)
    (A : BindingCloneAlgebra.Algebra.{u} S) (body : Body) : Prop :=
  BindingEquationInterpretation.Satisfies A [schema body]

theorem satisfies_iff_models (schema : Body → EqAxiom S M)
    (A : BindingCloneAlgebra.Algebra.{u} S) (p : Presentation Origin Label Body) :
    BindingEquationInterpretation.Satisfies A (equations schema p) ↔
      A ∈ models (equationSat schema) (bodyTheory p) := by
  rw [satisfies_iff_members]
  constructor
  · intro satisfies body member
    obtain ⟨entry, member, rfl⟩ := member
    apply satisfies
    simp only [equations, List.mem_map, Finset.mem_toList]
    exact ⟨entry, member, rfl⟩
  · intro satisfies equation member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    exact satisfies ⟨entry, Finset.mem_toList.mp entryMember, rfl⟩

/-- Reuse the binder-aware equation model; no parallel interpretation type. -/
abbrev Model (schema : Body → EqAxiom S M) (p : Presentation Origin Label Body) :=
  FreeBindingEquationModel.Model.{u} (equations schema p)

theorem satisfies_join (schema : Body → EqAxiom S M)
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    BindingEquationInterpretation.Satisfies A (equations schema r) ↔
      BindingEquationInterpretation.Satisfies A (equations schema p) ∧
        BindingEquationInterpretation.Satisfies A (equations schema q) := by
  simp only [satisfies_iff_models]
  rw [models_join (equationSat schema) joined]
  rfl

/-- The reduct of a model along an actual declaration inclusion. -/
def restrict (schema : Body → EqAxiom S M)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val)
    (model : Model.{u} schema q) : Model.{u} schema p where
  algebra := model.algebra
  satisfies := by
    apply (satisfies_iff_models schema model.algebra p).mpr
    intro body member
    obtain ⟨entry, member, rfl⟩ := member
    exact (satisfies_iff_models schema model.algebra q).mp model.satisfies
      ⟨entry, included member, rfl⟩

/-- Equation-model equality is determined by the complete binding algebra. -/
theorem model_ext {schema : Body → EqAxiom S M} {p : Presentation Origin Label Body}
    {first second : Model.{u} schema p} (same : first.algebra = second.algebra) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

theorem restrict_algebra (schema : Body → EqAxiom S M)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val)
    (model : Model.{u} schema q) : (restrict schema included model).algebra = model.algebra := rfl

/-- The free equation quotient supplies a model of every unrestricted
equation presentation. Failure of semantic existence must therefore state
the admitted carrier or interpretation scope. -/
theorem equation_model_exists (schema : Body → EqAxiom S M)
    (p : Presentation Origin Label Body) : Nonempty (Model.{0} schema p) :=
  ⟨FreeBindingEquationModel.presented (equations schema p)⟩

/-- Adding equations induces the canonical map between the established
quotient binding algebras. It preserves the full semantic substitution. -/
noncomputable def quotientInclusion (schema : Body → EqAxiom S M)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val) :
    FreeBindingClone.Hom
      (FreeBindingEquationModel.presented (equations schema p)).algebra
      (FreeBindingEquationModel.presented (equations schema q)).algebra :=
  FreeBindingEquationModel.interpretHom
    (restrict schema included (FreeBindingEquationModel.presented (equations schema q)))

/-- The quotient comparison and model restriction form a commuting
interpretation square, earned by the existing quotient initiality theorem. -/
theorem interpretation_restrict (schema : Body → EqAxiom S M)
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val)
    (model : Model.{u} schema q) :
    FreeBindingClone.Hom.comp (quotientInclusion schema included)
        (FreeBindingEquationModel.interpretHom model) =
      FreeBindingEquationModel.interpretHom (restrict schema included model) :=
  FreeBindingEquationModel.hom_unique (restrict schema included model) _

theorem quotientInclusion_self (schema : Body → EqAxiom S M)
    (p : Presentation Origin Label Body) :
    quotientInclusion schema (show p.val ⊆ p.val from Finset.Subset.refl p.val) =
      FreeBindingClone.Hom.id
        (FreeBindingEquationModel.presented (equations schema p)).algebra := by
  exact (FreeBindingEquationModel.hom_unique
    (restrict schema (Finset.Subset.refl p.val)
      (FreeBindingEquationModel.presented (equations schema p))) _).symm

theorem quotientInclusion_comp (schema : Body → EqAxiom S M)
    {p q r : Presentation Origin Label Body} (first : p.val ⊆ q.val) (second : q.val ⊆ r.val) :
    FreeBindingClone.Hom.comp (quotientInclusion schema first) (quotientInclusion schema second) =
      quotientInclusion schema (Finset.Subset.trans first second) :=
  FreeBindingEquationModel.hom_unique
    (restrict schema (Finset.Subset.trans first second)
      (FreeBindingEquationModel.presented (equations schema r))) _

/-- Agreement at any common ancestor retains the full shared parameters.
In particular, an equation-free ancestor still retains the signature algebra. -/
theorem ancestor_agreement_iff (schema : Body → EqAxiom S M)
    {ancestor p q : Presentation Origin Label Body}
    (left : ancestor.val ⊆ p.val) (right : ancestor.val ⊆ q.val)
    (first : Model.{u} schema p) (second : Model.{u} schema q) :
    restrict schema left first = restrict schema right second ↔
      first.algebra = second.algebra :=
  ⟨fun equal => congrArg (fun model : Model schema ancestor => model.algebra) equal,
    fun equal => model_ext equal⟩

/-- The compatible pairs use the existing models and equality of their
complete shared binding algebra, not equality of a selected readout. -/
abbrev CompatibleModels (schema : Body → EqAxiom S M)
    (p q : Presentation Origin Label Body) :=
  {pair : Model.{u} schema p × Model.{u} schema q // pair.1.algebra = pair.2.algebra}

def glueModel (schema : Body → EqAxiom S M)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (pair : CompatibleModels.{u} schema p q) : Model.{u} schema r where
  algebra := pair.val.1.algebra
  satisfies := (satisfies_join schema pair.val.1.algebra joined).mpr
    ⟨pair.val.1.satisfies, pair.property.symm ▸ pair.val.2.satisfies⟩

def splitModel (schema : Body → EqAxiom S M)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (model : Model.{u} schema r) : CompatibleModels.{u} schema p q :=
  ⟨(restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left) model,
      restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right) model), rfl⟩

/-- Every model of the joined equations is exactly one compatible pair of
component models. Both inverse laws retain the entire binding algebra. -/
def modelJoinEquiv (schema : Body → EqAxiom S M)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    Model.{u} schema r ≃ CompatibleModels.{u} schema p q where
  toFun := splitModel schema joined
  invFun := glueModel schema joined
  left_inv := fun _ => model_ext rfl
  right_inv := fun pair => Subtype.ext
    (Prod.ext (model_ext rfl) (model_ext pair.property))

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The model reduct square is a genuine pullback, for any declared common
ancestor. It is the contravariant semantic counterpart of declaration joining. -/
theorem modelJoin_isPullback (schema : Body → EqAxiom S M)
    {ancestor p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (left : ancestor.val ⊆ p.val) (right : ancestor.val ⊆ q.val) :
    IsPullback
      (↾(restrict.{u} schema
        ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left)))
      (↾(restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right)))
      (↾(restrict schema left)) (↾(restrict schema right)) := by
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext model
    exact model_ext rfl
  · intro first second equal
    exact model_ext (congrArg (fun model : Model schema p => model.algebra) equal.1)
  · intro first second equal
    have same := (ancestor_agreement_iff schema left right first second).mp equal
    exact ⟨glueModel schema joined ⟨(first, second), same⟩,
      model_ext rfl, model_ext same⟩

/-- The actual model square supplies the observer-presheaf amalgamation
criterion, without assuming compatible pairs already have a mediator. -/
theorem modelJoin_isWeakPullback (schema : Body → EqAxiom S M)
    {ancestor p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (left : ancestor.val ⊆ p.val) (right : ancestor.val ⊆ q.val) :
    AdmissibleContextCongruence.IsWeakPullback
      (restrict.{u} schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left))
      (restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right))
      (restrict schema left) (restrict schema right) := by
  intro first second equal
  have same := (ancestor_agreement_iff schema left right first second).mp equal
  exact ⟨glueModel schema joined ⟨(first, second), same⟩,
    model_ext rfl, model_ext same⟩

/-- Existential predicate image commutes with reindexing across the model
join, by the established observer-presheaf Beck–Chevalley theorem. -/
theorem modelJoin_exists_beckChevalley (schema : Body → EqAxiom S M)
    {ancestor p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (left : ancestor.val ⊆ p.val) (right : ancestor.val ⊆ q.val)
    (predicate : Set (Model.{u} schema p)) :
    (restrict schema right) ⁻¹' ((restrict schema left) '' predicate) =
      (restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right)) ''
        ((restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left)) ⁻¹'
          predicate) :=
  (AdmissibleContextCongruence.beckChevalley_exists_iff
    (restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left))
    (restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right))
    (restrict schema left) (restrict schema right)
    (fun _ => model_ext rfl)).mpr (modelJoin_isWeakPullback schema joined left right) predicate

/-- Universal predicate image satisfies the same earned change-of-base law. -/
theorem modelJoin_forall_beckChevalley (schema : Body → EqAxiom S M)
    {ancestor p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (left : ancestor.val ⊆ p.val) (right : ancestor.val ⊆ q.val)
    (predicate : Set (Model.{u} schema p)) :
    (restrict schema right) ⁻¹'
        AdmissibleContextCongruence.universalImage (restrict schema left) predicate =
      AdmissibleContextCongruence.universalImage
        (restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right))
        ((restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left)) ⁻¹'
          predicate) :=
  (AdmissibleContextCongruence.beckChevalley_forall_iff
    (restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left))
    (restrict schema ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right))
    (restrict schema left) (restrict schema right)
    (fun _ => model_ext rfl)).mpr (modelJoin_isWeakPullback schema joined left right) predicate

/-- The glued model receives the existing equational quotient interpretation.
Its substitution law includes arbitrary quotient-valued simultaneous
environments and every binder list; no new substitution operation is defined. -/
theorem glued_interpretation_substitute (schema : Body → EqAxiom S M)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (pair : CompatibleModels.{u} schema p q) {Γ Δ : Ctx S} {sort : S.Srt}
    (env : BindingSubstitutionAlgebra.Environment S
      (FreeBindingEquationModel.presented (equations schema r)).algebra.substitution.Carrier Γ Δ)
    (term : (FreeBindingEquationModel.presented (equations schema r)).algebra.substitution.Carrier
      Γ sort) :
    (FreeBindingEquationModel.interpretHom (glueModel schema joined pair)).raw.map
        ((FreeBindingEquationModel.presented (equations schema r)).algebra.substitution.substitute
          env term) =
      (glueModel schema joined pair).algebra.substitution.substitute
        (fun s v => (FreeBindingEquationModel.interpretHom
          (glueModel schema joined pair)).raw.map (env s v))
        ((FreeBindingEquationModel.interpretHom (glueModel schema joined pair)).raw.map term) :=
  (FreeBindingEquationModel.interpretHom (glueModel schema joined pair)).map_substitute env term

/-- Visible constraints suffice for observation-relative gluing. One side's
model class must be saturated for the observer: equality of observed values
then transfers its actual contextual equation satisfaction. -/
theorem observed_models_join (schema : Body → EqAxiom S M)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    {Value : Type*} (readout : BindingCloneAlgebra.Algebra.{u} S → Value)
    (visible : bodyTheory q ⊆ observable (equationSat schema) (Setoid.ker readout)) :
    readout '' models (equationSat schema) (bodyTheory r) =
      (readout '' models (equationSat schema) (bodyTheory p)) ∩
        (readout '' models (equationSat schema) (bodyTheory q)) := by
  rw [models_join (equationSat schema) joined]
  have saturated := Scope.isSaturated_models_of_observable visible
  apply Set.Subset.antisymm
  · rintro value ⟨model, member, rfl⟩
    exact ⟨⟨model, member.1, rfl⟩, ⟨model, member.2, rfl⟩⟩
  · rintro value ⟨⟨first, memberFirst, rfl⟩, ⟨second, memberSecond, same⟩⟩
    exact ⟨first, ⟨memberFirst, saturated memberSecond same⟩, rfl⟩

/-- Future-word observations enter through the established privileged-view
construction. The visibility obligation remains about the actual equations. -/
theorem future_observed_models_join (schema : Body → EqAxiom S M)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    {Input Value : Type*} (step : BindingCloneAlgebra.Algebra.{u} S → Input →
      BindingCloneAlgebra.Algebra.{u} S) (evaluation : BindingCloneAlgebra.Algebra.{u} S → Value)
    (visible : bodyTheory q ⊆ observable (equationSat schema)
      (Setoid.ker (PrivilegedView.wordBehaviour step evaluation))) :
    PrivilegedView.wordBehaviour step evaluation '' models (equationSat schema) (bodyTheory r) =
      (PrivilegedView.wordBehaviour step evaluation '' models (equationSat schema) (bodyTheory p)) ∩
        (PrivilegedView.wordBehaviour step evaluation '' models (equationSat schema) (bodyTheory q)) :=
  observed_models_join schema joined (PrivilegedView.wordBehaviour step evaluation) visible

/-- Module model coordinates along invertible transitions use the existing
holonomy system. Ordinary reducts need not be equivalences. -/
def modelViewSystem {Index : Type} (modules : Index → Presentation Origin Label Body)
    (schema : Body → EqAxiom S M) (Edge : Index → Index → Type)
    (coordinate : ∀ {i j}, Edge i j → Model.{u} schema (modules i) ≃ Model.{u} schema (modules j)) :
    Scope.ViewSystem Index where
  View := fun i => Model schema (modules i)
  Edge := Edge
  translate := coordinate

/-- On connected invertible model charts, global chart gluing is equivalent
to trivial holonomy. This does not equate chart gluing with existence of one
compatible family of model values. -/
theorem model_charts_glue_iff {Index : Type} (modules : Index → Presentation Origin Label Body)
    (schema : Body → EqAxiom S M) (Edge : Index → Index → Type)
    (coordinate : ∀ {i j}, Edge i j → Model.{u} schema (modules i) ≃ Model.{u} schema (modules j))
    {root : Index}
    (connect : ∀ j, Trunc ((modelViewSystem modules schema Edge coordinate).Walk root j)) :
    Nonempty (modelViewSystem modules schema Edge coordinate).Gluing ↔
      (modelViewSystem modules schema Edge coordinate).TrivialHolonomy :=
  Scope.ViewSystem.nonempty_gluing_iff connect

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluing
