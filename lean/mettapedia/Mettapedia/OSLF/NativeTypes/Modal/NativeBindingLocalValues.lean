import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTypedBodies
import Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventPresheaf

/-!
# Independently typed contextual values as actual native carrier points

The local dependency prefix is retained separately from ambient context.
Its type and the complete decoded native carrier spine are checked from
authored data. The source value becomes a point of the genuine presheaf
function carrier through the earned binding-body equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingLocalValues

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeBindingEventAction (bound)

variable {language : LanguageDef}

abbrev Value (dependencies : List TypeExpr) (expected : TypeExpr) (ambient : List String) :=
  {body : Pattern | HasType language FreeTypeContext.empty
    (dependencies ++ bound ambient) body expected ∧ isObjectPattern body = true ∧
    body.hasCanonicalBinderMetadata = true}

def action {dependencies : List TypeExpr} {expected : TypeExpr} {source target : List String}
    (substitution : Sub (signature language) source target)
    (value : Value (language := language) dependencies expected source) : Value (language := language) dependencies expected target :=
  ⟨ContextSubstitution.substitute
    (ContextSubstitution.lift dependencies.length (NativeBindingRendering.assignment substitution)) value.val,
    value.property.1.substituteBound
      ((NativeBindingRendering.typedAssignment substitution).liftContext dependencies),
    contextSubstitute_objects value.property.2.1
      (NativePremiseSubstitutionBase.objects_lift
        (fun index => (NativeBindingRendering.assignment_images substitution index).1) _),
    contextSubstitute_canonical value.property.2.2
      (NativePremiseSubstitutionBase.canonical_lift
        (fun index => (NativeBindingRendering.assignment_images substitution index).2) _)⟩

theorem action_identity {dependencies : List TypeExpr} {expected : TypeExpr} {ambient : List String}
    (value : Value (language := language) dependencies expected ambient) :
    action (fun _ position => Term.var position) value = value := by
  apply Subtype.ext
  simp only [action, NativeBindingRendering.assignment_identity,
    ContextSubstitution.lift_identity, ContextSubstitution.substitute_id]

theorem action_composition {dependencies : List TypeExpr} {expected : TypeExpr}
    {source middle target : List String} (first : Sub (signature language) source middle)
    (second : Sub (signature language) middle target) (value : Value (language := language) dependencies expected source) :
    action second (action first value) =
      action (fun sort position => Binding.bind second (first sort position)) value := by
  apply Subtype.ext
  simp only [action, ContextSubstitution.substitute_comp, ContextSubstitution.lift_comp,
    NativeBindingRendering.assignment_composition]

def values (dependencies : List TypeExpr) (expected : TypeExpr) : Base (algebra language) ⥤ Type where
  obj X := Value (language := language) dependencies expected X.unop.context
  map morphism := TypeCat.ofHom (action (NativeAuthoredEventPresheaf.morphismSub morphism))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro value
    change action (NativeAuthoredEventPresheaf.morphismSub (𝟙 X)) value = value
    rw [NativeAuthoredEventPresheaf.morphismSub_identity]
    exact action_identity value
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    change action (NativeAuthoredEventPresheaf.morphismSub (first ≫ second)) value =
      action (NativeAuthoredEventPresheaf.morphismSub second)
        (action (NativeAuthoredEventPresheaf.morphismSub first) value)
    rw [NativeAuthoredEventPresheaf.morphismSub_composition]
    exact (action_composition _ _ value).symm

def baseNames? : List TypeExpr → Option (List String)
  | [] => some []
  | .base sort :: types => (baseNames? types).map (sort :: ·)
  | _ :: _ => none

theorem baseNames?_exact (types : List TypeExpr) (names : List String) :
    baseNames? types = some names ↔ types = bound names := by
  induction types generalizing names with
  | nil => cases names <;> simp [baseNames?, bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext]
  | cons type types ih =>
      cases type with
      | base sort =>
          cases names with
          | nil => simp [baseNames?, bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext]
          | cons name names =>
              simp only [baseNames?, Option.map_eq_some_iff, bound,
                Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_cons, List.cons.injEq,
                TypeExpr.base.injEq]
              constructor
              · rintro ⟨tail, decoded, same⟩
                obtain ⟨rfl, rfl⟩ := same
                exact ⟨rfl, (ih _).mp decoded⟩
              · rintro ⟨rfl, same⟩
                exact ⟨names, (ih names).mpr same, ⟨rfl, rfl⟩⟩
      | arrow | multiBinder | collection =>
          cases names <;> simp [baseNames?, bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext]

structure Shape (dependencies : List TypeExpr) (expected : TypeExpr)
    (carrier : NativeSignature.Carrier language) where
  scope : List String
  domains : List String
  result : String
  dependencyContext : dependencies = bound scope
  represented : carrier.source = dependencies.reverse.foldr TypeExpr.arrow expected
  spine : BinderSpine carrier.source domains result

def shape? (dependencies : List TypeExpr) (expected : TypeExpr)
    (carrier : NativeSignature.Carrier language)
    (represented : carrier.source = dependencies.reverse.foldr TypeExpr.arrow expected) :
    Option (Shape dependencies expected carrier) := do
  let scope ← (baseNames? dependencies).attach
  let parsed ← (binderSpine? carrier.source).attach
  pure ⟨scope.val, parsed.val.1, parsed.val.2,
    (baseNames?_exact dependencies scope.val).mp scope.property,
    represented, (binderSpine?_exact _ _ _).mp parsed.property⟩

theorem shape?_complete {dependencies : List TypeExpr} {expected : TypeExpr}
    {carrier : NativeSignature.Carrier language} (shape : Shape dependencies expected carrier)
    (represented : carrier.source = dependencies.reverse.foldr TypeExpr.arrow expected) :
    ∃ decoded, shape? dependencies expected carrier represented = some decoded := by
  have dependenciesDecoded := (baseNames?_exact dependencies shape.scope).mpr shape.dependencyContext
  have spineDecoded := (binderSpine?_exact _ _ _).mpr shape.spine
  unfold shape?
  rw [Option.attach_eq_some _ ⟨shape.scope, dependenciesDecoded⟩]
  dsimp only [Bind.bind, Option.bind]
  rw [Option.attach_eq_some _ ⟨(shape.domains, shape.result), spineDecoded⟩]
  exact ⟨_, rfl⟩

theorem wrap_typed (scope : List String) {expected : TypeExpr} {ambient : List String} {body : Pattern}
    (typed : HasType language FreeTypeContext.empty (bound (scope.reverse ++ ambient)) body expected) :
    HasType language FreeTypeContext.empty (bound ambient) (wrap scope body)
      ((scope.map TypeExpr.base).foldr TypeExpr.arrow expected) := by
  induction scope generalizing ambient with
  | nil => exact typed
  | cons sort scope ih =>
      apply HasType.lambda
      have localTyped := ih (ambient := sort :: ambient)
        (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using typed)
      simpa only [bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_cons] using localTyped

def wrappedSource {dependencies : List TypeExpr} {expected : TypeExpr} {carrier : NativeSignature.Carrier language}
    (shape : Shape dependencies expected carrier) {ambient : List String}
    (value : Value (language := language) dependencies expected ambient) :
    NativeBindingTypedBodies.TypedSource (language := language) ambient carrier.source := by
  refine ⟨wrap shape.scope.reverse value.val, ?_, ?_, ?_⟩
  · rw [shape.represented]
    have typed := value.property.1
    have typedOriginal : HasType language FreeTypeContext.empty
        (bound shape.scope ++ bound ambient) value.val expected := by
      simpa only [shape.dependencyContext] using typed
    have wrapped := wrap_typed shape.scope.reverse
      (by simpa only [List.reverse_reverse, bound,
        Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_append] using typedOriginal)
    simpa only [shape.dependencyContext, bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext,
      List.map_reverse] using wrapped
  · induction shape.scope.reverse with
    | nil => exact value.property.2.1
    | cons _ _ ih => exact ih
  · induction shape.scope.reverse with
    | nil => exact value.property.2.2
    | cons _ _ ih => simpa only [wrap, Pattern.hasCanonicalBinderMetadata,
        Bool.and_eq_true, Option.isNone_none] using And.intro (show true = true from rfl) ih

theorem source_substitution {dependencies : List TypeExpr} {expected : TypeExpr}
    {carrier : NativeSignature.Carrier language} (shape : Shape dependencies expected carrier)
    {ambient target : List String} (substitution : Sub (signature language) ambient target)
    (value : Value (language := language) dependencies expected ambient) :
    (wrappedSource shape (action substitution value)).val = ContextSubstitution.substitute
      (NativeBindingRendering.assignment substitution) (wrappedSource shape value).val := by
  change wrap shape.scope.reverse (ContextSubstitution.substitute
    (ContextSubstitution.lift dependencies.length (NativeBindingRendering.assignment substitution)) value.val) =
    ContextSubstitution.substitute (NativeBindingRendering.assignment substitution)
      (wrap shape.scope.reverse value.val)
  rw [NativeBindingTypedBodies.substitute_wrap]
  have length : dependencies.length = shape.scope.reverse.length := by
    simpa only [bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext,
      List.length_map, List.length_reverse] using congrArg List.length shape.dependencyContext
  rw [length]

noncomputable def bodyMap {dependencies : List TypeExpr} {expected : TypeExpr}
    {carrier : NativeSignature.Carrier language} (shape : Shape dependencies expected carrier)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup) :
    values dependencies expected ⟶ scopedBodies (algebra language) shape.domains.reverse shape.result where
  app X := TypeCat.ofHom fun value =>
    NativeBindingTypedBodies.body admitted labels shape.spine (wrappedSource shape value)
  naturality X Y morphism := by
    apply ConcreteCategory.hom_ext
    intro value
    change NativeBindingTypedBodies.body admitted labels shape.spine
        (wrappedSource shape (action (NativeAuthoredEventPresheaf.morphismSub morphism) value)) =
      (scopedBodies (algebra language) shape.domains.reverse shape.result).map morphism
        (NativeBindingTypedBodies.body admitted labels shape.spine (wrappedSource shape value))
    have read := NativeBindingTypedBodies.body_substitution admitted labels shape.spine
      (NativeAuthoredEventPresheaf.morphismSub morphism)
      (wrappedSource shape value)
      (wrappedSource shape (action (NativeAuthoredEventPresheaf.morphismSub morphism) value))
      (source_substitution shape _ value)
    exact read.trans (NativeBindingScopedBodies.scoped_map _ _ morphism _).symm

/-- A typed contextual readout lands in the same actual native carrier
used by the authored constructor model. -/
noncomputable def nativeMap {dependencies : List TypeExpr} {expected : TypeExpr}
    {carrier : NativeSignature.Carrier language} (shape : Shape dependencies expected carrier)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup) :
    values dependencies expected ⟶ meaning carrier :=
  bodyMap shape admitted labels ≫ (NativeBindingScopedBodies.nativeBodyIso carrier shape.spine).inv

theorem nativeMap_read {dependencies : List TypeExpr} {expected : TypeExpr}
    {carrier : NativeSignature.Carrier language} (shape : Shape dependencies expected carrier)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    (X : Base (algebra language)) (value : (values dependencies expected).obj X) :
    (NativeBindingScopedBodies.nativeBodyIso carrier shape.spine).hom.app X
        ((nativeMap shape admitted labels).app X value) =
      NativeBindingTypedBodies.body admitted labels shape.spine (wrappedSource shape value) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun map => map.app X)
      (NativeBindingScopedBodies.nativeBodyIso carrier shape.spine).inv_hom_id) _

theorem nativeMap_source {dependencies : List TypeExpr} {expected : TypeExpr}
    {carrier : NativeSignature.Carrier language} (shape : Shape dependencies expected carrier)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    (X : Base (algebra language)) (value : (values dependencies expected).obj X) :
    wrap shape.domains
      (toPattern ((NativeBindingScopedBodies.nativeBodyIso carrier shape.spine).hom.app X
        ((nativeMap shape admitted labels).app X value))) =
      wrap shape.scope.reverse value.val := by
  rw [nativeMap_read]
  exact NativeBindingTypedBodies.body_read admitted labels shape.spine (wrappedSource shape value)

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingLocalValues
