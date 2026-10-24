import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.TypeTheory.ContextualPresheafExactness
import Mathlib.CategoryTheory.Functor.Const

/-!
# HOL as a constant fragment of a presheaf interpretation

Carriers, whole typed valuations and term denotations form constant presheaves.
Substitution and context extension are actual natural maps. HOL propositions
are read as stable predicates, with implication and quantification compared
against the ambient all-future operations. Quantifier comparison requires full
domains in the supplied HOL model.

This embeds a specified interpretation into one presheaf category. It does
not assert that every ambient stable predicate is a HOL proposition, or turn
the ambient subobject classifier into a constant Boolean object.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ConstantPresheafInterpretation

open CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualPresheafExactness
open Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

universe d u v w

variable {D : Type d} [Category.{d} D]
variable {Base : Type u} {Const : Ty Base → Type v}

def constant (A : Type w) : D ⥤ Type w := (Functor.const D).obj A

def constantPredicate {A : Type w} (predicate : A → Prop) : StablePredicate (constant (D := D) A) where
  holds point := predicate point.2
  closed step holds := by
    have same : _ = _ := step.2
    change _ = _ at same
    exact same ▸ holds

variable (M : HenkinModel.{u, v, w} Base Const)

def context (Γ : Ctx Base) : D ⥤ Type (max (u + 1) w) := constant (M.Valuation Γ)
def values (A : Ty Base) : D ⥤ Type (max (u + 1) w) := constant (Ty.denote M.Carrier A)

def term {Γ : Ctx Base} {A : Ty Base} (source : Term Const Γ A) :
    NaturalHom (context (D := D) M Γ) (values M A) where
  app _ := M.denote source
  naturality _ _ := rfl

def substitution {Γ Δ : Ctx Base} (source : Subst Const Γ Δ) :
    NaturalHom (context (D := D) M Δ) (context M Γ) where
  app _ := Soundness.substVal M source
  naturality _ _ := rfl

theorem term_substitution {Γ Δ : Ctx Base} {A : Ty Base}
    (sigma : Subst Const Γ Δ) (source : Term Const Γ A) :
    (substitution (D := D) M sigma).comp (term M source) = term M (subst sigma source) := by
  apply NaturalHom.ext
  intro point valuation
  exact (Soundness.denote_subst M sigma source valuation).symm

def projection (Γ : Ctx Base) (A : Ty Base) :
    NaturalHom (context (D := D) M (A :: Γ)) (context M Γ) where
  app _ valuation := fun index => valuation (.vs index)
  naturality _ _ := rfl

def lastVariable (Γ : Ctx Base) (A : Ty Base) :
    NaturalHom (context (D := D) M (A :: Γ)) (values M A) where
  app _ valuation := valuation .vz
  naturality _ _ := rfl

def extension (Γ : Ctx Base) (A : Ty Base) :
    NaturalHom (product (context (D := D) M Γ) (values M A)) (context M (A :: Γ)) where
  app _ pair := M.extend pair.1 pair.2
  naturality _ _ := rfl

theorem projection_extension (Γ : Ctx Base) (A : Ty Base) (point : D)
    (valuation : M.Valuation Γ) (value : Ty.denote M.Carrier A) :
    ((projection M Γ A).app point ((extension M Γ A).app point (valuation, value)) : M.Valuation Γ) =
      (valuation : M.Valuation Γ) := rfl

theorem variable_extension (Γ : Ctx Base) (A : Ty Base) (point : D)
    (valuation : M.Valuation Γ) (value : Ty.denote M.Carrier A) :
    (lastVariable M Γ A).app point ((extension M Γ A).app point (valuation, value)) = value := rfl

theorem extension_eta (Γ : Ctx Base) (A : Ty Base) (point : D) (valuation : M.Valuation (A :: Γ)) :
    ((extension M Γ A).app point ((projection M Γ A).app point valuation,
      (lastVariable M Γ A).app point valuation) : M.Valuation (A :: Γ)) =
        (valuation : M.Valuation (A :: Γ)) := by
  funext B index
  cases index <;> rfl

def predicate {Γ : Ctx Base} (formula : Formula Const Γ) : StablePredicate (context (D := D) M Γ) :=
  constantPredicate (fun valuation => (M.denote formula valuation).down)

theorem predicate_substitution {Γ Δ : Ctx Base} (sigma : Subst Const Γ Δ)
    (formula : Formula Const Γ) :
    inverseImage (substitution (D := D) M sigma) (predicate M formula) = predicate M (subst sigma formula) := by
  apply StablePredicate.ext
  intro point
  exact Iff.of_eq (congrArg ULift.down (Soundness.denote_subst M sigma formula point.2)).symm

theorem implication_reading {Γ : Ctx Base} (first second : Formula Const Γ) :
    implication (predicate (D := D) M first) (predicate M second) = predicate M (.imp first second) := by
  apply StablePredicate.ext
  intro point
  constructor
  · intro available firstHolds
    exact available point.1 (𝟙 point.1) firstHolds
  · intro available _ _ firstHolds
    exact available firstHolds

theorem universal_reading (full : M.FullDomains) {Γ : Ctx Base} {A : Ty Base}
    (body : Formula Const (A :: Γ)) :
    forallImage (projection (D := D) M Γ A) (predicate M body) = predicate M (.all body) := by
  apply StablePredicate.ext
  intro point
  constructor
  · intro available value _
    exact available point.1 (𝟙 point.1) (M.extend point.2 value) rfl
  · intro available future arrival valuation projected
    have recovered : (M.extend point.2 (valuation .vz) : M.Valuation (A :: Γ)) =
        (valuation : M.Valuation (A :: Γ)) := by
      funext B index
      cases index with
      | vz => rfl
      | vs old => exact (congrArg (fun values : M.Valuation Γ => values old) projected).symm
    have holds := available (valuation .vz) (full _ _)
    exact (congrArg (fun valuation : M.Valuation (A :: Γ) => (M.denote body valuation).down) recovered).mp holds

theorem existential_reading (full : M.FullDomains) {Γ : Ctx Base} {A : Ty Base}
    (body : Formula Const (A :: Γ)) :
    existsImage (projection (D := D) M Γ A) (predicate M body) = predicate M (.ex body) := by
  apply StablePredicate.ext
  intro point
  constructor
  · rintro ⟨valuation, projected, available⟩
    refine ⟨valuation .vz, full _ _, ?_⟩
    have recovered : (M.extend point.2 (valuation .vz) : M.Valuation (A :: Γ)) =
        (valuation : M.Valuation (A :: Γ)) := by
      funext B index
      cases index with
      | vz => rfl
      | vs old => exact (congrArg (fun values : M.Valuation Γ => values old) projected).symm
    exact (congrArg (fun valuation : M.Valuation (A :: Γ) => (M.denote body valuation).down) recovered).mpr available
  · rintro ⟨value, _, available⟩
    exact ⟨M.extend point.2 value, rfl, available⟩

/-- All 29 retained proof rules remain valid in the same presheaf context. -/
theorem proof_sound (full : M.FullDomains) {Γ : Ctx Base}
    {hypotheses : List (Formula Const Γ)} {conclusion : Formula Const Γ}
    (proof : ProofSyntax Const hypotheses conclusion) (point : (context (D := D) M Γ).Elements)
    (satisfied : ∀ formula ∈ hypotheses, (predicate M formula).holds point) :
    (predicate M conclusion).holds point :=
  Soundness.extDerivation_sound proof.erase (M.functionsRespectEqv_of_fullDomains full)
    (fun _ => full _ _) satisfied

/-- Classicality of the chosen HOL interpretation concerns this image of
predicates. No surjectivity onto all ambient stable predicates is asserted. -/
theorem excludedMiddle_in_image (full : M.FullDomains) {Γ : Ctx Base} (formula : Formula Const Γ)
    (point : (context (D := D) M Γ).Elements) :
    (predicate M (.or formula (.not formula))).holds point :=
  M.validatesExcludedMiddle formula point.2 (fun _ => full _ _)

/-- If every ambient predicate is the actual interpretation of a source
formula, classicality extends from the interpreted fragment to that entire
predicate object. Equality of predicates supplies both preservation and
reflection; a map of proof syntax alone does not supply this coverage. -/
theorem excludedMiddle_of_predicate_coverage (full : M.FullDomains) {Γ : Ctx Base}
    (covers : Function.Surjective (predicate (D := D) M (Γ := Γ)))
    (proposition : StablePredicate (context (D := D) M Γ))
    (point : (context (D := D) M Γ).Elements) :
    proposition.holds point ∨
      (implication proposition (predicate M (.bot : Formula Const Γ))).holds point := by
  obtain ⟨formula, rfl⟩ := covers proposition
  rcases excludedMiddle_in_image M full formula point with positive | negative
  · exact Or.inl positive
  · apply Or.inr
    rw [implication_reading]
    exact negative

end Mettapedia.Logic.HOL.Embedding.ConstantPresheafInterpretation
