import Mettapedia.Languages.Megalodon.HOLTermFormation
import Mettapedia.Logic.HOL.Syntax.TypeSubstitution

/-!
# HOL encoding commutes with simple-type interpretation

Retyping a term and then expanding its equality and logical constructors
agrees with performing those operations in the opposite order. A type
interpretation whose image has formed native annotations therefore provides
formed arguments for every encoded source term.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.HOLTypeSubstitutionEncoding

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding

universe u v w
variable {SourceBase : Type u} {SourceConst : Ty SourceBase → Type v}
variable {environment : Environment}
variable (types : SourceBase → Ty Base)
variable (constants : ∀ {type}, SourceConst type → Constant environment (type.substitute types))
variable {gamma : Ctx SourceBase} {type : Ty SourceBase}

theorem equality_mapTypes (type : Ty SourceBase) :
    mapTypes types constants (HenkinEqualityInterpretation.equality (Γ := gamma) type) =
      HenkinEqualityInterpretation.equality (type.substitute types) := rfl

theorem expandEquality_mapTypes (source : Term SourceConst gamma type) :
    expandEquality (mapTypes types constants source) =
      mapTypes types constants (expandEquality source) := by
  induction source <;>
    simp_all only [mapTypes, expandEquality, HenkinEqualityInterpretation.equalityFormula,
      equality_mapTypes]

theorem mapTypes_rename_lift_weaken {bound extra : Ty SourceBase}
    (source : Term SourceConst (bound :: gamma) type) :
    mapTypes types constants
        (rename (Rename.lift (Rename.weaken (σ := extra))) source) =
      rename (Rename.lift (Rename.weaken (σ := extra.substitute types)))
        (mapTypes types constants source) :=
  mapTypes_rename types constants _ _ (by intro value index; cases index <;> rfl) source

theorem expandInline_mapTypes (source : Term SourceConst gamma type) :
    ImpredicativeConnectives.expandInline (mapTypes types constants source) =
      mapTypes types constants (ImpredicativeConnectives.expandInline source) := by
  induction source <;>
    simp_all only [mapTypes, ImpredicativeConnectives.expandInline,
      ImpredicativeConnectives.truth, ImpredicativeConnectives.falsity,
      ImpredicativeConnectives.conjunctionFormula, ImpredicativeConnectives.disjunctionFormula,
      ImpredicativeConnectives.existentialInline, mapTypes_weaken,
      mapTypes_rename_lift_weaken, Var.mapTypes]

theorem encode_mapTypes (source : Term SourceConst gamma type) :
    encode (mapTypes types constants source) = mapTypes types constants (encode source) := by
  rw [encode, expandEquality_mapTypes, expandInline_mapTypes]
  rfl

theorem annotations_of_erasure (depth : Nat)
    (formed : ∀ type : Ty SourceBase, (reifyType (type.substitute types)).plainWellFormed depth = true)
    (source : Term SourceConst gamma type) {raw : Tm}
    (erased : erase (mapTypes types constants source) = some raw) :
    plainAnnotations depth raw = true := by
  induction source generalizing raw with
  | var index =>
      simp only [mapTypes, erase, Option.some.injEq] at erased
      subst raw
      rfl
  | const symbol =>
      cases h : constants symbol <;> simp only [mapTypes, erase, h, Option.some.injEq] at erased <;>
        subst raw <;> rfl
  | app function argument ihf iha | imp function argument ihf iha =>
      cases leftErased : erase (mapTypes types constants function) <;>
        cases rightErased : erase (mapTypes types constants argument) <;>
        simp_all [mapTypes, erase]
      all_goals
        subst raw
        simp_all [plainAnnotations]
  | lam body ih | all body ih =>
      cases bodyErased : erase (mapTypes types constants body) <;>
        simp_all [mapTypes, erase]
      all_goals
        subst raw
        simp_all [plainAnnotations]
  | top | bot | and | or | not | eq | ex => simp [mapTypes, erase] at erased

theorem native_annotations (depth : Nat)
    (formed : ∀ type : Ty SourceBase, (reifyType (type.substitute types)).plainWellFormed depth = true)
    (source : Term SourceConst gamma type) :
    plainAnnotations depth (native (mapTypes types constants source)) = true := by
  apply annotations_of_erasure types constants depth formed (encode source)
  rw [← encode_mapTypes]
  exact native_erased _

#print axioms equality_mapTypes
#print axioms expandEquality_mapTypes
#print axioms expandInline_mapTypes
#print axioms encode_mapTypes
#print axioms annotations_of_erasure
#print axioms native_annotations

end Mettapedia.Languages.Megalodon.HOLTypeSubstitutionEncoding
