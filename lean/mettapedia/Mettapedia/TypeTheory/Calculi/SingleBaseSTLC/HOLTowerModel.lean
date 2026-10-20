import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLConversionBubble
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TypedEqualityEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness

/-!
# The simple conversion comparison reaches the set-tower model

The common beta observer licenses equality in the tower's selected typed
judgment. Its context is formed independently from the original simple
context. The maintained annotated elaboration and set interpretation then
give the same equality a model meaning under `CofinalInaccessibles`.

The model hypothesis is used on this semantic edge, not by the simple
conversion checker. This does not reflect arbitrary set truth or higher
identity structure, or identify the tower with a native HOTG proof checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLTowerModel

open IntrinsicSTT TowerDTT HOLConversionBubble
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open TowerInterpretation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceUniverseInterpretation (interpretHead)

universe u v w

variable {Base : Type v} {Const : HOL.Ty Base → Type w}

/-- Equality admitted by the common computational observer is actual set
equality through the existing annotated tower interpretation. -/
theorem observed_set_equality (h : CofinalInaccessibles.{u}) (ground : Base)
    {Γ : List IntrinsicSTT.Ty} {A : IntrinsicSTT.Ty} (left right : IntrinsicSTT.Term Γ A)
    (observed : (gsltOSLF (theory (Const := Const) ground false Γ A)).satisfies (S := ()) left
      (nativeType ground false right).pred) :
    ∃ statement : CStatement Tower.Head,
      statement.CtxFormed (TowerControls.P₀ (L := Nat)) ∧
      CDerivable (TowerControls.P₀ (L := Nat)) statement ∧
      statement.erase = .equality (eraseContext Γ) (eraseTerm left) (eraseTerm right)
        (eraseTypeAt Γ.length A) ∧
      Holds (interpretHead h ∅ ∅ (fun _ => (0 : Nat))) (fun _ => ∅) statement := by
  have converted := (ConversionDecision.decideConversion_correct left right).1
    ((beta_satisfies_iff_decides ground left right).1 observed)
  have typed := TypedEqualityEmbedding.conversion_equal TypedEqualityEmbedding.towerHeads converted
  obtain ⟨statement, formed, derived, erases⟩ := tower_elaborates typed
    (TypedEqualityEmbedding.context_formed TypedEqualityEmbedding.towerHeads Γ)
  exact ⟨statement, formed, derived, erases, CDerivable.sound_tower h derived⟩

/-- The same tower also has a larger typed-equality judgment. Eta is available
there; the structural conversion tested by the beta observer is narrower. -/
theorem eta_typed_equality :
    Equal Tower.rules (eraseContext [.arr .atom .atom])
      (eraseTerm ConversionDecision.etaExpansion) (eraseTerm ConversionDecision.etaVariable)
      (eraseTypeAt 1 (.arr .atom .atom)) := by
  have pointwise := TypedEqualityEmbedding.beta_equal TypedEqualityEmbedding.towerHeads
    (.app (.var (.succ (.succ .zero))) (.var .zero) :
      IntrinsicSTT.Term [.atom, .atom, .arr .atom .atom] .atom)
    (.var .zero : IntrinsicSTT.Term [.atom, .arr .atom .atom] .atom)
  exact .etaPi
    (TypedEqualityEmbedding.term_typed TypedEqualityEmbedding.towerHeads ConversionDecision.etaExpansion)
    (TypedEqualityEmbedding.term_typed TypedEqualityEmbedding.towerHeads ConversionDecision.etaVariable)
    pointwise

theorem typed_equality_not_structural_conversion :
    Equal Tower.rules (eraseContext [.arr .atom .atom])
      (eraseTerm ConversionDecision.etaExpansion) (eraseTerm ConversionDecision.etaVariable)
      (eraseTypeAt 1 (.arr .atom .atom)) ∧
    ¬ Conv Tower.HeadEq (eraseTerm ConversionDecision.etaVariable)
      (eraseTerm ConversionDecision.etaExpansion) :=
  ⟨eta_typed_equality, HOLComparison.Controls.eta_not_towerConv⟩

#print axioms observed_set_equality
#print axioms typed_equality_not_structural_conversion

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLTowerModel
