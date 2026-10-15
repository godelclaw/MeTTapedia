import Mettapedia.CategoryTheory.PredicateDoctrineProduct
import Mettapedia.CategoryTheory.PositionedRewritePredicateLogic
import Mettapedia.CategoryTheory.PredicateDoctrineQuantifierCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Simultaneous satisfaction of two predicate coordinates

Reading both coordinates at one input preserves substitution and universal
quantification. Existential quantification supplies only a comparison: a
common witness supplies two witnesses, while the converse need not hold.
The same comparison applies to the actual positioned rewrite modality.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.PredicateDoctrineProductAgreement

open _root_.CategoryTheory
open PredicateDoctrine

universe u v p
variable {C : Type u} [Category.{v} C]
variable (D : FirstOrder.{u,v,p} C)

def simultaneous {X : C} (predicate : (PredicateDoctrineProduct.firstOrder D D).Fiber X) :
    D.Fiber X := predicate.1 ⊓ predicate.2

theorem simultaneous_mono {X : C} : Monotone (simultaneous D (X := X)) :=
  fun _ _ ordered => inf_le_inf ordered.1 ordered.2

theorem simultaneous_substitution {X Y : C} (incoming : X ⟶ Y)
    (predicate : (PredicateDoctrineProduct.firstOrder D D).Fiber Y) :
    simultaneous D ((PredicateDoctrineProduct.firstOrder D D).reindex incoming predicate) =
      D.reindex incoming (simultaneous D predicate) :=
  (D.reindex_inf incoming predicate.1 predicate.2).symm

theorem simultaneous_top (X : C) : simultaneous D (⊤ :
    (PredicateDoctrineProduct.firstOrder D D).Fiber X) = ⊤ := inf_idem _

theorem simultaneous_inf {X : C}
    (first second : (PredicateDoctrineProduct.firstOrder D D).Fiber X) :
    simultaneous D (first ⊓ second) = simultaneous D first ⊓ simultaneous D second :=
  inf_inf_inf_comm _ _ _ _

theorem simultaneous_forall {X Y : C} (route : X ⟶ Y)
    (predicate : (PredicateDoctrineProduct.firstOrder D D).Fiber X) :
    simultaneous D ((PredicateDoctrineProduct.firstOrder D D).forallAlong route predicate) =
      D.forallAlong route (simultaneous D predicate) :=
  ((D.forall_adj route).u_inf (b₁ := predicate.1) (b₂ := predicate.2)).symm

/-- A single input proves both coordinate existentials. The comparison
retains its direction rather than identifying independently chosen inputs. -/
theorem exists_simultaneous_le {X Y : C} (route : X ⟶ Y)
    (predicate : (PredicateDoctrineProduct.firstOrder D D).Fiber X) :
    D.existsAlong route (simultaneous D predicate) ≤
      simultaneous D ((PredicateDoctrineProduct.firstOrder D D).existsAlong route predicate) :=
  le_inf (D.exists_mono route inf_le_left) (D.exists_mono route inf_le_right)

theorem reindex_exists_of_mono {X Y : C} (route : X ⟶ Y) [Mono route]
    (predicate : D.Fiber X) : D.reindex route (D.existsAlong route predicate) = predicate := by
  have square : IsPullback (𝟙 X) (𝟙 X) route route :=
    IsPullback.of_horiz_isIso_mono
      ⟨by simp only [Category.id_comp]⟩
  exact (D.exists_baseChange (𝟙 X) (𝟙 X) route route square predicate).trans
    ((congrArg (D.existsAlong (𝟙 X)) (D.reindex_id X predicate)).trans
      (D.existsAlong_id X predicate))

/-- Monicity forces the coordinate witnesses at a focus to be the same
input. Beck--Chevalley and Frobenius earn the resulting equality. -/
theorem exists_simultaneous_eq_of_mono {X Y : C} (route : X ⟶ Y) [Mono route]
    (predicate : (PredicateDoctrineProduct.firstOrder D D).Fiber X) :
    D.existsAlong route (simultaneous D predicate) =
      simultaneous D ((PredicateDoctrineProduct.firstOrder D D).existsAlong route predicate) := by
  change D.existsAlong route (predicate.1 ⊓ predicate.2) =
    D.existsAlong route predicate.1 ⊓ D.existsAlong route predicate.2
  exact (congrArg (fun condition => D.existsAlong route (predicate.1 ⊓ condition))
    (reindex_exists_of_mono D route predicate.2).symm).trans
      (D.frobenius route predicate.1 (D.existsAlong route predicate.2))

/-- The rely-instance quantifier uses one complete input before the focus
image. Its simultaneous reading is bounded by the paired modality. -/
theorem modality_simultaneous_le {instances assignments carrier : C}
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (condition : (PredicateDoctrineProduct.firstOrder D D).Fiber instances) :
    PositionedRewritePredicateLogic.modality D forget focus (simultaneous D condition) ≤
      simultaneous D (PositionedRewritePredicateLogic.modality
        (PredicateDoctrineProduct.firstOrder D D) forget focus condition) := by
  change D.existsAlong focus (D.forallAlong forget (simultaneous D condition)) ≤
    simultaneous D ((PredicateDoctrineProduct.firstOrder D D).existsAlong focus
      ((PredicateDoctrineProduct.firstOrder D D).forallAlong forget condition))
  rw [← simultaneous_forall]
  exact exists_simultaneous_le D focus _

theorem modality_simultaneous_eq_of_mono {instances assignments carrier : C}
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier) [Mono focus]
    (condition : (PredicateDoctrineProduct.firstOrder D D).Fiber instances) :
    PositionedRewritePredicateLogic.modality D forget focus (simultaneous D condition) =
      simultaneous D (PositionedRewritePredicateLogic.modality
        (PredicateDoctrineProduct.firstOrder D D) forget focus condition) := by
  change D.existsAlong focus (D.forallAlong forget (simultaneous D condition)) =
    simultaneous D ((PredicateDoctrineProduct.firstOrder D D).existsAlong focus
      ((PredicateDoctrineProduct.firstOrder D D).forallAlong forget condition))
  rw [← simultaneous_forall]
  exact exists_simultaneous_eq_of_mono D focus _

end Mettapedia.CategoryTheory.PredicateDoctrineProductAgreement
