import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LocalWordCarrier

/-!
# Regression checks for the local derivative-word carrier
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16LocalWordCarrierRegression

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier

theorem localFieldLetter_card_degree_zero :
    Fintype.card (LocalFieldLetter 0) = 6 := by
  decide

theorem localFieldLetter_card_degree_one :
    Fintype.card (LocalFieldLetter 1) = 30 := by
  decide

theorem localFieldLetter_card_degree_two :
    Fintype.card (LocalFieldLetter 2) = 126 := by
  set_option maxRecDepth 10000 in
    decide

theorem labeled_actions_commute
    {fieldCount derivativeCount : ℕ}
    (h : Hypercubic4) (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    (rename • sector).hypercubicAct h =
      rename • sector.hypercubicAct h :=
  hypercubicAct_relabel h rename sector

theorem orbit_tensor_sign_cocycle
    (left right : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    orbit.tensorSign (left * right) =
      orbit.tensorSign right * (right • orbit).tensorSign left :=
  FieldRelabelOrbitCarrier.tensorSign_mul left right orbit

end HypercubicDimension16LocalWordCarrierRegression
end YangMills
end QuantumTheory
end Mettapedia
