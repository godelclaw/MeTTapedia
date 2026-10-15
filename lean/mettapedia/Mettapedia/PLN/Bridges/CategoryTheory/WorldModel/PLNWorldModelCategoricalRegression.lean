import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness

/-!
# Chapter-8 WM Categorical Regression Fixture

Concrete theorem-level regression fixtures: the evidence-level endpoint
`institution_beckChevalley_endpoint` on an identity pullback square of any WM
hyperdoctrine and on a pullback square of the counting hyperdoctrine, and the
HOL and FOL consequence bridges on fixed states.
-/

namespace Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalRegression

open _root_.CategoryTheory
open LO
open LO.FirstOrder
open Mettapedia.Logic.HOL
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelInstitution
open Mettapedia.PLN.Evidence.EvidenceClass

universe u v x

abbrev WMHyper (State : Type x) [EvidenceType State] :=
  Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine.WMHyperdoctrine.{u, v, 0, x} State

variable {State : Type x} [EvidenceType State]

/-- Ch.8 concrete fixture: the evidence-level endpoint on the identity square at
one object. -/
theorem institution_beckChevalley_endpoint_id_fixture
    (H : WMHyper State)
    {X : H.Obj} (W : State) (φ : H.query X) :
    Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := H) (π₁ := 𝟙 X) (π₂ := 𝟙 X) (f := 𝟙 X) (g := 𝟙 X) W φ := by
  simpa using
    (Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge.WMHyperdoctrine.institution_beckChevalley_endpoint
      (H := H) (P := X) (A := X) (B := X) (D := X)
      (π₁ := 𝟙 X) (π₂ := 𝟙 X) (f := 𝟙 X) (g := 𝟙 X)
      (hpb := _root_.CategoryTheory.IsPullback.id_horiz (f := (𝟙 X)))
      (W := W) (φ := φ))

abbrev HOLFixtureBase := PUnit
abbrev HOLFixtureConst (_ : Ty HOLFixtureBase) := PEmpty

def holFixtureModel :
    HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst :=
  HenkinModel.standard (Base := HOLFixtureBase) (Const := HOLFixtureConst)
    (Carrier := fun _ => PUnit)
    (constDen := by intro τ c; nomatch c)

abbrev holFalseQuery :
    Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness.HOLQuery
      (Base := HOLFixtureBase) HOLFixtureConst := .bot
abbrev holTrueQuery :
    Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness.HOLQuery
      (Base := HOLFixtureBase) HOLFixtureConst := .top

def holFixtureState :
    Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst) :=
  ({holFixtureModel} :
      Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst)) +
    ({holFixtureModel} :
      Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst))

theorem holFalse_to_true_pointwise :
    ∀ M : HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst,
      Mettapedia.Logic.HOL.holSatisfies
        (Base := HOLFixtureBase) (Const := HOLFixtureConst) M holFalseQuery →
      Mettapedia.Logic.HOL.holSatisfies
        (Base := HOLFixtureBase) (Const := HOLFixtureConst) M holTrueQuery := by
  intro M hFalse
  exact False.elim ((HenkinModel.models_bot M) hFalse)

/-- Ch.8 concrete HOL fixture: pointwise implication `⊥ → ⊤` transported to a
WM strength inequality on a fixed two-model state. -/
theorem hol_pointwise_bool_fixture :
    BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst))
        (Query := Mettapedia.Logic.HOL.HOLQuery HOLFixtureConst)
        holFixtureState holFalseQuery ≤
      BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel.{0, 0, 0} HOLFixtureBase HOLFixtureConst))
        (Query := Mettapedia.Logic.HOL.HOLQuery HOLFixtureConst)
        holFixtureState holTrueQuery :=
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompletenessCore.multiset_strength_le_of_pointwise
    (Base := HOLFixtureBase) (Const := HOLFixtureConst)
    (W := holFixtureState) (φ := holFalseQuery) (ψ := holTrueQuery)
    holFalse_to_true_pointwise

/-- Ch.8 concrete counting fixture: the evidence-level endpoint on the pullback
of `selectTrue` along itself in the counting hyperdoctrine. -/
theorem counting_endpoint_selectTrue_fixture :
    Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointStatement
      (H := Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine.countingHyperdoctrine)
      (𝟙 _) Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine.selectTrue
      Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine.selectTrue (𝟙 _)
      Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine.onePoint
      (.atom Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine.isTrue) :=
  Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge.WMHyperdoctrine.institution_beckChevalley_endpoint
    _ _ _ _ _ (_root_.CategoryTheory.IsPullback.id_horiz _) _ _

/-- Ch.8 concrete FOL fixture (proof-theoretic path):
consume `provable_imp_iff_singletonStrengthLEOnTheory` to obtain provability,
then build and execute a `wmConsequenceRuleOn_of_provable_imp` endpoint on a
singleton state. -/
theorem fol_provable_bridge_rule_singleton_fixture
    {L : Language.{u}}
    (S : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.PointedFOL L) :
    BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLState L)
        (Query := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L)
        ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLState L)
        (⊥ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L) ≤
      BinaryWorldModel.queryStrength
        (State := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLState L)
        (Query := Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L)
        ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLState L)
        (⊤ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L) := by
  let T : Theory L := (∅ : Theory L)
  let φ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L :=
    (⊥ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L)
  let ψ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L :=
    (⊤ : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLQuery L)
  have hpoint :
      Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.pointwiseImpliesOnTheory
        T φ ψ := by
    intro S' _hT hφ
    simp [ψ, Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOL.folSatisfies]
  have hsing :
      Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.singletonStrengthLEOnTheory
        T φ ψ :=
    (Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
      (T := T) (φ := φ) (ψ := ψ)).1 hpoint
  have hprov : T ⊢ (φ ➝ ψ) :=
    (Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.provable_imp_iff_singletonStrengthLEOnTheory
      (T := T) (φ := φ) (ψ := ψ)).2 hsing
  let rule :=
    Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.wmConsequenceRuleOn_of_provable_imp
      (T := T) (φ := φ) (ψ := ψ) hprov
  have hside : rule.side ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLState L) := by
    intro S' hmem
    simp [T]
  have hsound := rule.sound hside
  change BinaryWorldModel.queryStrength
      ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLState L) φ ≤
    BinaryWorldModel.queryStrength
      ({S} : Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelFOLCompleteness.FOLState L) ψ
  exact hsound

end Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalRegression
