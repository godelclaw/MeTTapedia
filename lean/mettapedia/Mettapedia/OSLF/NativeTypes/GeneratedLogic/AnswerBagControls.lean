import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorParts

/-!
# Controls: the answer-bag driver through both front doors

Payloads are the atoms `a` and `b` of a payload language (`payloadCalc`). The answer language reads bags of them up
to order, and its bags split into sub-bags; the generated front door decides the driver's formulas with the bag parts
decider over the bags' canonical forms. Each decided runtime verdict of the completed-answer controls (exact packets and
lower multiplicity bounds on the answer bag `{b, b}`) is also obtained from the generated front door, with the agreement
proved at every budget (`agreesOn_of_frontDoorOn`):

| formula | bag | answer |
|---|---|---|
| exactly `b, b` | `{b, b}` | yes |
| exactly `b` | `{b, b}` | no |
| exactly `b, b, b` | `{b, b}` | no |
| exactly `a, b` | `{b, b}` | no |
| at least two `b` | `{b, b}` | yes |
| at least three `b` | `{b, b}` | no |
| the singleton `b` | `{b, b}` | no |
| exactly nothing | `{}` | yes |
| exactly `a, b` | `{b, a}` | yes |
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.OSLF.NativeTypes.Instances.SpatialBag (driver installed)
open FrontDoorAgreement Embeddings

/-- **A payload language**: the atoms `a` and `b`. -/
def payloadCalc : LanguageDef where
  name := "Payloads"
  types := ["Atom"]
  terms := [
    { label := "a", category := "Atom", params := [], syntaxPattern := [] },
    { label := "b", category := "Atom", params := [], syntaxPattern := [] }]
  equations := []
  rewrites := []

theorem payload : Payload payloadCalc := ⟨rfl, rfl, by decide⟩

def a : Pattern := .apply "a" []
def b : Pattern := .apply "b" []

theorem payload_a : IsPayload payloadCalc a :=
  ⟨rfl, rfl, (checkOpenPatternWellSorted_sound (by decide +kernel :
    checkOpenPatternWellSorted (answers payloadCalc) FreeTypeContext.empty [] (.base "Atom") a = true)).1⟩

theorem payload_b : IsPayload payloadCalc b :=
  ⟨rfl, rfl, (checkOpenPatternWellSorted_sound (by decide +kernel :
    checkOpenPatternWellSorted (answers payloadCalc) FreeTypeContext.empty [] (.base "Atom") b = true)).1⟩

theorem payloads {items : List Pattern} (each : ∀ item ∈ items, item = a ∨ item = b) : Payloads payloadCalc items :=
  fun item member => by
    rcases each item member with rfl | rfl
    · exact payload_a
    · exact payload_b

/-! ## The generated front door over the answer language -/

theorem no_equations : (answers payloadCalc).equations = [] := rfl

theorem no_algebra : (answers payloadCalc).hasAlgebraDeclarations = false := answers_algebra payload

theorem guarded : (answers payloadCalc).rewrites.all (fun rule => rule.premises.all BagForms.guard) = true := rfl

/-- The bags' canonical forms. -/
def forms : CanonicalForms RelationEnv.empty (answers payloadCalc) 2 :=
  BagForms.forms no_equations no_algebra guarded 2

/-- The bag parts decider. -/
def decider : Decider RelationEnv.empty (answers payloadCalc) :=
  partsDecider (fuel := 2) (presentations := List.singleton) (BagForms.canonical no_equations no_algebra)
    (BagForms.coherent no_equations no_algebra guarded 2) (BagForms.parts no_equations no_algebra) 4

/-- The generated front door's answer about a driver formula at a bag, along the reading of the tests it names. -/
def frontAnswer (formula : driver.Formula) (items : List Pattern) : Option Bool :=
  frontDoorOn (reading RelationEnv.empty payload (leaves formula)) decider [] 2 formula (BagModel.encode items) 4
    (some forms)

/-- **The runtime agrees with the generated front door** about a driver formula at a bag of payloads. -/
theorem agrees (formula : driver.Formula) {items : List Pattern} (region : Payloads payloadCalc items) {answer : Bool}
    (answered : frontAnswer formula items = some answer) :
    AgreesOn installed formula (BagModel.encode items) answer :=
  agreesOn_of_frontDoorOn installed (reading RelationEnv.empty payload (leaves formula)) decider formula
    (atomsCovered_of_leaves formula fun _ member => member) rfl ⟨items, trivial, rfl⟩ region (by rfl) answered

/-! ## The verdicts -/

theorem packet_complete_answer : frontAnswer (BagModel.packet [b, b]) [b, b] = some true := by decide +kernel

/-- **`{b, b}` is exactly `b, b`.** -/
theorem packet_complete : AgreesOn installed (BagModel.packet [b, b]) (BagModel.encode [b, b]) true :=
  agrees _ (payloads (by decide)) packet_complete_answer

theorem packet_missing_copy_answer : frontAnswer (BagModel.packet [b]) [b, b] = some false := by decide +kernel

/-- **It is not exactly `b`.** -/
theorem packet_missing_copy : AgreesOn installed (BagModel.packet [b]) (BagModel.encode [b, b]) false :=
  agrees _ (payloads (by decide)) packet_missing_copy_answer

theorem packet_extra_copy_answer : frontAnswer (BagModel.packet [b, b, b]) [b, b] = some false := by decide +kernel

/-- **Nor exactly `b, b, b`.** -/
theorem packet_extra_copy : AgreesOn installed (BagModel.packet [b, b, b]) (BagModel.encode [b, b]) false :=
  agrees _ (payloads (by decide)) packet_extra_copy_answer

theorem packet_wrong_value_answer : frontAnswer (BagModel.packet [a, b]) [b, b] = some false := by decide +kernel

/-- **Nor exactly `a, b`.** -/
theorem packet_wrong_value : AgreesOn installed (BagModel.packet [a, b]) (BagModel.encode [b, b]) false :=
  agrees _ (payloads (by decide)) packet_wrong_value_answer

theorem second_copy_answer : frontAnswer (BagModel.atLeast b 2) [b, b] = some true := by decide +kernel

/-- **It has at least two `b`.** -/
theorem second_copy : AgreesOn installed (BagModel.atLeast b 2) (BagModel.encode [b, b]) true :=
  agrees _ (payloads (by decide)) second_copy_answer

theorem third_copy_absent_answer : frontAnswer (BagModel.atLeast b 3) [b, b] = some false := by decide +kernel

/-- **But not three.** -/
theorem third_copy_absent : AgreesOn installed (BagModel.atLeast b 3) (BagModel.encode [b, b]) false :=
  agrees _ (payloads (by decide)) third_copy_absent_answer

theorem singleton_is_exact_answer : frontAnswer (.atom (.singleton b)) [b, b] = some false := by decide +kernel

/-- **It is not the singleton `b`.** -/
theorem singleton_is_exact : AgreesOn installed (.atom (.singleton b)) (BagModel.encode [b, b]) false :=
  agrees _ (payloads (by decide)) singleton_is_exact_answer

theorem empty_accepted_answer : frontAnswer (BagModel.packet []) [] = some true := by decide +kernel

/-- **The empty bag is exactly nothing.** -/
theorem empty_accepted : AgreesOn installed (BagModel.packet []) (BagModel.encode []) true :=
  agrees _ (payloads (by decide)) empty_accepted_answer

theorem packet_permuted_answer : frontAnswer (BagModel.packet [a, b]) [b, a] = some true := by decide +kernel

/-- **`{b, a}` is exactly `a, b`**: the order of the answers does not matter. -/
theorem packet_permuted : AgreesOn installed (BagModel.packet [a, b]) (BagModel.encode [b, a]) true :=
  agrees _ (payloads (by decide)) packet_permuted_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBag.Controls
