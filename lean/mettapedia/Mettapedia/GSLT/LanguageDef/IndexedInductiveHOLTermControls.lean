import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms

/-!
# Constructor-index program controls

The arithmetic symbols denote the admitted Natural operations. The generated
Vector constructor returns the successor length while its child function
returns the original length. A recursive field preceding a later data binder
exercises abstraction of data that the earlier index expression cannot use.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms.Controls

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open IndexedInductiveNatVec

inductive SortCode where | number | element
abbrev number : Ty SortCode := .base .number
abbrev element : Ty SortCode := .base .element

inductive Symbol : Ty SortCode → Type where
  | zero : Symbol number
  | successor : Symbol (number ⇒ number)
  | addition : Symbol (number ⇒ number ⇒ number)

@[reducible] def arithmetic : Arithmetic Symbol :=
  ⟨number, element, .const .zero, .const .successor, .const .addition⟩

def carrier : SortCode → Type 1
  | .number => ULift.{1} Natural.Carrier
  | .element => ULift.{1} Bool

@[reducible] noncomputable def model : HenkinModel.{0,0,0} SortCode Symbol :=
  .standard carrier (fun symbol => match symbol with
    | .zero => .up Natural.zero
    | .successor => fun value => .up (Natural.succ value.down)
    | .addition => fun first second => .up (Natural.add first.down second.down))

noncomputable abbrev empty : model.Valuation [] := Arithmetic.emptyValuation model

noncomputable def consData : ConstructorData (Vectors.consCode Bool) :=
  (Natural.succ Natural.zero, true, PUnit.unit)

theorem cons_result :
    (arithmetic.reading Bool).applyData model
      (arithmetic.encodeData Bool model ULift.up ULift.up) (dataSorts (Vectors.consCode Bool))
      (model.denote (arithmetic.resultProgram Bool) empty) consData =
      ULift.up (Natural.succ (Natural.succ Natural.zero)) := by
  simpa only [Arithmetic.resultProgram, IndexedConstructorTerms.Reading.valuation,
    dataResultIndex, Vectors.consCode, Vectors.interface, Vectors.IndexExpr.eval,
    Vectors.LengthVariable.lookup, consData] using
    arithmetic.constructor_result_denote Bool model ULift.up ULift.up rfl
    (fun _ => rfl) (fun _ _ => rfl) (Vectors.consCode Bool) PUnit.unit consData

theorem cons_child :
    (arithmetic.reading Bool).applyData model
      (arithmetic.encodeData Bool model ULift.up ULift.up) (dataSorts (Vectors.consCode Bool))
      (model.denote (arithmetic.childProgram Bool) empty) consData =
      ULift.up (Natural.succ Natural.zero) := by
  have generated := arithmetic.constructor_child_denote Bool model ULift.up ULift.up rfl
    (fun _ => rfl) (fun _ _ => rfl) (Vectors.consCode Bool) PUnit.unit consData
    ⟨0, by change 0 < 1; decide⟩
  have indexValue : dataRecursiveIndexAt (Vectors.consCode Bool) PUnit.unit consData
      ⟨0, by change 0 < 1; decide⟩ = Natural.succ Natural.zero := rfl
  simpa only [Arithmetic.childProgram, IndexedConstructorTerms.Reading.valuation] using
    generated.trans (congrArg ULift.up indexValue)

theorem result_is_not_child :
    model.denote (arithmetic.resultProgram Bool) empty ≠
      model.denote (arithmetic.childProgram Bool) empty := by
  intro same
  have applied := congrArg
    (fun function => (arithmetic.reading Bool).applyData model
      (arithmetic.encodeData Bool model ULift.up ULift.up) (dataSorts (Vectors.consCode Bool))
      function consData) same
  rw [cons_result, cons_child] at applied
  have impossible := congrArg (fun value => Natural.toNat value.down) applied
  change (2 : Nat) = 1 at impossible
  cases impossible

def laterData : Code (Vectors.interface Bool) [.length] :=
  .recursive (.variable .here)
    (.data .payload (.result (.successor (.variable (.there .here)))))

theorem earlier_child_ignores_later_data :
    (arithmetic.reading Bool).applyData model
      (arithmetic.encodeData Bool model ULift.up ULift.up) (dataSorts laterData)
      (model.denote ((arithmetic.reading Bool).childProgram laterData ⟨0, by change 0 < 1; decide⟩)
        ((arithmetic.reading Bool).valuation model
          (arithmetic.encodeData Bool model ULift.up ULift.up)
          empty (context := [.length])
          (Natural.succ Natural.zero, PUnit.unit)))
      (false, PUnit.unit) = ULift.up (Natural.succ Natural.zero) := by
  have generated := arithmetic.constructor_child_denote Bool model ULift.up ULift.up rfl
    (fun _ => rfl) (fun _ _ => rfl) laterData
    (Natural.succ Natural.zero, PUnit.unit) (false, PUnit.unit)
    ⟨0, by change 0 < 1; decide⟩
  have indexValue : dataRecursiveIndexAt laterData
      (Natural.succ Natural.zero, PUnit.unit) (false, PUnit.unit)
      ⟨0, by change 0 < 1; decide⟩ = Natural.succ Natural.zero := rfl
  exact generated.trans (congrArg ULift.up indexValue)

#print axioms cons_result
#print axioms cons_child
#print axioms result_is_not_child
#print axioms earlier_child_ignores_later_data

end Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms.Controls
