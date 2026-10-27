import Mettapedia.Logic.HOL.GeneratedFamilyPredicate
import Mettapedia.Logic.HOL.VectorContainerPositionPrograms
import Mettapedia.Logic.HOL.SuccessorOrder
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace
import Mettapedia.TypeTheory.IndexedPolynomialMappedPredicate

/-!
# The generated Vector-container family in recursive-tree semantics

The model interprets the actual generated guards over natural numbers and
recursive-space trees carrying predicate-handler payloads. The source is the
registered indexed Vector code. Its shape data is reconstructed from the
stored length, and the payload map distinguishes absence from every length.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel
open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory
open IndexedPositiveContainer IndexedPolynomial.RecursiveSpaceRepresentation
open IndexedConstructorGuards FiniteConstructorEncoding

noncomputable def presentation :=
  IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation VectorControl.orderedFinitary VectorControl.code
abbrev Point := Σ index, presentation.polynomial.Shape VectorControl.environment index

def point (length : Nat) : Point := ⟨(), VectorControl.shapeAt length⟩
def pointLength (value : Point) : Nat := value.2.1

theorem point_readback (value : Point) : point (pointLength value) = value := by
  rcases value with ⟨index, length, container, equation⟩
  cases index
  cases container
  cases equation with
  | up equation =>
      cases equation with
      | up equation => rfl


universe u v w

/-- Primitive carrier and operation comparisons for the registered Vector
container. Shape, position, edge and family membership laws are derived below. -/
structure CarrierReading {Base : Type u} {Const : Ty Base → Type v}
    (model : HenkinModel.{u,v,w} Base Const) where
  number : Ty Base
  space : Ty Base
  numeral : Nat → ClosedTerm Const number
  less : ClosedTerm Const (number ⇒ number ⇒ .prop)
  bottom : ClosedTerm Const space
  construct : ClosedTerm Const (number ⇒ payloadType [[number]] ⇒ (number ⇒ space) ⇒ space)
  numbers : Nat ≃ Ty.denote model.Carrier number
  trees : RecursiveSpace.Tree (Ty.denote model.Carrier (payloadType [[number]])) ≃
    Ty.denote model.Carrier space
  zero : RecursiveSpacePredicate.Signature.denotes model (numeral 0) = numbers 0
  less_iff : ∀ slot length,
    (RecursiveSpacePredicate.Signature.denotes model less (numbers slot) (numbers length)).down ↔ slot < length
  bottom_eq : trees RecursiveSpace.bottom = RecursiveSpacePredicate.Signature.denotes model bottom
  construct_eq : ∀ tag payload children,
    trees (RecursiveSpace.construct tag payload children) =
      RecursiveSpacePredicate.Signature.denotes model construct (numbers tag) payload
        (fun n => trees (children (numbers.symm n)))

namespace CarrierReading
variable {Base : Type u} {Const : Ty Base → Type v}
  {model : HenkinModel.{u,v,w} Base Const} (reading : CarrierReading model)

def constructors := VectorContainerPositionPrograms.constructors reading.number reading.numeral
def positions := VectorContainerPositionPrograms.positions reading.number reading.numeral reading.less
def signature := reading.positions.signature reading.bottom reading.construct
abbrev Payload := Ty.denote model.Carrier (payloadType [[reading.number]])
abbrev Tree := RecursiveSpace.Tree reading.Payload
def values (_reading : CarrierReading model) : model.Valuation [] := fun impossible => nomatch impossible

def data (length : Nat) : reading.constructors.Data model :=
  ⟨⟨0, by change 0 < 1; decide⟩, reading.numbers length, PUnit.unit⟩
def packed (length : Nat) : reading.Payload := reading.constructors.packedData model (reading.data length)
def unused : reading.Payload := fun _ => ULift.up False

theorem data_unique (value : reading.constructors.Data model) : ∃ length, value = reading.data length := by
  rcases value with ⟨occurrence, fields⟩
  have same : occurrence = ⟨0, by change 0 < 1; decide⟩ := by
    apply Fin.ext
    have bound := occurrence.isLt
    change occurrence.val < 1 at bound
    change occurrence.val = 0
    omega
  cases same
  rcases fields with ⟨length, ⟨⟩⟩
  exact ⟨reading.numbers.symm length, by simp only [data, Equiv.apply_symm_apply]⟩

theorem data_injective : Function.Injective reading.data := by
  intro first second same
  have fields := eq_of_heq (Sigma.mk.inj same).2
  exact reading.numbers.injective (congrArg Prod.fst fields)

theorem packed_injective : Function.Injective reading.packed :=
  reading.constructors.packedData_injective model |>.comp reading.data_injective

theorem packed_ne_unused (length : Nat) : reading.packed length ≠ reading.unused := by
  intro same
  have observed := congrFun same (fun _ => ULift.up True)
  change ULift.up True = ULift.up False at observed
  exact (congrArg ULift.down observed).mp True.intro

def payloadMap : RecursivePayload presentation VectorControl.environment → reading.Payload
  | none => reading.unused
  | some value => reading.packed (pointLength value)

theorem payloadMap_injective : Function.Injective reading.payloadMap := by
  intro first second same
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some value => exact False.elim (reading.packed_ne_unused _ same.symm)
  | some first =>
      cases second with
      | none => exact False.elim (reading.packed_ne_unused _ same)
      | some second =>
          have lengths := reading.packed_injective same
          exact congrArg some ((point_readback first).symm.trans
            ((congrArg point lengths).trans (point_readback second)))

theorem allowed (length : Nat) : reading.constructors.dataAllowed model reading.values (reading.data length) := True.intro
theorem result_index (length : Nat) :
    reading.constructors.resultValue model reading.values (reading.data length) = ULift.up True := rfl

theorem relation_iff (full : model.FullDomains) (length slot : Nat)
    (index : Ty.denote model.Carrier Ty.prop) :
    reading.positions.related model reading.values (reading.data length) (reading.numbers slot) index ↔
      slot < length ∧ index = ULift.up True := by
  exact (VectorContainerPositionPrograms.related_iff model full reading.number reading.numeral reading.less
    reading.values (reading.numbers length) (reading.numbers slot) index).trans
    (and_congr (by simpa only [RecursiveSpacePredicate.Signature.denote_closed] using
      reading.less_iff slot length) Iff.rfl)

#print axioms payloadMap_injective
#print axioms relation_iff
end CarrierReading

inductive SortCode where | number | space
abbrev number : Ty SortCode := .base .number
abbrev space : Ty SortCode := .base .space
abbrev payload : Ty SortCode := payloadType [[number]]
abbrev NumberValue := ULift.{1} Nat
abbrev PayloadValue := (NumberValue → ULift.{1} Prop) → ULift.{1} Prop
abbrev Tree := RecursiveSpace.Tree PayloadValue

inductive Symbol : Ty SortCode → Type where
  | zero : Symbol number
  | successor : Symbol (number ⇒ number)
  | bottom : Symbol space
  | construct : Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)

def carrier : SortCode → Type 1
  | .number => NumberValue
  | .space => Tree
def model : HenkinModel.{0,0,0} SortCode Symbol := .standard carrier
  (fun symbol => match symbol with
    | .zero => .up 0
    | .successor => fun n => .up (n.down + 1)
    | .bottom => RecursiveSpace.bottom
    | .construct => fun tag payload children =>
        RecursiveSpace.construct tag.down payload (fun n => children (.up n)))
def values : model.Valuation [] := fun impossible => nomatch impossible
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _
def successor : ClosedTerm Symbol (number ⇒ number) := .const .successor
def numeral : Nat → ClosedTerm Symbol number
  | 0 => .const .zero
  | n + 1 => .app successor (numeral n)
def constructors := VectorContainerPositionPrograms.constructors number numeral
def positions := VectorContainerPositionPrograms.positions number numeral (SuccessorOrder.less successor)
def construct : ClosedTerm Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space) := .const .construct
def bottom : ClosedTerm Symbol space := .const .bottom
def signature := positions.signature bottom construct

/-- The original recursive-tree model instantiates the same carrier interface
as received source models. -/
def referenceCarrier : CarrierReading model where
  number := number
  space := space
  numeral := numeral
  less := SuccessorOrder.less successor
  bottom := bottom
  construct := construct
  numbers := Equiv.ulift.symm
  trees := Equiv.refl _
  zero := rfl
  less_iff := by
    intro slot length
    have law := SuccessorOrder.less_iff model full successor values Equiv.ulift.symm
      (fun _ => rfl) (ULift.up slot) (ULift.up length)
    change (model.denote (SuccessorOrder.less successor) values (ULift.up slot) (ULift.up length)).down ↔
      slot < length at law
    rw [← RecursiveSpacePredicate.Signature.denote_closed model (SuccessorOrder.less successor) values]
    exact law
  bottom_eq := rfl
  construct_eq := fun _ _ _ => rfl

def data (length : Nat) : constructors.Data model := ⟨⟨0, by decide⟩, ULift.up length, PUnit.unit⟩
def packed (length : Nat) : PayloadValue := constructors.packedData model (data length)
def unused : PayloadValue := fun _ => ULift.up False

theorem data_unique (value : constructors.Data model) : ∃ length, value = data length := by
  rcases value with ⟨occurrence, fields⟩
  have same : occurrence = ⟨0, by decide⟩ := by
    apply Fin.ext
    have bound := occurrence.isLt
    change occurrence.val < 1 at bound
    change occurrence.val = 0
    omega
  cases same
  rcases fields with ⟨⟨length⟩, ⟨⟩⟩
  exact ⟨length, rfl⟩

theorem data_injective : Function.Injective data := by
  intro first second same
  have fields := eq_of_heq (Sigma.mk.inj same).2
  exact congrArg (fun pair => pair.1.down) fields

theorem packed_injective : Function.Injective packed :=
  constructors.packedData_injective model |>.comp data_injective

theorem packed_ne_unused (length : Nat) : packed length ≠ unused := by
  intro same
  have observed := congrFun same (fun _ => ULift.up True)
  change ULift.up True = ULift.up False at observed
  exact (congrArg ULift.down observed).mp True.intro


def payloadMap : RecursivePayload presentation VectorControl.environment → PayloadValue
  | none => unused
  | some value => packed (pointLength value)

theorem payloadMap_injective : Function.Injective payloadMap := by
  intro first second same
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some value => exact False.elim (packed_ne_unused _ same.symm)
  | some first =>
      cases second with
      | none => exact False.elim (packed_ne_unused _ same)
      | some second =>
          have lengths := packed_injective same
          exact congrArg some ((point_readback first).symm.trans
            ((congrArg point lengths).trans (point_readback second)))

theorem allowed (length : Nat) : constructors.dataAllowed model values (data length) := True.intro
theorem result_index (length : Nat) : constructors.resultValue model values (data length) = ULift.up True := rfl

theorem relation_iff (length slot : Nat) (index : Ty.denote.{0,0} model.Carrier Ty.prop) :
    positions.related model values (data length) (ULift.up slot) index ↔
      slot < length ∧ index = ULift.up True :=
  (VectorContainerPositionPrograms.related_iff model full number numeral (SuccessorOrder.less successor)
    values (ULift.up length) (ULift.up slot) index).trans
    (and_congr (SuccessorOrder.less_iff model full successor values Equiv.ulift.symm
      (fun _ => rfl) (ULift.up slot) (ULift.up length)) Iff.rfl)

#print axioms payloadMap_injective
#print axioms point_readback
#print axioms relation_iff
end Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel
