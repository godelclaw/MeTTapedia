import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation
import Mettapedia.Logic.HOL.Embedding.CodedHypersetInterpretation

/-!
# Material codes for the full simple types of the hyperset model

The base sort is the actual set of all valid codes of small hypersets, one
universe above their graphs. Higher-order function types are actual sets of
total functional graphs over those codes. Decoding compares every type with
the full Henkin carrier, including whole higher-order function spaces.

This carrier is larger than a single small hyperset. It is distinct from the
member family of an individual code used in `CodedFamilyCwf`. Over the stated
closed-universe base, containing the base carrier is necessary and sufficient
for containing all these simple-type codes; no inaccessible-cardinal necessity
claim is inferred from this finite-type closure result.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.HOL.Embedding.HypersetHOLTypeInterpretation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ZFSetDependentProducts ZFSetHOLTypeInterpretation ZFSetUniverseClosure

universe u

def bases (_ : Unit) : ZFSet.{u + 1} := hsetCode.{u}

@[reducible] def typeCode : Ty Unit → ZFSet.{u + 1} := simpleTypeCode bases.{u}

abbrev Value (type : Ty Unit) := Elements (typeCode.{u} type)

def decode : (type : Ty Unit) → Value.{u} type ≃
    Ty.denote.{0, u + 1} HypersetHenkinInterpretation.carrier.{u} type :=
  simpleTypeEquiv bases (fun _ => CodedFamilies.carrierEquiv)

def lam {A B : Ty Unit} (body : Value.{u} A → Value B) : Value (.arr A B) :=
  encodeFunction (a := typeCode A) (b := fun _ => typeCode B) body

def app {A B : Ty Unit} (function : Value.{u} (.arr A B)) (argument : Value A) : Value B :=
  graphValue (a := typeCode A) (b := fun _ => typeCode B) function argument

theorem app_lam {A B : Ty Unit} (body : Value.{u} A → Value B) (argument : Value A) :
    app (lam body) argument = body argument :=
  congrFun (decode_encode_function (a := typeCode A) (b := fun _ => typeCode B) body) argument

theorem lam_eta {A B : Ty Unit} (function : Value.{u} (.arr A B)) :
    lam (fun argument => app function argument) = function :=
  encode_decode_function (a := typeCode A) (b := fun _ => typeCode B) function

theorem decode_app {A B : Ty Unit} (function : Value.{u} (.arr A B)) (argument : Value A) :
    decode B (app function argument) = decode (.arr A B) function (decode A argument) :=
  simpleTypeEquiv_app bases (fun _ => CodedFamilies.carrierEquiv) function argument

theorem decode_lam {A B : Ty Unit} (body : Value.{u} A → Value B) :
    decode (.arr A B) (lam body) = fun value => decode B (body ((decode A).symm value)) :=
  simpleTypeEquiv_lam bases (fun _ => CodedFamilies.carrierEquiv) body

/-- These particular material representations have extensional identity. -/
theorem equality_decode (presentation : HSet.Presentation.{u}) {A : Ty Unit} (left right : Value.{u} A) :
    left = right ↔ (HypersetHenkinInterpretation.model presentation).Eqv A (decode A left) (decode A right) := by
  constructor
  · rintro rfl
    exact (HypersetHenkinInterpretation.model presentation).eqv_refl
      (HypersetHenkinInterpretation.fullDomains presentation A _)
  · intro same
    apply (decode A).injective
    exact (HypersetHenkinInterpretation.model presentation).eq_of_eqv_of_fullDomains
      (HypersetHenkinInterpretation.fullDomains presentation) same

/-- Exact closure requirement for this recursive simple-type interpretation. -/
theorem all_typeCodes_mem_iff {U : ZFSet.{u + 1}} (closed : Closed U) :
    (∀ type : Ty Unit, typeCode.{u} type ∈ U) ↔ hsetCode.{u} ∈ U := by
  constructor
  · intro all
    exact all (.base ())
  · intro baseMember type
    exact simpleTypeCode_mem bases closed (truthCode_mem closed baseMember) (fun _ => baseMember) type

/-- The earlier host bound is a sufficient construction for every simple type. -/
theorem typeCode_mem_of_carrier_mem {U : ZFSet.{u + 1}} (closed : Closed U)
    (contains : ZFSetUniverseLift.carrierCode.{u} ∈ U) (type : Ty Unit) : typeCode.{u} type ∈ U :=
  (all_typeCodes_mem_iff closed).mpr (hsetCode_mem_of_carrierCode_mem closed contains) type

theorem value_mem {U : ZFSet.{u + 1}} (closed : Closed U) (contains : hsetCode.{u} ∈ U)
    (type : Ty Unit) (value : Value.{u} type) : value.1 ∈ U :=
  closed.transitive _ ((all_typeCodes_mem_iff closed).mpr contains type) value.2

/-- The whole base carrier cannot serve as its own enclosing universe. -/
theorem not_self_contained : ¬ ∀ type : Ty Unit, typeCode.{u} type ∈ hsetCode.{u} :=
  fun all => ZFSet.mem_irrefl _ (all (.base ()))

/-- A cyclic guest value is still an element of the well-founded material
base code. Its cycle belongs to interpreted membership, not graph membership. -/
def quine : Value.{u} (.base ()) := CodedFamilies.encode HSet.quineAtom

theorem quine_decode : decode (.base ()) quine.{u} = HSet.quineAtom :=
  CodedFamilies.decode_encode _

theorem quine_memberships : codeMem quine.{u}.1 quine.{u}.1 ∧ quine.{u}.1 ∉ quine.{u}.1 :=
  CodedHypersetInterpretation.memberships_distinct.{u}

end Mettapedia.Logic.HOL.Embedding.HypersetHOLTypeInterpretation
