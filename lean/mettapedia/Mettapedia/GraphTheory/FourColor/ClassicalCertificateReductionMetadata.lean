import Mettapedia.GraphTheory.FourColor.ClassicalCertificateExactTraceEnumeration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadata

open ClassicalCertificateConfiguration
open ClassicalCertificateContractComponents
open ClassicalCertificateExactTraceEnumeration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateTraceTree

/-- Finite data needed to interpret one catalogue configuration as a checked
contracted boundary-coloring problem. -/
structure Code where
  hypermap : HypermapCode
  ringValues : List Nat
  contractValues : List Nat
  partition : ClassicalCertificateFacePartition.Code
  components : ClassicalCertificateContractComponents.Code
  orderValues : List Nat
  deriving DecidableEq, Repr

/-- The independently executable hypermap constructed by a configuration
program. -/
def materialized (configuration : Configuration) : HypermapCode :=
  HypermapCode.materialize configuration.compile.pointee

/-- Decode a list of natural-number indices, dropping any out-of-range value.
Accepted metadata proves that no value is dropped. -/
def finsOfValues (bound : Nat) (values : List Nat) : List (Fin bound) :=
  match values with
  | [] => []
  | value :: values =>
      if h : value < bound then
        ⟨value, h⟩ :: finsOfValues bound values
      else
        finsOfValues bound values

def ValuesInRange (bound : Nat) (values : List Nat) : Prop :=
  ∀ value ∈ values, value < bound

instance (bound : Nat) (values : List Nat) :
    Decidable (ValuesInRange bound values) := by
  unfold ValuesInRange
  infer_instance

theorem map_finsOfValues_val {bound : Nat} {values : List Nat}
    (hinRange : ValuesInRange bound values) :
    (finsOfValues bound values).map Fin.val = values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      have hvalue : value < bound := hinRange value (by simp)
      have htail : ValuesInRange bound values := by
        intro other hother
        exact hinRange other (by simp [hother])
      simp [finsOfValues, hvalue, ih htail]

def ring (code : Code) : List (Fin code.hypermap.dartCount) :=
  finsOfValues code.hypermap.dartCount code.ringValues

def contract (code : Code) : Finset (Fin code.hypermap.dartCount) :=
  (finsOfValues code.hypermap.dartCount code.contractValues).toFinset

def order (code : Code) :
    List (Fin code.components.componentCount) :=
  finsOfValues code.components.componentCount code.orderValues

/-- Raw index bounds checked before dependent objects are used. -/
def IndexConditions (code : Code) : Prop :=
  ValuesInRange code.hypermap.dartCount code.ringValues ∧
    ValuesInRange code.hypermap.dartCount code.contractValues ∧
    ValuesInRange code.components.componentCount code.orderValues

instance (code : Code) : Decidable (IndexConditions code) := by
  unfold IndexConditions
  infer_instance

/-- Boundary geometry and completeness of the component-coloring order. -/
def GeometricConditions (code : Code) : Prop :=
  RawReverseBoundaryCycle code.hypermap (ring code) ∧
    ContractAvoidsBoundary (contract code) (ring code) ∧
    ∀ component : Fin code.components.componentCount,
      component ∈ order code

instance (code : Code) : Decidable (GeometricConditions code) := by
  unfold GeometricConditions
  infer_instance

/-- Reflected checker for one complete reduction-metadata record. -/
def checker (code : Code) : Bool :=
  decide (IndexConditions code) &&
    if hpartition : ClassicalCertificateFacePartition.checker
        code.hypermap code.partition = true then
      let partitionValid :=
        ClassicalCertificateFacePartition.valid_of_checker_true
          code.hypermap code.partition hpartition
      ClassicalCertificateContractComponents.checker partitionValid
          (contract code) code.components &&
        decide (GeometricConditions code)
    else false

/-- Semantic data obtained from an accepted metadata record. -/
structure Valid (code : Code) : Prop where
  indexConditions : IndexConditions code
  partitionAccepted : ClassicalCertificateFacePartition.checker
    code.hypermap code.partition = true
  componentsAccepted : ClassicalCertificateContractComponents.checker
    (ClassicalCertificateFacePartition.valid_of_checker_true
      code.hypermap code.partition partitionAccepted)
      (contract code) code.components = true
  geometry : GeometricConditions code

theorem valid_of_checker_true (code : Code) (hchecker : checker code = true) :
    Valid code := by
  simp only [checker, Bool.and_eq_true] at hchecker
  have hindices : IndexConditions code :=
    Bool.of_decide_true hchecker.1
  by_cases hpartition : ClassicalCertificateFacePartition.checker
      code.hypermap code.partition = true
  · simp only [hpartition, ↓reduceDIte, Bool.and_eq_true] at hchecker
    exact ⟨hindices, hpartition, hchecker.2.1,
      Bool.of_decide_true hchecker.2.2⟩
  · simp [hpartition] at hchecker

/-- Exact provenance connecting locally checked metadata to an original
catalogue construction program.  It is deliberately separate from `checker`:
the catalogue-wide normalized-program checker supplies these equalities once,
without replaying the recursive compiler inside every local reduction check. -/
structure ProgramLink (configuration : Configuration) (code : Code) : Prop where
  hypermap_eq : materialized configuration = code.hypermap
  ringValues_eq : code.ringValues = configuration.compile.forwardRing
  contractValues_eq : code.contractValues = configuration.contractDarts

/-- A locally accepted reduction record together with its construction
provenance. -/
structure Certified (configuration : Configuration) (code : Code) : Prop where
  valid : Valid code
  link : ProgramLink configuration code

namespace Valid

variable {code : Code}

def partitionValid (valid : Valid code) :
    ClassicalCertificateFacePartition.Valid
      code.hypermap code.partition :=
  ClassicalCertificateFacePartition.valid_of_checker_true
    code.hypermap code.partition valid.partitionAccepted

def componentsValid (valid : Valid code) :
    ClassicalCertificateContractComponents.Valid (partitionValid valid)
      (contract code) code.components :=
  ClassicalCertificateContractComponents.valid_of_checker_true
    (partitionValid valid) (contract code) code.components (by
      simpa [partitionValid] using valid.componentsAccepted)

theorem ring_map_val (valid : Valid code) :
    (ring code).map Fin.val = code.ringValues :=
  map_finsOfValues_val valid.indexConditions.1

theorem contract_list_map_val (valid : Valid code) :
    (finsOfValues code.hypermap.dartCount
      code.contractValues).map Fin.val = code.contractValues :=
  map_finsOfValues_val valid.indexConditions.2.1

theorem order_map_val (valid : Valid code) :
    (order code).map Fin.val = code.orderValues :=
  map_finsOfValues_val valid.indexConditions.2.2

theorem reverseBoundaryCycle (valid : Valid code) :
    RawReverseBoundaryCycle code.hypermap (ring code) :=
  valid.geometry.1

theorem contractAvoidsBoundary (valid : Valid code) :
    ContractAvoidsBoundary (contract code) (ring code) :=
  valid.geometry.2.1

theorem orderComplete (valid : Valid code)
    (component : Fin code.components.componentCount) :
    component ∈ order code :=
  valid.geometry.2.2 component

/-- An accepted metadata record instantiates the exact trace enumerator with
the standard contract-ring semantics. -/
theorem enumerate_accepts_iff_contractRingTrace
    (valid : Valid code) (word : List TraceSymbol) :
    (enumerate (componentsValid valid) (ring code) (order code)).accepts word = true ↔
      FiniteHypermap.ContractRingTrace
        (checkedHypermap (partitionValid valid))
          (contract code) (ring code)
            (word.map TraceSymbol.toColor) := by
  exact
    ClassicalCertificateExactTraceEnumeration.enumerate_accepts_iff_contractRingTrace
      (componentsValid valid) (ring code) (order code) (orderComplete valid)
        (reverseBoundaryCycle valid) (contractAvoidsBoundary valid) word

end Valid

end ClassicalCertificateReductionMetadata

end Mettapedia.GraphTheory.FourColor
