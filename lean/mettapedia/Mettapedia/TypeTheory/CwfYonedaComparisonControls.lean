import Mettapedia.TypeTheory.CwfYonedaComparisonUniverse
import Mettapedia.TypeTheory.ContextualProductCellUniquenessControls

/-!
# Varying dependent comparison controls

The source has independent context and term sizes. Both complete native
comparisons retain varying finite witnesses. A nonidentity environment
changes the actual readout. The negative profile retains a Boolean in each
function: beta and substitution hold, while complete native abstraction
forgets that Boolean because source eta fails.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfYonedaComparisonControls

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualProductSections
open CwfYonedaComparisonUniverse DisplayedPresheafPi
open ContextualSumComprehensionControls (varyingDomain varyingCodomain familySums)

abbrev original := familiesCwf.{0}
abbrev represented : Cwf.{1, 1, 1, 0} := representedModel original

def sourceProducts : StableProducts original where
  operations := Families.products
  beta := PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts
  substitution := Families.products_substitution
  eta := ContextualProductCellUniquenessControls.family_eta

abbrev products := representedProducts sourceProducts
abbrev sums := representedSums familySums.{0}
abbrev context : represented.Ctx := ⟨Nat⟩
abbrev domain : represented.Ty context := ⟨varyingDomain⟩
abbrev codomain : represented.Ty (represented.ext context domain) := ⟨varyingCodomain⟩

def diagonal : represented.Tm context domain :=
  ⟨fun n => ⟨n, Nat.lt_succ_self n⟩⟩

def body : represented.Tm (represented.ext context domain) codomain :=
  ⟨fun point => ⟨point.2.val, by change point.2.val < point.1 + point.2.val + 1; omega⟩⟩

def function : represented.Tm context (products.operations.pi domain codomain) :=
  products.operations.lam body

def second : represented.Tm context (represented.tySub codomain
    (ContextualProductComparison.selfExtend represented diagonal)) :=
  ⟨fun n => ⟨n, by
    change n < n + n + 1
    exact Nat.lt_succ_of_le (Nat.le_add_right n n)⟩⟩

def paired : represented.Tm context (sums.operations.sigma domain codomain) :=
  sums.operations.pair diagonal second

def successor : represented.Sub context context := ⟨fun n => n + 1⟩

noncomputable def nativeFunction := CwfYoneda.interpretFunction represented products function
noncomputable def nativeApplied := appDisplayed nativeFunction (CwfYoneda.interpretTerm represented diagonal)

theorem source_fibres_actually_vary :
    Fintype.card (domain.down 0) = 1 ∧ Fintype.card (domain.down 1) = 2 ∧
      Fintype.card (codomain.down ⟨1, ⟨0, by decide⟩⟩) = 2 ∧
      Fintype.card (codomain.down ⟨1, ⟨1, by decide⟩⟩) = 3 := by decide

theorem native_application_retains_witness (n : Nat) :
    ((nativeApplied.val ⟨op (CwfYoneda.context represented context), represented.idS context⟩).val.down n).2.val = n := by
  have reading := CwfYoneda.interpretFunction_application represented products function diagonal
    (op (CwfYoneda.context represented context)) (represented.idS context)
  exact congrArg (fun arrow : represented.Sub context
    (represented.ext (represented.ext context domain) codomain) => (arrow.down n).2.val) reading

theorem native_application_future_witness (n : Nat) :
    ((nativeApplied.val ⟨op (CwfYoneda.context represented context), successor⟩).val.down n).2.val = n + 1 := by
  have reading := CwfYoneda.interpretFunction_application represented products function diagonal
    (op (CwfYoneda.context represented context)) successor
  exact congrArg (fun arrow : represented.Sub context
    (represented.ext (represented.ext context domain) codomain) => (arrow.down n).2.val) reading

theorem omitted_future_substitution_is_detected (n : Nat) :
    ((nativeApplied.val ⟨op (CwfYoneda.context represented context), successor⟩).val.down n).2.val ≠
      ((nativeApplied.val ⟨op (CwfYoneda.context represented context), represented.idS context⟩).val.down n).2.val := by
  rw [native_application_retains_witness, native_application_future_witness]
  omega

noncomputable def nativePair :=
  (CwfYoneda.sumFamilyIso represented sums domain codomain).hom.app
    ⟨op (CwfYoneda.context represented context), successor⟩
    ((CwfYoneda.interpretTerm represented paired).val
      ⟨op (CwfYoneda.context represented context), successor⟩)

theorem native_pair_retains_both (n : Nat) :
    (nativePair.1.val.down n).2.val = n + 1 ∧
      (nativePair.2.val.down n).2.val = n + 1 := ⟨rfl, rfl⟩

theorem original_application_readout (n : Nat) :
    ((products.operations.app function diagonal).down n).val = n := rfl

noncomputable def nativeCompleteFunction :=
  (CwfYoneda.productFamilyIso represented products domain codomain).hom.app
    ⟨op (CwfYoneda.context represented context), successor⟩
    ((CwfYoneda.interpretTerm represented function).val
      ⟨op (CwfYoneda.context represented context), successor⟩)

theorem native_generic_application (n : Nat) (argument : Fin (n + 2)) :
    (((CwfYoneda.representedProductGenericIso represented domain codomain successor).hom
      nativeCompleteFunction).val.down ⟨n, argument⟩).2.val = argument.val := by
  have reading := CwfYoneda.productFamilyForward_generic represented products domain codomain successor
    ((CwfYoneda.interpretTerm represented function).val
      ⟨op (CwfYoneda.context represented context), successor⟩)
  rw [← CwfYoneda.productFamilyIso_hom] at reading
  exact congrArg (fun receipt => (receipt.val.down ⟨n, argument⟩).2.val) reading

theorem full_native_function_roundtrip
    (native : (CwfYoneda.representedProductFamily represented domain codomain).obj
      ⟨op (CwfYoneda.context represented context), successor⟩) :
    CwfYoneda.productFibreEquiv represented products domain codomain successor
      ((CwfYoneda.productFibreEquiv represented products domain codomain successor).symm native) = native :=
  (CwfYoneda.productFibreEquiv represented products domain codomain successor).apply_symm_apply native

abbrev hiddenOperations := ContextualProductCellUniquenessControls.hiddenProducts
abbrev hiddenFormed : StrictPiFormationSubstitution hiddenOperations :=
  ContextualProductCellUniquenessControls.hidden_substitution.1

def hiddenSourceFunction (mark : Bool) : represented.Tm context
    (ULift.up (hiddenOperations.pi varyingDomain varyingCodomain)) :=
  ULift.up (ContextualProductCellUniquenessControls.suppliedHidden mark)

noncomputable def hiddenNativeFunction (mark : Bool) :=
  lamDisplayed (CwfYoneda.bodyTermSectionEquiv represented domain codomain
    (ULift.up (ContextualPiEta.genericSection hiddenOperations hiddenFormed
      (ContextualProductCellUniquenessControls.suppliedHidden mark))))

theorem hidden_native_abstractions_agree : hiddenNativeFunction false = hiddenNativeFunction true := by
  exact congrArg (fun sectionValue : original.Tm
    (original.ext Nat varyingDomain) varyingCodomain =>
      lamDisplayed (CwfYoneda.bodyTermSectionEquiv represented domain codomain (ULift.up sectionValue)))
    ContextualProductCellUniquenessControls.hidden_generic_application_agrees

theorem hidden_source_sections_remain_distinct :
    CwfYoneda.interpretTerm represented (hiddenSourceFunction false) ≠
      CwfYoneda.interpretTerm represented (hiddenSourceFunction true) := by
  intro equal
  have originalEqual := (CwfYoneda.termSectionEquiv represented
    (ULift.up (hiddenOperations.pi varyingDomain varyingCodomain))).injective equal
  exact ContextualProductCellUniquenessControls.hidden_functions_differ
    (congrArg ULift.down originalEqual)

end Mettapedia.TypeTheory.CwfYonedaComparisonControls
