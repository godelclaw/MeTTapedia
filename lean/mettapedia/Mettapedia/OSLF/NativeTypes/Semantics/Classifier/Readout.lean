import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Operations

/-! # Named predicate classifiers recover the original subfunctor exactly -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Readout

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.GSLT.Topos

universe u
variable {D : Presheaf.CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

theorem named_classifier_exact (carrier : D.Carrier) (kind : HSort)
    (predicate : Subfunctor (operational carrier)) (world : Wᵒᵖ)
    (value : (operational carrier).obj world) :
    Code.Member (.operational value)
      (.classifier kind (NativePowerPredicates.name (operational carrier) predicate world)) ↔
        value ∈ predicate.obj world := by
  have exactPredicate := NativePowerPredicates.membership_pairName (operational carrier) predicate
  exact Iff.of_eq (congrArg (fun subfunctor : Subfunctor (operational carrier) =>
    value ∈ subfunctor.obj world) exactPredicate)

theorem top_classifier_accepts (carrier : D.Carrier) (kind : HSort) (world : Wᵒᵖ)
    (value : (operational carrier).obj world) :
    Code.Member (.operational value)
      (.classifier kind (NativePowerPredicates.name (operational carrier) ⊤ world)) :=
  (named_classifier_exact operational carrier kind ⊤ world value).mpr trivial

theorem empty_classifier_rejects (carrier : D.Carrier) (kind : HSort) (world : Wᵒᵖ)
    (value : (operational carrier).obj world) :
    ¬ Code.Member (.operational value)
      (.classifier kind (NativePowerPredicates.name (operational carrier) ⊥ world)) :=
  (named_classifier_exact operational carrier kind ⊥ world value).mp

theorem operational_not_kinded (carrier : D.Carrier) (world : Wᵒᵖ)
    (value : (operational carrier).obj world) (kind : HSort) :
    ¬ Code.Member (.operational value : Code operational carrier world) (.sort kind) := by
  cases kind <;> exact id

theorem classifierName_substitution {P Q : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (kind : HSort) (predicate : P ⟶ NativePowerPredicates.power (operational carrier))
    (substitution : Q ⟶ P) :
    substitution ≫ Carrier.classifierName operational carrier kind predicate =
      Carrier.classifierName operational carrier kind (substitution ≫ predicate) := by
  ext world value
  rfl

theorem injection_monic (carrier : D.Carrier) (world : Wᵒᵖ) :
    Function.Injective ((Carrier.injection operational carrier).app world) := by
  intro first second same
  exact Code.operational.inj same

end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Readout
