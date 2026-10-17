import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyRequests
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementScopeResize

/-! # The generated request projection is the actual double comprehension projection -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyRequestProjection

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open DisplayedPresheafComprehension
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Classifier Families Operations CertifiedProjection

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)
variable (rely target focus : D.Carrier) (kind sort : HSort)

noncomputable section
attribute [local irreducible] Classifier.Model.model

abbrev iface := SingleRelyParameters.interface rely target focus kind sort
abbrev model := Classifier.Model.model operational algebra vertex
abbrev params : Scope W 2 := ContinuationSemantics.parameterScope operational algebra vertex
  (iface rely target focus kind sort)
abbrev actual := SingleRelyRequests.targetScope operational algebra vertex rely target focus kind sort
abbrev requests := SingleRelyRequests.requests operational algebra vertex rely target focus kind sort

variable (A : NativeType (params operational algebra vertex rely target focus kind sort).1)
    (B : NativeType (totalSpace A.decoded))

abbrev complete : Scope W 4 := ((params operational algebra vertex rely target focus kind sort).snoc A).snoc B

abbrev twoProjection : (complete operational algebra vertex rely target focus kind sort A B).1 ⟶
    (params operational algebra vertex rely target focus kind sort).1 :=
  totalProjection B.decoded ≫ totalProjection A.decoded

private def projectionMap : ModelSubstitution (model operational algebra vertex)
    (complete operational algebra vertex rely target focus kind sort A B)
    (params operational algebra vertex rely target focus kind sort)
    (fun position => .var position.succ.succ) where
  arrow := twoProjection operational algebra vertex rely target focus kind sort A B
  readout position := by
    change some (Value.substitute (K := (NativeModel W).toCwf)
      (Value.substitute (K := (NativeModel W).toCwf)
        ((params operational algebra vertex rely target focus kind sort).2.lookup position)
        (totalProjection A.decoded)) (totalProjection B.decoded)) = _
    exact congrArg some (Value.substitute_composition (K := (NativeModel W).toCwf)
      ((params operational algebra vertex rely target focus kind sort).2.lookup position)
      (totalProjection A.decoded) (totalProjection B.decoded)).symm

variable (same : Scope.resize (SingleRelyBeta.requestSize vertex rely target focus kind sort)
  (actual operational algebra vertex rely target focus kind sort) =
    complete operational algebra vertex rely target focus kind sort A B)

/-- Relabelling preserves the actual request presheaf. The earned equality
of scoped interpretations supplies only its canonical change of presentation. -/
def change : (actual operational algebra vertex rely target focus kind sort).1 ≅
    (complete operational algebra vertex rely target focus kind sort A B).1 :=
  eqToIso (congrArg (fun scope : Scope W 4 => scope.1) same)

theorem project_eq :
    (requests operational algebra vertex rely target focus kind sort).project =
      (change operational algebra vertex rely target focus kind sort A B same).hom ≫
        twoProjection operational algebra vertex rely target focus kind sort A B := by
  have read := (model operational algebra vertex).evaluateSubstitution_resize_source
    (SingleRelyBeta.requestSize vertex rely target focus kind sort)
    (actual operational algebra vertex rely target focus kind sort)
    (params operational algebra vertex rely target focus kind sort)
    (ContinuationSemantics.requestSyntax vertex (iface rely target focus kind sort)).projection
  rw [ContinuationSemantics.projection_read] at read
  change (model operational algebra vertex).evaluateSubstitution
    (Scope.resize (SingleRelyBeta.requestSize vertex rely target focus kind sort)
      (actual operational algebra vertex rely target focus kind sort))
    (params operational algebra vertex rely target focus kind sort)
    (fun position => SingleRelyBeta.normalizedProjection vertex rely target focus kind sort position) =
      some (requests operational algebra vertex rely target focus kind sort).project at read
  have mapping : (fun position => SingleRelyBeta.normalizedProjection vertex rely target focus kind sort position) =
      (fun position => (.var position.succ.succ : TermExpr (symbols D) 4)) :=
    funext (SingleRelyBeta.normalizedProjection_eq vertex rely target focus kind sort)
  rw [mapping] at read
  have changed := (model operational algebra vertex).evaluateSubstitution_source_eq
    (Scope.resize (SingleRelyBeta.requestSize vertex rely target focus kind sort)
      (actual operational algebra vertex rely target focus kind sort))
    (complete operational algebra vertex rely target focus kind sort A B)
    (params operational algebra vertex rely target focus kind sort) same
    (fun position => .var position.succ.succ)
    (requests operational algebra vertex rely target focus kind sort).project read
  have equality := Option.some.inj (changed.symm.trans
    (projectionMap operational algebra vertex rely target focus kind sort A B).evaluate)
  calc
    (requests operational algebra vertex rely target focus kind sort).project =
        (change operational algebra vertex rely target focus kind sort A B same).hom ≫
          (eqToHom (congrArg (fun scope : Scope W 4 => scope.1) same.symm) ≫
            (requests operational algebra vertex rely target focus kind sort).project) := by
      simp [change, ← Category.assoc]
    _ = _ := congrArg ((change operational algebra vertex rely target focus kind sort A B same).hom ≫ ·) equality

theorem project_point (world : Wᵒᵖ)
    (request : (actual operational algebra vertex rely target focus kind sort).1.obj world) :
    (requests operational algebra vertex rely target focus kind sort).project.app world request =
      (twoProjection operational algebra vertex rely target focus kind sort A B).app world
        ((change operational algebra vertex rely target focus kind sort A B same).hom.app world request) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (project_eq operational algebra vertex rely target focus kind sort A B same) world) request

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyRequestProjection
