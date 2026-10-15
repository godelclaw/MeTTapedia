import Mettapedia.CategoryTheory.ProgramReductionTheoryIsoClasses
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Program maps through an independent functor comparison

A natural isomorphism changes all context presentations of a closed
program map. Its program isomorphism and reduction map are transported
together. Naturality earns both endpoint squares, and the resulting
compatible comparison retains the complete event map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.ProgramReductionTheory.Map

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory

universe k
variable {source target : Theory.{k,k}}
variable (mapping : Map source target) {next : source.closed.Obj ⥤ target.closed.Obj}
variable (comparison : mapping.closed.functor ≅ next)

def ofFunctorIso : Map source target := by
  let : PreservesFiniteLimits mapping.closed.functor := mapping.closed.preservesFiniteLimits
  let : PreservesFiniteLimits next := preservesFiniteLimits_of_natIso comparison
  let : MonoidalClosedFunctor mapping.closed.functor := mapping.closed.preservesExponentials
  exact {
    closed := {
      functor := next
      preservesFiniteLimits := inferInstance
      preservesExponentials := CartesianClosedFunctorCoherence.closed_of_naturalIso comparison.symm }
    program := (comparison.app source.program).symm ≪≫ mapping.program
    reduction := comparison.inv.app source.Event ≫ mapping.reduction
    source := by
      change (comparison.inv.app source.Event ≫ mapping.reduction) ≫ target.source =
        next.map source.source ≫ (comparison.inv.app source.program ≫ mapping.program.hom)
      rw [Category.assoc, mapping.source, ← Category.assoc,
        ← comparison.inv.naturality source.source, Category.assoc]
    target := by
      change (comparison.inv.app source.Event ≫ mapping.reduction) ≫ target.target =
        next.map source.target ≫ (comparison.inv.app source.program ≫ mapping.program.hom)
      rw [Category.assoc, mapping.target, ← Category.assoc,
        ← comparison.inv.naturality source.target, Category.assoc] }

def compatibleComparison : ProgramReductionTheoryIsoClasses.MapIso mapping (ofFunctorIso mapping comparison) where
  comparison := comparison
  program := by
    change comparison.hom.app source.program ≫
      (comparison.inv.app source.program ≫ mapping.program.hom) = _
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

theorem entire_event_square :
    comparison.hom.app source.Event ≫ (ofFunctorIso mapping comparison).reduction = mapping.reduction :=
  (compatibleComparison mapping comparison).reduction_square

end Mettapedia.GSLT.Core.ProgramReductionTheory.Map
