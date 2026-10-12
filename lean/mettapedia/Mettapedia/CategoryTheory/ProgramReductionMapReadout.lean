import Mettapedia.CategoryTheory.ProgramReductionFunctorComparison

/-!
# Complete program and event readouts of compatible map comparisons

Each readout transports the complete supplied section through the actual
context comparison. Naturality and the program square determine program
readouts; the earned event square determines event readouts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.ProgramReductionTheoryIsoClasses.MapIso

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ProgramReductionTheory

universe k
variable {source target : Theory.{k,k}} {first second : Map source target}
variable (comparison : MapIso first second)

theorem complete_program_readout {context : source.closed.Obj} (term : context ⟶ source.program) :
    comparison.comparison.inv.app context ≫ first.closed.functor.map term ≫ first.program.hom =
      second.closed.functor.map term ≫ second.program.hom := by
  rw [← comparison.program, ← Category.assoc, ← Category.assoc,
    ← comparison.comparison.inv.naturality term, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc]

theorem complete_event_readout {context : source.closed.Obj} (event : context ⟶ source.Event) :
    comparison.comparison.inv.app context ≫ first.closed.functor.map event ≫ first.reduction =
      second.closed.functor.map event ≫ second.reduction := by
  rw [← comparison.reduction_square, ← Category.assoc, ← Category.assoc,
    ← comparison.comparison.inv.naturality event, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc]

end Mettapedia.CategoryTheory.ProgramReductionTheoryIsoClasses.MapIso
