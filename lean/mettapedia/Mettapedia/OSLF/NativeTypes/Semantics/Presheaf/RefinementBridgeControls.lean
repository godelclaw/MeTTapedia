import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.RefinementBridge
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementNativeDeclarationModels
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Native evaluator controls for the generated intuitionistic fragment

An existing independently specified dependent scalar model supplies the atomic
code and meaning. The embedded code runs through the shared native evaluator,
retaining its scalar parameter; zero and a positive parameter are separated.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.RefinementBridgeControls

open _root_.CategoryTheory Logic RefinementBridge
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeDeclarationModels

abbrev World := Discrete PUnit.{1}
abbrev spot : Worldᵒᵖ := Opposite.op (Discrete.mk PUnit.unit)

def nativeAtoms : Unit → PropExpr Controls.symbols 1 := fun _ => Controls.positive 0
def nativeMeanings : Unit → Subfunctor (scalarScope (C := World)).1 := fun _ => positivity

theorem atom_readout (name : Unit) :
    (model (C := World)).evaluatePredicate scalarScope (nativeAtoms name) =
      some (nativeMeanings name) := positive_scalar_read

theorem actual_native_evaluator :
    (model (C := World)).evaluatePredicate scalarScope
      (embed nativeAtoms (.conj (.atom ()) .top)) =
        some (denote nativeMeanings (.conj (.atom ()) .top)) :=
  evaluate_embed model scalarScope nativeAtoms nativeMeanings atom_readout _

theorem evaluated_positive_parameter :
    (⟨PUnit.unit, (1 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) ∈
      (denote nativeMeanings (.conj (.atom ()) .top)).obj spot := by
  exact ⟨Nat.zero_lt_succ 0, trivial⟩

theorem evaluated_zero_parameter_rejected :
    (⟨PUnit.unit, (0 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) ∉
      (denote nativeMeanings (.conj (.atom ()) .top)).obj spot := by
  intro alleged
  exact Nat.not_lt_zero 0 alleged.1

theorem native_negation_positive_rejected :
    ¬ Satisfaction nativeMeanings (Formula.atom ()).negation spot
      (⟨PUnit.unit, (1 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) := by
  intro alleged
  apply alleged spot (𝟙 spot)
  change 0 < (1 : Nat)
  exact Nat.zero_lt_succ 0

theorem dependent_parameter_kept :
    (⟨PUnit.unit, (0 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) ≠
      (⟨PUnit.unit, (1 : Nat)⟩ : (scalarScope (C := World)).1.obj spot) := by
  intro equal
  have impossible : (0 : Nat) = 1 := congrArg
    (fun value : (scalarScope (C := World)).1.obj spot => (show Nat from value.2)) equal
  exact Nat.zero_ne_one impossible

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.RefinementBridgeControls
