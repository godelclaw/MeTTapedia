import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Monotone
import Mettapedia.GSLT.Topos.NativeFixedPointEncodingsControls

/-!
# Syntactic variance admission and fixed-point controls

Single negative occurrences are refused, double negative occurrences are
admitted, and a seed-or-variable body computes a proper native predicate.
The checker drives the actual operator used by the fixed-point construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.MonotoneControls

open _root_.CategoryTheory Logic Mettapedia.GSLT.Topos
open _root_.Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Monotone
open NativeFixedPointEncodings NativeFixedPointEncodingsControls

def boundVariable : Formula (Sum Unit Unit) := .atom (.inr ())

def seedBody : Formula (Sum Unit Unit) := .disj (.atom (.inl ())) boundVariable

def doubleNegative : Formula (Sum Unit Unit) := boundVariable.negation.negation

theorem seed_checked : variance true seedBody = true := rfl

theorem single_negative_refused : variance true boundVariable.negation = false := rfl

theorem double_negative_checked : variance true doubleNegative = true := rfl

theorem single_negative_not_installed :
    install (fun _ : Unit => trueOnly) boundVariable.negation = none :=
  (install_none_iff _ _).mpr single_negative_refused

theorem seeded_operator_exact : operator (fun _ : Unit => trueOnly) seedBody seed_checked = seeded := by
  ext candidate world value
  rfl

theorem seeded_inductive_exact :
    inductiveMeaning (fun _ : Unit => trueOnly) seedBody seed_checked = trueOnly := by
  unfold inductiveMeaning
  rw [seeded_operator_exact]
  exact corrected_mu_inhabits_exact_seed

theorem seeded_coinductive_exact :
    coinductiveMeaning (fun _ : Unit => trueOnly) seedBody seed_checked = ⊤ := by
  unfold coinductiveMeaning
  rw [seeded_operator_exact]
  exact corrected_nu_full

theorem generated_seed_positive :
    true ∈ (inductiveMeaning (fun _ : Unit => trueOnly) seedBody seed_checked).obj spot := by
  rw [seeded_inductive_exact]
  rfl

theorem generated_seed_negative :
    false ∉ (inductiveMeaning (fun _ : Unit => trueOnly) seedBody seed_checked).obj spot := by
  rw [seeded_inductive_exact]
  exact Bool.false_ne_true

theorem generated_nonidentity_substitution :
    (inductiveMeaning (fun _ : Unit => trueOnly) seedBody seed_checked).preimage constantTrue =
      inductiveMeaning (fun _ : Unit => trueOnly.preimage constantTrue) seedBody seed_checked :=
  inductive_substitution _ _ _ _

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.MonotoneControls
