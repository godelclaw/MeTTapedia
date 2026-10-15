import Mettapedia.OSLF.Framework.RhoGeneratedScopeStrata
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution
import Mettapedia.OSLF.Syntax.RhoScopeQuotientControls

/-!
# Actual quotient-scope derivation controls

The same admitted name has distinct atomic process origins, and a recursive
certificate of greater depth than its atomic certificate. Its least stratum
remains zero. An unseeded generator has an empty least fixed point even though
the actual name eta and unit equations give every name a coinductive witness.
These controls separate finite derivation, process-origin uniqueness and
greatest-fixed-point membership on the same source equation quotient.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoScopeQuotientControls
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoGeneratedScopeStrata

def outputCertificate : Certificate leftScope rightScope (quote visible) :=
  (congrArg quote (join_zero_left visible)) ▸
    Certificate.atoms (zero []) visible rfl (Or.inl rfl)

def suspendedCertificate : Certificate leftScope rightScope (quote visible) :=
  ((congrArg quote (join_zero_left suspended)).trans same_actual_name) ▸
    Certificate.atoms (zero []) suspended rfl (Or.inr rfl)

theorem distinct_atomic_certificate_origins : outputCertificate ≠ suspendedCertificate := by
  intro same
  have origins := congrArg Certificate.atomicOrigins same
  simp only [outputCertificate, suspendedCertificate, Certificate.atomicOrigins_cast,
    Certificate.atomicOrigins, List.cons.injEq, Sum.inr.injEq, true_and, and_true] at origins
  exact suspended_not_visible origins.symm

def recursiveCertificate : Certificate leftScope rightScope (quote visible) :=
  ((congrArg quote (join_zero_left (drop (quote visible)))).trans
    (quote_drop (quote visible))) ▸
    Certificate.right (left := leftScope) (right := rightScope)
      (zero []) rfl (quote visible) outputCertificate

theorem output_certificate_depth : outputCertificate.depth = 0 := by
  simp only [outputCertificate, depth_cast, Certificate.depth]

theorem suspended_certificate_depth : suspendedCertificate.depth = 0 := by
  simp only [suspendedCertificate, depth_cast, Certificate.depth]

theorem recursive_certificate_depth : recursiveCertificate.depth = 1 := by
  simp only [recursiveCertificate, depth_cast, Certificate.depth, output_certificate_depth]

theorem same_name_different_derivation_depth : outputCertificate.depth ≠ recursiveCertificate.depth := by
  rw [output_certificate_depth, recursive_certificate_depth]
  decide

theorem actual_least_stratum : stratum (certificate_sound outputCertificate) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [output_certificate_depth] using
    stratum_le_certificate (certificate_sound outputCertificate) outputCertificate

def unseededAtom : Process [] → Prop := fun _ => False

theorem unseeded_least_scope_empty (name : Name []) :
    ¬ generated unseededAtom leftScope name := by
  have empty : generated unseededAtom leftScope ≤ (⊥ : NamePredicate []) := by
    apply generated_induction
    intro result
    rintro ⟨first, second, readout, admitted, _⟩
    rcases admitted with impossible | ⟨_, impossible, _⟩
    · exact impossible
    · exact impossible
  exact empty name

theorem unseeded_greatest_scope_admits_every_name (name : Name []) :
    (step unseededAtom leftScope).gfp name := by
  have recursive : (⊤ : NamePredicate []) ≤ step unseededAtom leftScope ⊤ := by
    intro result _
    refine ⟨drop result, zero [], own_drop_beside_zero result, ?_, Or.inl rfl⟩
    exact Or.inr ⟨result, by constructor, rfl⟩
  exact (step unseededAtom leftScope).le_gfp recursive name (by constructor)

theorem coinductive_admission_does_not_supply_a_finite_certificate (name : Name []) :
    (step unseededAtom leftScope).gfp name ∧
      ¬ Nonempty (Certificate unseededAtom leftScope name) := by
  refine ⟨unseeded_greatest_scope_admits_every_name name, ?_⟩
  intro certificate
  exact unseeded_least_scope_empty name ((generated_iff_certificate _ _ name).mpr certificate)

end Mettapedia.OSLF.Framework.RhoGeneratedScopeControls
