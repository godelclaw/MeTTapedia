import Mettapedia.OSLF.Framework.RhoEquationGeneratedScope
import Mathlib.Data.Nat.Find

/-!
# Strata determined by actual scope derivations

The stratum of a generated name is the least depth among its finite
certificates. This measures the admitted derivations rather than a chosen
parse tree. Membership is the union of the bounded derivation stages; each
minimum is attained, and every certificate bounds it from above.

These bounded stages are semantic predicates. An executable enumeration or
decision procedure additionally needs complete, finite presentations of the
relevant equation-class decompositions and atomic tests.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeStrata

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoEquationGeneratedScope

variable {context : Ctx sig} {left right : Process context → Prop}

def Bounded (left right : Process context → Prop) (bound : Nat) (name : Name context) : Prop :=
  ∃ certificate : Certificate left right name, certificate.depth ≤ bound

theorem bounded_mono {first second : Nat} (inclusion : first ≤ second)
    {name : Name context} : Bounded left right first name → Bounded left right second name := by
  rintro ⟨certificate, small⟩
  exact ⟨certificate, small.trans inclusion⟩

theorem generated_iff_bounded (name : Name context) :
    generated left right name ↔ ∃ bound, Bounded left right bound name := by
  constructor
  · intro member
    obtain ⟨certificate⟩ := (generated_iff_certificate _ _ name).mp member
    exact ⟨certificate.depth, certificate, Nat.le_refl _⟩
  · rintro ⟨_, certificate, _⟩
    exact certificate_sound certificate

noncomputable def stratum {name : Name context} (member : generated left right name) : Nat := by
  classical
  exact Nat.find ((generated_iff_bounded name).mp member)

theorem stratum_attained {name : Name context} (member : generated left right name) :
    Bounded left right (stratum member) name := by
  classical
  exact Nat.find_spec ((generated_iff_bounded name).mp member)

theorem stratum_le {name : Name context} (member : generated left right name)
    {bound : Nat} (bounded : Bounded left right bound name) : stratum member ≤ bound := by
  classical
  exact Nat.find_min' ((generated_iff_bounded name).mp member) bounded

theorem stratum_le_certificate {name : Name context} (member : generated left right name)
    (certificate : Certificate left right name) : stratum member ≤ certificate.depth :=
  stratum_le member ⟨certificate, Nat.le_refl _⟩

theorem least_certificate_depth {name : Name context} (member : generated left right name) :
    ∃ certificate : Certificate left right name, certificate.depth = stratum member := by
  obtain ⟨certificate, bounded⟩ := stratum_attained member
  exact ⟨certificate, Nat.le_antisymm bounded (stratum_le_certificate member certificate)⟩

theorem below_stratum_has_no_certificate {name : Name context}
    (member : generated left right name) {bound : Nat} (small : bound < stratum member) :
    ¬ Bounded left right bound name :=
  fun bounded => (Nat.not_lt_of_ge (stratum_le member bounded)) small

theorem bounded_zero_iff_atoms (name : Name context) :
    Bounded left right 0 name ↔
      ∃ first second, left first ∧ right second ∧ quote (join first second) = name := by
  constructor
  · rintro ⟨certificate, small⟩
    cases certificate with
    | atoms first second firstAdmitted secondAdmitted =>
        exact ⟨first, second, firstAdmitted, secondAdmitted, rfl⟩
    | left => simp only [Certificate.depth] at small; omega
    | right => simp only [Certificate.depth] at small; omega
    | both => simp only [Certificate.depth] at small; omega
  · rintro ⟨first, second, firstAdmitted, secondAdmitted, rfl⟩
    exact ⟨.atoms first second firstAdmitted secondAdmitted, Nat.le_refl 0⟩

theorem stratum_zero_iff_atoms {name : Name context} (member : generated left right name) :
    stratum member = 0 ↔
      ∃ first second, left first ∧ right second ∧ quote (join first second) = name := by
  constructor
  · intro zero
    apply (bounded_zero_iff_atoms name).mp
    simpa only [zero] using stratum_attained member
  · intro atoms
    exact Nat.eq_zero_of_le_zero (stratum_le member ((bounded_zero_iff_atoms name).mpr atoms))

end Mettapedia.OSLF.Framework.RhoGeneratedScopeStrata
