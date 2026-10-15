import Mettapedia.OSLF.Framework.RhoScopeFiniteStep
import Mettapedia.OSLF.Framework.RhoGeneratedScopeStrata

/-!
# Actual bounded scope membership for arbitrary decidable atoms

The complete finite decomposition catalogue earns the finite-depth decision
for the manuscript's actual atomic-part generator. Depth is the maximum depth
of its retained scope derivation, including circular equation-class splits.
This measures generation, not runtime work, observer depth or purse funding.
Positive unbounded membership has a finite successful bound; a terminating
unbounded rejection still needs the additional finite-dependency argument.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeBoundedDecision

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoEquationGeneratedScope RhoGeneratedScopeStrata RhoScopeFiniteStep

theorem bounded_succ_iff {context : Ctx sig} (left right : Process context → Prop)
    (limit : Nat) (name : Name context) :
    Bounded left right (limit + 1) name ↔ step left right (Bounded left right limit) name := by
  constructor
  · rintro ⟨certificate, bound⟩
    cases certificate with
    | atoms first second firstAtom secondAtom =>
      exact ⟨first, second, rfl, Or.inl firstAtom, Or.inl secondAtom⟩
    | left child childCertificate second secondAtom =>
      have small : childCertificate.depth ≤ limit := by
        simpa only [Certificate.depth, Nat.add_le_add_iff_right] using bound
      exact ⟨drop child, second, rfl, Or.inr ⟨child, ⟨childCertificate, small⟩, rfl⟩,
        Or.inl secondAtom⟩
    | right first firstAtom child childCertificate =>
      have small : childCertificate.depth ≤ limit := by
        simpa only [Certificate.depth, Nat.add_le_add_iff_right] using bound
      exact ⟨first, drop child, rfl, Or.inl firstAtom,
        Or.inr ⟨child, ⟨childCertificate, small⟩, rfl⟩⟩
    | both first second firstCertificate secondCertificate =>
      have small : max firstCertificate.depth secondCertificate.depth ≤ limit := by
        simpa only [Certificate.depth, Nat.add_le_add_iff_right] using bound
      exact ⟨drop first, drop second, rfl,
        Or.inr ⟨first, ⟨firstCertificate, (le_max_left _ _).trans small⟩, rfl⟩,
        Or.inr ⟨second, ⟨secondCertificate, (le_max_right _ _).trans small⟩, rfl⟩⟩
  · rintro ⟨first, second, readout, (firstAtom | ⟨firstName, firstMember, rfl⟩),
      (secondAtom | ⟨secondName, secondMember, rfl⟩)⟩
    · exact readout ▸ ⟨Certificate.atoms first second firstAtom secondAtom, Nat.zero_le _⟩
    · obtain ⟨certificate, small⟩ := secondMember
      exact readout ▸ ⟨Certificate.right first firstAtom secondName certificate,
        Nat.add_le_add_right small 1⟩
    · obtain ⟨certificate, small⟩ := firstMember
      exact readout ▸ ⟨Certificate.left firstName certificate second secondAtom,
        Nat.add_le_add_right small 1⟩
    · obtain ⟨firstCertificate, firstSmall⟩ := firstMember
      obtain ⟨secondCertificate, secondSmall⟩ := secondMember
      exact readout ▸ ⟨Certificate.both firstName secondName firstCertificate secondCertificate,
        Nat.add_le_add_right (max_le firstSmall secondSmall) 1⟩

theorem bounded_zero_iff_step_bottom {context : Ctx sig} (left right : Process context → Prop)
    (name : Name context) :
    Bounded left right 0 name ↔ step left right (fun _ => False) name := by
  rw [bounded_zero_iff_atoms]
  constructor
  · rintro ⟨first, second, firstAtom, secondAtom, readout⟩
    exact ⟨first, second, readout, Or.inl firstAtom, Or.inl secondAtom⟩
  · rintro ⟨first, second, readout, (firstAtom | impossible), (secondAtom | impossible)⟩
    · exact ⟨first, second, firstAtom, secondAtom, readout⟩
    all_goals obtain ⟨_, excluded, _⟩ := impossible; exact excluded.elim

def boundedDecision {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] :
    (limit : Nat) → (name : Name context) → Decidable (Bounded left right limit name)
  | 0, name => by
      letI := stepDecision left right (fun _ => False) name
      exact decidable_of_iff' _ (bounded_zero_iff_step_bottom left right name)
  | limit + 1, name => by
      letI : DecidablePred (Bounded left right limit) := boundedDecision left right limit
      letI := stepDecision left right (Bounded left right limit) name
      exact decidable_of_iff' _ (bounded_succ_iff left right limit name)

def boundedTest {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (limit : Nat) (name : Name context) : Bool :=
  @decide (Bounded left right limit name) (boundedDecision left right limit name)

theorem boundedTest_true_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (limit : Nat) (name : Name context) :
    boundedTest left right limit name = true ↔ Bounded left right limit name :=
  Iff.of_eq (@decide_eq_true_eq _ (boundedDecision left right limit name))

theorem boundedTest_false_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (limit : Nat) (name : Name context) :
    boundedTest left right limit name = false ↔ ¬ Bounded left right limit name :=
  @decide_eq_false_iff_not _ (boundedDecision left right limit name)

theorem generated_iff_successful_bound {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (name : Name context) :
    generated left right name ↔ ∃ limit, boundedTest left right limit name = true := by
  rw [generated_iff_bounded]
  exact exists_congr fun limit => (boundedTest_true_iff left right limit name).symm

end Mettapedia.OSLF.Framework.RhoScopeBoundedDecision
