import Mettapedia.PLN.WorldModel.EvidenceContracts
import Mettapedia.GSLT.Logic.KripkeFixedPoint

/-!
# The four-valued support of evidence counts

`EvidenceContracts.belnap` reads evidence counts `(n⁺, n⁻)` as one of Belnap's
four values: is there evidence for, and is there evidence against. This module
computes what each operation on counts does to that reading, and how strong
Kleene statuses (the statuses of `Mettapedia.GSLT.KripkeTruth`) enter evidence.

## Operations on counts, read in four values

* Revision (`+`) is the information join (`belnap_add`).
* Fusion of likelihood reports (`EvidenceContracts.fuse`, the coordinatewise
  product) is the information meet, the consensus of two sources
  (`belnap_fuse`): a report for and a report against fuse to no evidence.
* The truth-order meet and join of the evidence bilattice (`tmeet`, `tjoin`)
  are the truth-order meet and join of the four values (`belnap_tmeet`,
  `belnap_tjoin`), and evidential negation exchanges the two readings
  (`belnap_against`).
* The paired-sample product (`*`, conjunction over two independent sample bags)
  is the weak conjunction of Bochvar: the value with no evidence absorbs
  (`belnap_mul`). It agrees with the truth-order meet exactly unless one side
  has no evidence and the other has evidence against
  (`belnap_mul_eq_belnap_tmeet_iff`).

## Strong Kleene statuses as evidence

A status `none`, `some true`, `some false` enters as no sample, one positive
sample or one negative sample (`ofStatus`, injective). Strong Kleene negation,
conjunction and disjunction become `against`, `tmeet` and `tjoin`
(`ofStatus_kleeneNot`, `ofStatus_kleeneAnd`, `ofStatus_kleeneOr`). Conjunction
does not become the paired product: undetermined and refuted is refuted for
strong Kleene and no evidence for the product (`Controls.kleeneAnd_not_paired`).
Revising a verified and a refuted status gives evidence both ways, a value that
no status has (`Controls.revision_leaves_statuses`).

## Readout under negation

The three-valued readout commutes with negation: `readout (against e)` is
`1 - readout e`, and both are undetermined at zero (`readout_against`). A total
readout that commutes with negation must answer `1/2` with no evidence
(`total_readout_at_zero`), so a total readout cannot tell no evidence from
balanced evidence, and the total `strength`, which answers `0` with no evidence,
does not commute with negation there (`Controls.strength_not_against_at_zero`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.EvidenceSupportBilattice

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence
open Mettapedia.PLN.WorldModel.EvidenceContracts

/-! ## The four values and their operations

A value is a pair (evidence for, evidence against). -/

/-- Information join: what either source was told. -/
def infoJoin (a b : Bool × Bool) : Bool × Bool := (a.1 || b.1, a.2 || b.2)

/-- Information meet: what both sources were told. -/
def infoMeet (a b : Bool × Bool) : Bool × Bool := (a.1 && b.1, a.2 && b.2)

/-- Truth-order meet: true when both are, false when either is. -/
def truthMeet (a b : Bool × Bool) : Bool × Bool := (a.1 && b.1, a.2 || b.2)

/-- Truth-order join: true when either is, false when both are. -/
def truthJoin (a b : Bool × Bool) : Bool × Bool := (a.1 || b.1, a.2 && b.2)

/-- Weak (Bochvar) conjunction: the value with no evidence absorbs; otherwise
the truth-order meet. -/
def weakMeet (a b : Bool × Bool) : Bool × Bool :=
  if a = (false, false) ∨ b = (false, false) then (false, false) else truthMeet a b

/-! ## Operations on counts, read in four values -/

private theorem decide_add_ne_zero (m n : ℕ) :
    decide (m + n ≠ 0) = (decide (m ≠ 0) || decide (n ≠ 0)) := by
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]

/-- **Revision is the information join.** -/
theorem belnap_add (a b : Evidence ℕ) : belnap (a + b) = infoJoin (belnap a) (belnap b) := by
  simp only [belnap, infoJoin, Evidence.add_pos, Evidence.add_neg, decide_add_ne_zero]

/-- **Fusion of reports is the information meet**: the consensus of two
sources. -/
theorem belnap_fuse (a b : Evidence ℕ) : belnap (fuse a b) = infoMeet (belnap a) (belnap b) := by
  obtain ⟨p, n⟩ := a
  obtain ⟨q, m⟩ := b
  simp only [belnap, infoMeet, fuse]
  by_cases hp : p = 0 <;> by_cases hn : n = 0 <;> by_cases hq : q = 0 <;> by_cases hm : m = 0 <;>
    simp [hp, hn, hq, hm]

/-- **The truth-order meet of counts is the truth-order meet of values.** -/
theorem belnap_tmeet (a b : Evidence ℕ) :
    belnap (tmeet a b) = truthMeet (belnap a) (belnap b) := by
  obtain ⟨p, n⟩ := a
  obtain ⟨q, m⟩ := b
  simp only [belnap, truthMeet, tmeet]
  by_cases hp : p = 0 <;> by_cases hn : n = 0 <;> by_cases hq : q = 0 <;> by_cases hm : m = 0 <;>
    simp [hp, hn, hq, hm]

/-- **The truth-order join of counts is the truth-order join of values.** -/
theorem belnap_tjoin (a b : Evidence ℕ) :
    belnap (tjoin a b) = truthJoin (belnap a) (belnap b) := by
  obtain ⟨p, n⟩ := a
  obtain ⟨q, m⟩ := b
  simp only [belnap, truthJoin, tjoin]
  by_cases hp : p = 0 <;> by_cases hn : n = 0 <;> by_cases hq : q = 0 <;> by_cases hm : m = 0 <;>
    simp [hp, hn, hq, hm]

/-- **Evidential negation exchanges the two readings.** -/
theorem belnap_against (a : Evidence ℕ) : belnap (against a) = (belnap a).swap := rfl

/-- **The paired-sample product is the weak (Bochvar) conjunction** of the four
values: no evidence on either side gives no evidence. -/
theorem belnap_mul (a b : Evidence ℕ) : belnap (a * b) = weakMeet (belnap a) (belnap b) := by
  obtain ⟨p, n⟩ := a
  obtain ⟨q, m⟩ := b
  simp only [belnap, weakMeet, truthMeet, Evidence.mul_pos, Evidence.mul_neg]
  by_cases hp : p = 0 <;> by_cases hn : n = 0 <;> by_cases hq : q = 0 <;> by_cases hm : m = 0 <;>
    simp [hp, hn, hq, hm]

/-- **Where the paired product and the truth-order meet part**: exactly where
one side has no evidence and the other has evidence against. -/
theorem belnap_mul_eq_belnap_tmeet_iff (a b : Evidence ℕ) :
    belnap (a * b) = belnap (tmeet a b) ↔ ¬ (a = 0 ∧ b.neg ≠ 0) ∧ ¬ (b = 0 ∧ a.neg ≠ 0) := by
  obtain ⟨p, n⟩ := a
  obtain ⟨q, m⟩ := b
  have zero_iff : ∀ x y : ℕ, (⟨x, y⟩ : Evidence ℕ) = 0 ↔ x = 0 ∧ y = 0 := by
    intro x y
    constructor
    · intro h
      exact ⟨congrArg Evidence.pos h, congrArg Evidence.neg h⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  rw [belnap_mul, belnap_tmeet, zero_iff, zero_iff]
  simp only [belnap, weakMeet, truthMeet]
  by_cases hp : p = 0 <;> by_cases hn : n = 0 <;> by_cases hq : q = 0 <;> by_cases hm : m = 0 <;>
    simp [hp, hn, hq, hm]

/-! ## Strong Kleene statuses as evidence -/

open Mettapedia.GSLT.KripkeTruth (kleeneNot)

/-- Strong Kleene conjunction of statuses. -/
def kleeneAnd : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- Strong Kleene disjunction of statuses. -/
def kleeneOr : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- A status as evidence: undetermined is no sample, verified one positive
sample, refuted one negative sample. -/
def ofStatus : Option Bool → Evidence ℕ
  | none => 0
  | some true => positive
  | some false => negative

theorem ofStatus_injective : Function.Injective ofStatus := by
  intro s t h
  have hp := congrArg Evidence.pos h
  have hn := congrArg Evidence.neg h
  rcases s with _ | _ | _ <;> rcases t with _ | _ | _ <;>
    simp_all [ofStatus, positive, negative, Evidence.ext_iff]

/-- The four-valued reading of a status is its Kleene value in Belnap's square:
undetermined has no evidence either way. -/
theorem belnap_ofStatus (s : Option Bool) :
    belnap (ofStatus s) = (decide (s = some true), decide (s = some false)) := by
  rcases s with _ | _ | _ <;> simp [ofStatus, belnap, positive, negative]

/-- **Strong Kleene negation is evidential negation.** -/
theorem ofStatus_kleeneNot (s : Option Bool) : ofStatus (kleeneNot s) = against (ofStatus s) := by
  rcases s with _ | _ | _ <;> rfl

/-- **Strong Kleene conjunction is the truth-order meet.** -/
theorem ofStatus_kleeneAnd (s t : Option Bool) :
    ofStatus (kleeneAnd s t) = tmeet (ofStatus s) (ofStatus t) := by
  rcases s with _ | _ | _ <;> rcases t with _ | _ | _ <;> rfl

/-- **Strong Kleene disjunction is the truth-order join.** -/
theorem ofStatus_kleeneOr (s t : Option Bool) :
    ofStatus (kleeneOr s t) = tjoin (ofStatus s) (ofStatus t) := by
  rcases s with _ | _ | _ <;> rcases t with _ | _ | _ <;> rfl

/-! ## Readout under negation -/

section Readout

variable {R : Type*} [Field R] [DecidableEq R]

/-- **The three-valued readout commutes with negation**: the evidence against
reads as one minus the evidence for, and both are undetermined at zero. -/
theorem readout_against (e : Evidence R) : readout (against e) = (readout e).map (1 - ·) := by
  have total_against : (against e).total = e.total := by
    simp [total, against, add_comm]
  by_cases zero : e.total = 0
  · simp [readout, total_against, zero]
  · simp only [readout, total_against, zero, if_false, Option.map_some, Option.some.injEq]
    rw [strength, strength, total_against]
    field_simp
    simp [total, against]

omit [DecidableEq R] in
/-- **A total readout that commutes with negation answers `1/2` with no
evidence**, the answer it must also give to balanced evidence. -/
theorem total_readout_at_zero [CharZero R] (r : Evidence R → R)
    (commutes : ∀ e, r (against e) = 1 - r e) : r 0 = 1 / 2 := by
  have fixed : against (0 : Evidence R) = 0 := by
    ext <;> rfl
  have := commutes 0
  rw [fixed] at this
  rw [eq_div_iff two_ne_zero]
  linear_combination this

end Readout

namespace Controls

/-- **Positive: the two conjunctions agree away from the boundary.** Evidence
`(2, 1)` and `(3, 0)` read the same under the paired product and the meet. -/
theorem mul_agrees_with_tmeet :
    belnap ((⟨2, 1⟩ : Evidence ℕ) * ⟨3, 0⟩) = belnap (tmeet ⟨2, 1⟩ ⟨3, 0⟩) := by
  decide

/-- **Negative: undetermined and refuted.** Strong Kleene answers refuted; the
paired product of their evidence has no evidence, which reads out undetermined;
the truth-order meet gives the refuting sample. -/
theorem kleeneAnd_not_paired :
    kleeneAnd none (some false) = some false ∧
      ofStatus none * ofStatus (some false) = 0 ∧
      tmeet (ofStatus none) (ofStatus (some false)) = negative ∧
      readout (Evidence.map (Nat.castRingHom ℚ) (ofStatus none * ofStatus (some false))) = none := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · ext <;> rfl
  · have zero : ofStatus none * ofStatus (some false) = 0 := by ext <;> rfl
    rw [zero, map_zero]
    exact readout_zero

/-- **Revision leaves the statuses**: revising a verified and a refuted status
gives evidence for and against, the glut, which is the image of no status. -/
theorem revision_leaves_statuses :
    belnap (ofStatus (some true) + ofStatus (some false)) = (true, true) ∧
      ∀ s, belnap (ofStatus s) ≠ (true, true) := by
  refine ⟨by decide, fun s => ?_⟩
  rw [belnap_ofStatus]
  rcases s with _ | _ | _ <;> decide

/-- **Fusion of opposite reports is no evidence**: consensus of a source told
true and a source told false. -/
theorem fuse_opposite_reports :
    belnap (fuse (ofStatus (some true)) (ofStatus (some false))) = (false, false) := by
  decide

/-- **The total strength, which answers `0` with no evidence, does not commute
with negation there.** -/
theorem strength_not_against_at_zero :
    strength (against (0 : Evidence ℚ)) ≠ 1 - strength (0 : Evidence ℚ) := by
  norm_num [strength, total, against]

end Controls

end Mettapedia.PLN.WorldModel.EvidenceSupportBilattice
