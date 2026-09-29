import MettapediaFourColor.DiamondProfileCertificate
import MettapediaFourColor.DiamondBoundaryRepair
import MettapediaFourColor.KempeBoundarySplit
import FourColor.Bulk.Index

/-!
# Input coverage for the common diamond profile law

The six- and seven-port cores admit every proper zero-sum trace as an input.
The eight-port core uses the joint contraction relation, retaining both
insertions. All three inputs use the same profile descent theorem.
-/

namespace FourColor.DiamondProfileFamilyRepair

open Color DiamondProfile DiamondProfileCertificate KempeBoundarySplit

private theorem complete_dropLast {et : List Color} (hne : et ≠ []) (hs : et.sum = 0) :
    completeTrace et.dropLast = et := by
  have hlast := List.dropLast_append_getLast hne
  have hsum : et.dropLast.sum + et.getLast hne = 0 := by
    have hcat := congrArg List.sum hlast
    simpa using hcat.trans hs
  unfold completeTrace
  rw [Color.add_eq_zero_iff.mp hsum, hlast]

/-- The reference digit decoder is used only to enumerate possible inputs. -/
theorem repair_of_coverage (s : Shape) (m : ℕ)
    (hc : ∀ j : Fin (3 ^ m), (Bulk.partialOf m j.val).sum ≠ 0 →
      DiamondProfileCertificate.covered s (Bulk.traceOf m j.val) = true) :
    Repairs (Supports s) (m + 1) := by
  intro et hlen hzero hsum
  have hne : et ≠ [] := by intro h; simp [h] at hlen
  have htail : et.dropLast.length = m := by simp [hlen]
  have htailzero : (0 : Color) ∉ et.dropLast :=
    fun h => hzero (List.mem_of_mem_dropLast h)
  let j := Bulk.indexOf m et.dropLast
  have hj := Bulk.indexOf_lt m et.dropLast
  have hp : Bulk.partialOf m j = et.dropLast := Bulk.partialOf_indexOf htail htailzero
  have ht : Bulk.traceOf m j = et := by
    rw [Bulk.traceOf, hp]
    exact complete_dropLast hne hsum
  have hs : (Bulk.partialOf m j).sum ≠ 0 := by
    intro hz
    apply hzero
    rw [← ht, Bulk.traceOf, completeTrace, hz]
    simp
  rw [← ht]
  exact covered_repair s _ (hc ⟨j, hj⟩ hs)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Enumerate the finite proper trace inputs against the checked representatives.
theorem coverage0 : ∀ j : Fin (3 ^ 5), (Bulk.partialOf 5 j.val).sum ≠ 0 →
    DiamondProfileCertificate.covered 0 (Bulk.traceOf 5 j.val) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Enumerate the finite proper trace inputs against the checked representatives.
theorem coverage1 : ∀ j : Fin (3 ^ 6), (Bulk.partialOf 6 j.val).sum ≠ 0 →
    DiamondProfileCertificate.covered 1 (Bulk.traceOf 6 j.val) = true := by decide +kernel

theorem repair0 : Repairs (Supports 0) 6 := repair_of_coverage 0 5 coverage0
theorem repair1 : Repairs (Supports 1) 7 := repair_of_coverage 1 6 coverage1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Enumerate the finite proper trace inputs against the checked representatives.
theorem coverage2 :
    (DiamondBoundaryRepair.words DiamondBoundaryRepair.startCodes).all
      (DiamondProfileCertificate.covered 2) = true := by
  decide +kernel

/-- The coupled input remains relational; its two insertions are never separated. -/
theorem repair2 (a b x y z w : Color)
    (h : a ≠ b ∧ x ≠ a ∧ z ≠ b ∧ y ≠ a ∧ y ≠ b ∧ w ≠ a ∧ w ≠ b) :
    KempeCoclosure (Supports 2) (trace [a, x, a, y, b, z, b, w]) := by
  obtain ⟨g, hg⟩ := DiamondBoundaryRepair.normalize a b x y z w h
  exact kempeCoclosure_of_map g
    (covered_repair 2 _ ((List.all_eq_true.mp coverage2) _ hg))

end FourColor.DiamondProfileFamilyRepair
