import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordHeart
import Mettapedia.GraphTheory.FourColor.PentagonContextTensor

/-!
# The unique nonempty Kempe support disjoint from a pentagon

An admissible five-port word has colour multiplicities `3,1,1`. Modulo
global colour relabelling, the two singleton positions give ten orbits.
For each of the two pairs containing the repeated colour, the physical
noncrossing mate supplies one of two possible orbit transitions.

If a nonempty support satisfies these necessary transitions and avoids the
five pentagon-compatible orbits, it is exactly the other five orbits. The
proof follows a forced cycle through those five states; it does not
enumerate supports. The transition table is checked against literal Kempe
switches and the existing physical boundary-language interface.

The exceptional support satisfies the displayed transition condition.
Excluding its realization by a planar shore is a separate geometric problem.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport

open FiveCutWordHeart CyclicBoundaryMatching PentagonContextTensor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The existing lexicographic singleton-pair representatives, in `Color`. -/
def representative (i : Fin 10) : CAP5BoundaryWord := color ∘ orbitWord i

/-- Exactly the orbits whose singleton positions are cyclic neighbours. -/
def good : Finset (Fin 10) := {0, 3, 4, 7, 9}

/-- Exactly the orbits whose singleton positions are diagonals. -/
def bad : Finset (Fin 10) := {1, 2, 5, 6, 8}

theorem bad_iff_not_good (i : Fin 10) : i ∈ bad ↔ i ∉ good := by
  fin_cases i <;> decide

theorem bad_card : bad.card = 5 := by decide

/-- The majority colour is red; the other selected colour is blue or purple. -/
def other : Fin 2 → Color := ![blue, purple]

/-- Omit the singleton whose colour is not in the selected pair. -/
def activePorts (i : Fin 10) (p : Fin 2) : Fin 4 → Fin 5 :=
  (if p = 0 then (slots i).2.1 else (slots i).1).succAbove

def mateOption (i : Fin 10) (p : Fin 2) (nested : Bool) : Fin 5 → Fin 5 :=
  let a := activePorts i p
  if nested then pairingMate (a 0) (a 3) (a 1) (a 2)
  else pairingMate (a 0) (a 1) (a 2) (a 3)

/-- One whole component of the selected matching. -/
def component (i : Fin 10) (p : Fin 2) (nested : Bool) : Finset (Fin 5) :=
  {activePorts i p 0, activePorts i p (if nested then 3 else 1)}

/-- The two targets in the order of the separated and nested matchings. -/
def targetPair : Fin 10 → Fin 2 → Fin 10 × Fin 10 :=
  ![![(4, 6), (1, 3)], ![(4, 8), (0, 2)], ![(5, 9), (3, 1)],
    ![(6, 9), (2, 0)], ![(1, 7), (0, 5)], ![(2, 7), (6, 4)],
    ![(3, 8), (5, 0)], ![(9, 5), (8, 4)], ![(9, 6), (7, 1)],
    ![(8, 3), (7, 2)]]

def target (i : Fin 10) (p : Fin 2) (nested : Bool) : Fin 10 :=
  if nested then (targetPair i p).2 else (targetPair i p).1

/-- Necessary existential closure; it does not require both choices to work. -/
def Closed (S : Set (Fin 10)) : Prop :=
  ∀ i ∈ S, ∀ p : Fin 2, target i p false ∈ S ∨ target i p true ∈ S

def orbitSupport (L : CAP5BoundaryWord → Prop) : Set (Fin 10) :=
  {i | L (representative i)}

/-- The six global permutations of the nonzero colours, fixing zero. -/
def relabel : Fin 6 → Color ≃ Color :=
  ![σRBP, σRPB, σBRP, σPBR, σBPR, σPRB]

private theorem relabel_zero : ∀ r, relabel r 0 = 0 := by decide

private theorem other_valid : ∀ p, other p ≠ 0 ∧ red ≠ other p := by decide

private theorem component_closed : ∀ i p b, ∀ k ∈ component i p b,
    mateOption i p b k ∈ component i p b := by decide

/-- Every table entry is the orbit of an actual boundary component switch. -/
theorem target_realized : ∀ i p b, ∃ r : Fin 6,
    cap5MapBoundaryWord (relabel r)
      (cap5BoundarySwap red (other p) (component i p b) (representative i)) =
        representative (target i p b) := by decide +kernel

private theorem mate_options (i : Fin 10) (p : Fin 2) (mate : Fin 5 → Fin 5)
    (hinv : Function.Involutive mate)
    (hactive : ∀ k, mate k ≠ k ↔
      (representative i k = red ∨ representative i k = other p))
    (hnc : IsNoncrossingMatching mate) :
    mate = mateOption i p false ∨ mate = mateOption i p true := by
  fin_cases i <;> fin_cases p
  all_goals first
    | exact mate_dichotomy_0123 mate hinv
        (fun k => (hactive k).trans (by revert k; decide)) hnc
    | exact mate_dichotomy_0124 mate hinv
        (fun k => (hactive k).trans (by revert k; decide)) hnc
    | exact mate_dichotomy_0134 mate hinv
        (fun k => (hactive k).trans (by revert k; decide)) hnc
    | exact mate_dichotomy_0234 mate hinv
        (fun k => (hactive k).trans (by revert k; decide)) hnc
    | exact mate_dichotomy_1234 mate hinv
        (fun k => (hactive k).trans (by revert k; decide)) hnc

/-- Existing physical chain closure implies the finite orbit condition. -/
theorem orbitSupport_closed {L : CAP5BoundaryWord → Prop}
    (hL : BoundaryLanguage L) : Closed (orbitSupport L) := by
  intro i hi p
  obtain ⟨mate, hinv, hactive, hnc, hswitch⟩ :=
    hL.chainClosed _ hi red (other p) red_ne_zero
      (other_valid p).1 (other_valid p).2
  have along (b : Bool) (hm : mate = mateOption i p b) :
      target i p b ∈ orbitSupport L := by
    have hc := hswitch (component i p b) (by rw [hm]; exact component_closed i p b)
    obtain ⟨r, hr⟩ := target_realized i p b
    have h := hL.colourClosed (relabel r) (relabel_zero r) _ hc
    rwa [hr] at h
  rcases mate_options i p mate hinv hactive hnc with hm | hm
  · exact Or.inl (along false hm)
  · exact Or.inr (along true hm)

/-- The exceptional profile survives every separate colour-pair obligation. -/
theorem bad_closed : Closed (bad : Set (Fin 10)) := by
  unfold Closed
  decide +kernel

/-- Avoiding the good states forces the cycle `1 → 2 → 5 → 6 → 8 → 1`. -/
theorem eq_bad_of_nonempty_closed_disjoint {S : Set (Fin 10)}
    (hne : S.Nonempty) (hc : Closed S)
    (hdisj : ∀ i ∈ S, i ∉ good) : S = (bad : Set (Fin 10)) := by
  have h0 : (0 : Fin 10) ∉ S := fun h => hdisj 0 h (by decide)
  have h3 : (3 : Fin 10) ∉ S := fun h => hdisj 3 h (by decide)
  have h4 : (4 : Fin 10) ∉ S := fun h => hdisj 4 h (by decide)
  have h7 : (7 : Fin 10) ∉ S := fun h => hdisj 7 h (by decide)
  have h9 : (9 : Fin 10) ∉ S := fun h => hdisj 9 h (by decide)
  have h12 : (1 : Fin 10) ∈ S → 2 ∈ S :=
    fun h => (hc 1 h 1).resolve_left h0
  have h25 : (2 : Fin 10) ∈ S → 5 ∈ S :=
    fun h => (hc 2 h 0).resolve_right h9
  have h56 : (5 : Fin 10) ∈ S → 6 ∈ S :=
    fun h => (hc 5 h 1).resolve_right h4
  have h68 : (6 : Fin 10) ∈ S → 8 ∈ S :=
    fun h => (hc 6 h 0).resolve_left h3
  have h81 : (8 : Fin 10) ∈ S → 1 ∈ S :=
    fun h => (hc 8 h 1).resolve_left h7
  have h1 : (1 : Fin 10) ∈ S := by
    obtain ⟨i, hi⟩ := hne
    fin_cases i
    · exact (h0 hi).elim
    · exact hi
    · exact h81 (h68 (h56 (h25 hi)))
    · exact (h3 hi).elim
    · exact (h4 hi).elim
    · exact h81 (h68 (h56 hi))
    · exact h81 (h68 hi)
    · exact (h7 hi).elim
    · exact h81 hi
    · exact (h9 hi).elim
  have h2 := h12 h1
  have h5 := h25 h2
  have h6 := h56 h5
  have h8 := h68 h6
  ext i
  fin_cases i <;> simp_all [bad]

private instance : DecidablePred (Odd : Nat → Prop) := fun n =>
  decidable_of_iff (n % 2 = 1) Nat.odd_iff.symm

private instance (w : CAP5BoundaryWord) : Decidable (CAP5BoundaryWordIsNonzero w) := by
  unfold CAP5BoundaryWordIsNonzero; infer_instance

private instance (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordHasOddColorCounts w) := by
  unfold CAP5BoundaryWordHasOddColorCounts; infer_instance

private instance (w : CAP5BoundaryWord) (x : CAP5InternalCycleColoring) :
    Decidable (CAP5ExtendsAcrossCycleWith w x) := by
  unfold CAP5ExtendsAcrossCycleWith IsTaitColorTriple; infer_instance

private instance (w : CAP5BoundaryWord) : Decidable (CAP5WordExtendsAcrossCycle w) := by
  unfold CAP5WordExtendsAcrossCycle; infer_instance

/-- The good indices have their literal cap-extension meaning. -/
theorem representative_extends_iff : ∀ i,
    CAP5WordExtendsAcrossCycle (representative i) ↔ i ∈ good := by decide +kernel

/-- Every admissible word can be relabelled to one of the ten representatives. -/
theorem canonicalize : ∀ w : CAP5BoundaryWord,
    CAP5BoundaryWordIsNonzero w → CAP5BoundaryWordHasOddColorCounts w →
    ∃ i : Fin 10, ∃ r : Fin 6,
      cap5MapBoundaryWord (relabel r) w = representative i := by decide +kernel

theorem orbitSupport_nonempty {L : CAP5BoundaryWord → Prop}
    (hL : BoundaryLanguage L) (hne : ∃ w, L w) : (orbitSupport L).Nonempty := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨i, r, hr⟩ := canonicalize w (hL.admissible w hw).1 (hL.admissible w hw).2
  refine ⟨i, ?_⟩
  change L (representative i)
  exact hr ▸ hL.colourClosed (relabel r) (relabel_zero r) w hw

/-- Exact compatibility criterion for a nonempty physical boundary language.
The remaining obstruction is equality with one five-orbit profile. -/
theorem meets_pentagon_iff_ne_bad {L : CAP5BoundaryWord → Prop}
    (hL : BoundaryLanguage L) (hne : ∃ w, L w) :
    (∃ w, L w ∧ CAP5WordExtendsAcrossCycle w) ↔
      orbitSupport L ≠ (bad : Set (Fin 10)) := by
  constructor
  · rintro ⟨w, hw, hext⟩ heq
    obtain ⟨i, r, hr⟩ := canonicalize w (hL.admissible w hw).1 (hL.admissible w hw).2
    have hi : i ∈ orbitSupport L := by
      change L (representative i)
      exact hr ▸ hL.colourClosed (relabel r) (relabel_zero r) w hw
    have hg : i ∈ good := (representative_extends_iff i).mp
      (hr ▸ cap5WordExtendsAcrossCycle_map_equiv_of_map_zero (relabel_zero r) hext)
    rw [heq] at hi
    exact (bad_iff_not_good i).mp hi hg
  · intro hneBad
    by_contra hnone
    apply hneBad
    apply eq_bad_of_nonempty_closed_disjoint (orbitSupport_nonempty hL hne)
      (orbitSupport_closed hL)
    intro i hi hg
    exact hnone ⟨representative i, hi, (representative_extends_iff i).mpr hg⟩

/-- The admissible words rejected by the literal pentagon. -/
def Rejected (w : CAP5BoundaryWord) : Prop :=
  CAP5BoundaryWordIsNonzero w ∧ CAP5BoundaryWordHasOddColorCounts w ∧
    ¬ CAP5WordExtendsAcrossCycle w

instance (w : CAP5BoundaryWord) : Decidable (Rejected w) := by
  unfold Rejected; infer_instance

theorem rejected_card : (Finset.univ.filter Rejected).card = 30 := by decide +kernel

/-- The classification is an equality of literal word languages, not merely
an upper bound on their sizes. -/
theorem language_eq_rejected_of_avoids {L : CAP5BoundaryWord → Prop}
    (hL : BoundaryLanguage L) (hne : ∃ w, L w)
    (havoid : ∀ w, L w → ¬ CAP5WordExtendsAcrossCycle w) : L = Rejected := by
  have hs : orbitSupport L = (bad : Set (Fin 10)) :=
    eq_bad_of_nonempty_closed_disjoint (orbitSupport_nonempty hL hne)
      (orbitSupport_closed hL)
      (fun i hi hg => havoid _ hi ((representative_extends_iff i).mpr hg))
  funext w
  apply propext
  constructor
  · intro hw
    exact ⟨(hL.admissible w hw).1, (hL.admissible w hw).2, havoid w hw⟩
  · rintro ⟨hnz, hodd, hnot⟩
    obtain ⟨i, r, hr⟩ := canonicalize w hnz hodd
    have hi : i ∈ bad := (bad_iff_not_good i).mpr (by
      intro hg
      apply hnot
      apply (cap5WordExtendsAcrossCycle_map_equiv_iff_of_map_zero (relabel_zero r)).mp
      rw [hr]
      exact (representative_extends_iff i).mpr hg)
    have hmem : L (representative i) := by
      change i ∈ orbitSupport L
      rwa [hs]
    have hz : (relabel r).symm 0 = 0 := by
      apply (relabel r).injective
      simp [relabel_zero]
    have hback := hL.colourClosed (relabel r).symm hz _ hmem
    rw [← hr] at hback
    have hid : cap5MapBoundaryWord (relabel r).symm
        (cap5MapBoundaryWord (relabel r) w) = w := by
      funext k
      exact (relabel r).symm_apply_apply (w k)
    exact hid ▸ hback

end Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport
