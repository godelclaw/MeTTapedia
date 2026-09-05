import Mettapedia.GraphTheory.FourColor.NoncrossingEnum

/-!
# The enumerated step condition

A certificate node supplies one switch set per listed noncrossing matching of
its active ports; the enumerated step condition checks each listed matching
only.  By completeness of the enumeration it implies the step condition over
all port maps (`stepOk_of_stepOkEnum`), so `Derivable.of_known` applies with
the cost of the listed matchings rather than of all `n^n` maps.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation

open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open GoertzelV24HexagonPairingTargetAwareBoundary

variable {n : Nat}

/-- the active ports, in increasing order -/
def activeList (w : Word n) (pair : TaitColorPair) : List (Fin n) :=
  (List.finRange n).filter fun i => decide (activeAt w pair i)

theorem mem_activeList {w : Word n} {pair : TaitColorPair} {i : Fin n} :
    i ∈ activeList w pair ↔ activeAt w pair i := by
  simp [activeList, List.mem_filter]

theorem activeList_pairwise (w : Word n) (pair : TaitColorPair) :
    (activeList w pair).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).sublist List.filter_sublist

theorem activeList_length_le (w : Word n) (pair : TaitColorPair) :
    (activeList w pair).length ≤ n := by
  unfold activeList
  exact (List.length_filter_le _ _).trans (by simp)

/-- the listed matchings of a node -/
def nodeMatchings (w : Word n) (pair : TaitColorPair) : List (List (Fin n × Fin n)) :=
  enumPairs n (activeList w pair)

/-- **the enumerated step condition**: one switch set per listed matching -/
def StepOkEnum (w : Word n) (pair : TaitColorPair) (known : Finset (Word n))
    (sel : Nat → Finset (Fin n)) : Prop :=
  ∀ k (h : k < (nodeMatchings w pair).length),
    IsComponentUnion (mateOf (nodeMatchings w pair)[k]) (sel k) ∧
      switchBoundaryWord w pair (sel k) ∈ known

instance (w : Word n) (pair : TaitColorPair) (known : Finset (Word n)) (sel : Nat → Finset (Fin n)) :
    Decidable (StepOkEnum w pair known sel) := by
  unfold StepOkEnum; infer_instance

/-- **soundness of the enumerated check** -/
theorem stepOk_of_stepOkEnum {w : Word n} {pair : TaitColorPair} {known : Finset (Word n)}
    {sel : Nat → Finset (Fin n)} (h : StepOkEnum w pair known sel) : StepOk w pair known := by
  intro mate ha hn
  have hinv : ∀ i, mate (mate i) = i := fun i => (ha i).2.1
  have hperf : ∀ i ∈ activeList w pair, mate i ∈ activeList w pair ∧ mate i ≠ i := fun i hi =>
    ⟨mem_activeList.mpr ((ha i).1.mp (mem_activeList.mp hi)),
      (ha i).2.2.1 (mem_activeList.mp hi)⟩
  obtain ⟨pairs, hpairs, hagree⟩ := complete n (activeList w pair) (activeList_length_le w pair)
    (activeList_pairwise w pair) mate hinv hperf hn
  obtain ⟨k, hk, hpk⟩ := List.getElem_of_mem hpairs
  obtain ⟨hunion, hmem⟩ := h k hk
  refine ⟨sel k, ?_, hmem⟩
  have heq : mateOf pairs = mate := by
    funext i
    by_cases hi : activeAt w pair i
    · exact hagree i (mem_activeList.mpr hi)
    · rw [(ha i).2.2.2 hi]
      have := mateOf_append_of_forall pairs [] i (fun p hp => by
        have hp' := mem_of_mem_enumPairs n _ pairs hpairs p hp
        exact ⟨fun e => hi (mem_activeList.mp (e ▸ hp'.1)),
          fun e => hi (mem_activeList.mp (e ▸ hp'.2))⟩)
      rw [List.append_nil] at this
      rw [this]; rfl
  unfold nodeMatchings at hunion
  rw [hpk, heq] at hunion
  exact hunion

/-- a certificate with switch sets -/
structure CertificateEnum (n : Nat) where
  nodes : List (Word n × TaitColorPair × (Nat → Finset (Fin n)))

def CertificateEnum.knownAt (base : Finset (Word n)) (c : CertificateEnum n) (k : Nat) :
    Finset (Word n) :=
  base ∪ ((c.nodes.take k).map fun t => t.1).toFinset

def CertificateEnum.Ok (base : Finset (Word n)) (c : CertificateEnum n) : Prop :=
  ∀ k (h : k < c.nodes.length),
    StepOkEnum (c.nodes[k]).1 (c.nodes[k]).2.1 (c.knownAt base k) (c.nodes[k]).2.2

instance (base : Finset (Word n)) (c : CertificateEnum n) : Decidable (c.Ok base) := by
  unfold CertificateEnum.Ok; infer_instance

/-- **soundness of enumerated certificates** -/
theorem CertificateEnum.derivable_of_ok {target : Set (Word n)} {base : Finset (Word n)}
    (hbase : ∀ u ∈ base, u ∈ target) (c : CertificateEnum n) (hok : c.Ok base) :
    ∀ k (h : k < c.nodes.length), Derivable target (c.nodes[k]).1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    refine Derivable.of_known (c.nodes[k]).2.1 (known := c.knownAt base k) ?_
      (stepOk_of_stepOkEnum (hok k h))
    intro u hu
    simp only [CertificateEnum.knownAt, Finset.mem_union, List.mem_toFinset, List.mem_map] at hu
    rcases hu with hu | ⟨t, hmem, rfl⟩
    · exact Derivable.base (hbase u hu)
    · obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
      rw [List.getElem_take] at hjk
      have hjlt : j < k := by
        have := hj; simp only [List.length_take] at this; omega
      have := ih j hjlt (by simp only [List.length_take] at hj; omega)
      rw [hjk] at this
      exact this

end KempeDerivation
end Mettapedia.GraphTheory.FourColor
