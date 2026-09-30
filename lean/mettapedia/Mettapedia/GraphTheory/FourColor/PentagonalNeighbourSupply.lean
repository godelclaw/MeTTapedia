import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces

/-!
# Pentagonal neighbour density supplies a flanked edge

The observation is made on actual face darts, with incidence multiplicity.
Three pentagonal neighbours of a five- or six-sided face force two positions
separated by one edge. In a cubic rotation these give the two pentagonal
flanks of an edge. The face and vertex counts then show that a spherical
all-five/six map with fewer than 56 vertices has such an edge.

The geometric diamond consumer identifies the appropriate six-, seven- or
eight-port reduction. No colouring or catalogue theorem enters this module.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalNeighbourSupply

open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceCyclicOrder
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided PhysicalForkCodeFaces

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

def size (d : RS.D) : ℕ := (RS.faceOrbit d).card

def ShortFaces : Prop := ∀ d : RS.D, size RS d = 5 ∨ size RS d = 6

/-- The two faces at the ends of an edge, other than its two incident faces. -/
def Flanked (d : RS.D) : Prop :=
  size RS (RS.rho (RS.rho d)) = 5 ∧
    size RS (RS.rho (RS.rho (RS.alpha d))) = 5

def neighbours (f : OrbitFace RS) : Finset RS.D :=
  (orbitFaceDarts RS f).filter fun d => size RS (RS.alpha d) = 5

/-- The usual boundary-edge fullerene predicate supplies the actual dart
lengths when the ambient map has two distinct facial sides at every edge. -/
theorem shortFaces_of_fullerene (htwo : OrbitFacesTwoSided RS)
    (hf : OrbitFaceFullerene RS) : ShortFaces RS := by
  intro d
  have h := hf (dartOrbitFace RS d)
  rw [orbitFaceBoundarySimple_of_twoSided RS htwo,
    orbitFaceDarts_dartOrbitFace_eq_faceOrbit] at h
  exact h

theorem size_phi (d : RS.D) : size RS (RS.phi d) = size RS d := by
  unfold size
  rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
    dartOrbitFace_phi_eq, orbitFaceDarts_dartOrbitFace_eq_faceOrbit]

theorem size_pow (d : RS.D) (k : ℕ) : size RS ((RS.phi ^ k) d) = size RS d := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [pow_succ', Equiv.Perm.mul_apply, size_phi] using ih

theorem flanked_flip (d : RS.D) : Flanked RS (RS.alpha d) ↔ Flanked RS d := by
  simp only [Flanked, RS.alpha_involutive, and_comm]

theorem next_flank (d : RS.D) :
    size RS (RS.alpha (RS.phi d)) = size RS (RS.rho (RS.rho (RS.alpha d))) := by
  have h := size_phi RS (RS.alpha (RS.phi d))
  simpa only [RotationSystem.phi, Equiv.Perm.mul_apply, RS.alpha_involutive] using h.symm

theorem previous_flank (hC : Cubic3 RS) (d : RS.D) :
    RS.rho (RS.rho (RS.phi d)) = RS.alpha d := by
  exact hC.cube (RS.alpha d)

theorem last_flank (hC : Cubic3 RS) (d : RS.D) (n : ℕ)
    (hp : (RS.phi ^ (n + 1)) d = d) :
    size RS (RS.alpha ((RS.phi ^ n) d)) = size RS (RS.rho (RS.rho d)) := by
  have he : RS.phi ((RS.phi ^ n) d) = d := by
    simpa only [pow_succ', Equiv.Perm.mul_apply] using hp
  rw [← previous_flank RS hC, he]

private theorem gap_five : ∀ b : Fin 5 → Bool,
    2 < (Finset.univ.filter fun i => b i = true).card →
      ∃ i, b i = true ∧ b (i + 2) = true := by decide +kernel

private theorem gap_six : ∀ b : Fin 6 → Bool,
    2 < (Finset.univ.filter fun i => b i = true).card →
      ∃ i, b i = true ∧ b (i + 2) = true := by decide +kernel

private def indexEquiv (root : RS.D) (n : ℕ) (hn : size RS root = n) :
    Fin n ≃ {d // d ∈ RS.faceOrbit root} :=
  (finCongr hn.symm).trans (faceOrbitDartEquiv RS root)

private theorem indexEquiv_val (root : RS.D) (n : ℕ) (hn : size RS root = n)
    (i : Fin n) : (indexEquiv RS root n hn i).val = (RS.phi ^ i.val) root := rfl

theorem neighbours_card_index (root : RS.D) (n : ℕ) (hn : size RS root = n) :
    (Finset.univ.filter fun i : Fin n =>
      size RS (RS.alpha ((RS.phi ^ i.val) root)) = 5).card =
        (neighbours RS (dartOrbitFace RS root)).card := by
  unfold neighbours
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
  apply Finset.card_bij (fun i _ => (RS.phi ^ i.val) root)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(indexEquiv RS root n hn i).property,
      (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    exact (indexEquiv RS root n hn).injective (Subtype.ext he)
  · intro d hd
    obtain ⟨i, hi⟩ := (indexEquiv RS root n hn).surjective
      ⟨d, (Finset.mem_filter.mp hd).1⟩
    have hv := congrArg Subtype.val hi
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hv⟩
    simpa only [← indexEquiv_val RS root n hn, hv] using (Finset.mem_filter.mp hd).2

/-- Local supply from three incidences. Distinct neighbouring faces are not
assumed: the observation retains the actual positions on the facial cycle. -/
theorem exists_flanked_of_three (hC : Cubic3 RS) (hs : ShortFaces RS)
    (face : OrbitFace RS) (hthree : 2 < (neighbours RS face).card) :
    ∃ d : RS.D, Flanked RS d := by
  obtain ⟨root, rfl⟩ := exists_dartOrbitFace_eq RS face
  rcases hs root with h5 | h6
  · let p (i : Fin 5) := (RS.phi ^ i.val) root
    have hp : (RS.phi ^ 5) root = root := by
      have hp := (phi_isCycleOn_faceOrbit RS root).pow_card_apply (RS.mem_faceOrbit_self root)
      change (RS.phi ^ size RS root) root = root at hp
      simpa only [h5] using hp
    have step (i : Fin 5) : p (i + 1) = RS.phi (p i) := by
      fin_cases i <;> first | rfl | exact hp.symm
    have hc : 2 < (Finset.univ.filter fun i : Fin 5 =>
        decide (size RS (RS.alpha (p i)) = 5) = true).card := by
      simpa only [decide_eq_true_eq, p, neighbours_card_index RS root 5 h5] using hthree
    obtain ⟨i, hi, hj⟩ := gap_five _ hc
    simp only [decide_eq_true_eq] at hi hj
    refine ⟨p (i + 1), ?_, ?_⟩
    · simpa only [step, previous_flank RS hC] using hi
    · rw [← next_flank, ← step]
      simpa only [add_assoc, show (1 : Fin 5) + 1 = 2 from rfl] using hj
  · let p (i : Fin 6) := (RS.phi ^ i.val) root
    have hp : (RS.phi ^ 6) root = root := by
      have hp := (phi_isCycleOn_faceOrbit RS root).pow_card_apply (RS.mem_faceOrbit_self root)
      change (RS.phi ^ size RS root) root = root at hp
      simpa only [h6] using hp
    have step (i : Fin 6) : p (i + 1) = RS.phi (p i) := by
      fin_cases i <;> first | rfl | exact hp.symm
    have hc : 2 < (Finset.univ.filter fun i : Fin 6 =>
        decide (size RS (RS.alpha (p i)) = 5) = true).card := by
      simpa only [decide_eq_true_eq, p, neighbours_card_index RS root 6 h6] using hthree
    obtain ⟨i, hi, hj⟩ := gap_six _ hc
    simp only [decide_eq_true_eq] at hi hj
    refine ⟨p (i + 1), ?_, ?_⟩
    · simpa only [step, previous_flank RS hC] using hi
    · rw [← next_flank, ← step]
      simpa only [add_assoc, show (1 : Fin 6) + 1 = 2 from rfl] using hj

/-- Reversing every dart counts the same pentagonal incidences at their
opposite ends. Repeated incidences are counted, rather than discarded. -/
theorem sum_neighbours :
    ∑ f : OrbitFace RS, (neighbours RS f).card =
      ∑ f : OrbitFace RS, if (orbitFaceDarts RS f).card = 5
        then (orbitFaceDarts RS f).card else 0 := by
  classical
  calc
    _ = ∑ d : RS.D, if size RS (RS.alpha d) = 5 then 1 else 0 := by
      simp only [neighbours, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_fiberwise Finset.univ (dartOrbitFace RS) _
    _ = ∑ d : RS.D, if size RS d = 5 then 1 else 0 :=
      Equiv.sum_comp RS.alpha (fun d => if size RS d = 5 then (1 : ℕ) else 0)
    _ = ∑ f : OrbitFace RS, ∑ d ∈ orbitFaceDarts RS f,
        if size RS d = 5 then 1 else 0 :=
      (Finset.sum_fiberwise Finset.univ (dartOrbitFace RS) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      have same (d : RS.D) (hd : d ∈ orbitFaceDarts RS f) :
          size RS d = (orbitFaceDarts RS f).card := by
        rw [size, ← orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
          (mem_orbitFaceDarts_iff RS f d).mp hd]
      calc
        _ = ∑ _d ∈ orbitFaceDarts RS f,
            if (orbitFaceDarts RS f).card = 5 then (1 : ℕ) else 0 :=
          Finset.sum_congr rfl fun d hd => by rw [same d hd]
        _ = _ := by split_ifs <;> simp

/-- Absence of the three diamond shapes forces at least thirty faces and
56 vertices. This is a density consequence, not a universal supply claim. -/
theorem fiftysix_le_of_not_flanked (hC : Cubic3 RS) (hs : ShortFaces RS)
    (sphere : OrbitSphericalCubicMapData RS) (hn : ∀ d, ¬ Flanked RS d) :
    56 ≤ Fintype.card V := by
  have hb (f : OrbitFace RS) : (neighbours RS f).card ≤ 2 := by
    by_contra h
    obtain ⟨d, hd⟩ := exists_flanked_of_three RS hC hs f (by omega)
    exact hn d hd
  have ht : (∑ f : OrbitFace RS, if (orbitFaceDarts RS f).card = 5
      then (orbitFaceDarts RS f).card else 0) ≤ 2 * Fintype.card (OrbitFace RS) := by
    rw [← sum_neighbours]
    calc
      _ ≤ ∑ _f : OrbitFace RS, (2 : ℕ) := Finset.sum_le_sum fun f _ => hb f
      _ = _ := by simp [Nat.mul_comm]
  have hl (f : OrbitFace RS) :
      (if (orbitFaceDarts RS f).card = 5 then ((orbitFaceDarts RS f).card : ℤ) else 0) =
        30 - 5 * (orbitFaceDarts RS f).card := by
    obtain ⟨d, rfl⟩ := exists_dartOrbitFace_eq RS f
    rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
    rcases hs d with h | h <;> change (RS.faceOrbit d).card = _ at h <;> rw [h] <;> norm_num
  have ht' : (∑ f : OrbitFace RS, if (orbitFaceDarts RS f).card = 5
      then ((orbitFaceDarts RS f).card : ℤ) else 0) ≤ 2 * Fintype.card (OrbitFace RS) := by
    exact_mod_cast ht
  simp_rw [hl] at ht'
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at ht'
  have hd := sum_card_orbitFaceDarts_eq_card_darts RS
  have hd' : (∑ f : OrbitFace RS, ((orbitFaceDarts RS f).card : ℤ)) = Fintype.card RS.D := by
    exact_mod_cast hd
  rw [hd'] at ht'
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht'
  have hv := RS.card_darts_eq_three_times_card_vertices sphere.cubic
  have he := RS.card_darts_eq_twice_card_edges
  have hv' : (Fintype.card RS.D : ℤ) = 3 * Fintype.card V := by exact_mod_cast hv
  have he' : (Fintype.card RS.D : ℤ) = 2 * Fintype.card E := by exact_mod_cast he
  have heuler := sphere.euler
  omega

theorem exists_flanked_of_card_lt_fiftysix (hC : Cubic3 RS) (hs : ShortFaces RS)
    (sphere : OrbitSphericalCubicMapData RS) (hlt : Fintype.card V < 56) :
    ∃ d : RS.D, Flanked RS d := by
  by_contra hn
  have hb := fiftysix_le_of_not_flanked RS hC hs sphere (by simpa only [not_exists] using hn)
  omega

end
end Mettapedia.GraphTheory.FourColor.PentagonalNeighbourSupply
