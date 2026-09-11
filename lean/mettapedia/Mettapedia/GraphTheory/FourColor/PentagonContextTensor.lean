import Mettapedia.GraphTheory.FourColor.PentagonPositiveResolution
import Mathlib.LinearAlgebra.Pi

/-!
# A positive five-port tensor invisible to the pentagon

The signed delta-epsilon span, after an explicit cyclic sign correction,
contains a nonnegative tensor supported exactly on the rejected admissible
words. Its ten colour-orbit coordinates obey four relations. Those relations
force any vector vanishing on the pentagon to lie on the same single ray.

These are statements about the displayed algebraic relaxation. No theorem
identifies every such vector with the count of an actual plane exterior.
The accompanying gate checks abstract noncrossing Kempe closure separately.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonContextTensor

abbrev Word := Fin 5 → Fin 3
abbrev Coordinates := Fin 10 → Int

def epsilon (a b c : Fin 3) : Int :=
  if a = b ∨ b = c ∨ a = c then 0
  else if (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) then 1 else -1

/-- First two entries are the wire pair, the other three its ordered complement. -/
def slots : Fin 10 → Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5
  | 0 => (0, 1, 2, 3, 4)
  | 1 => (0, 2, 1, 3, 4)
  | 2 => (0, 3, 1, 2, 4)
  | 3 => (0, 4, 1, 2, 3)
  | 4 => (1, 2, 0, 3, 4)
  | 5 => (1, 3, 0, 2, 4)
  | 6 => (1, 4, 0, 2, 3)
  | 7 => (2, 3, 0, 1, 4)
  | 8 => (2, 4, 0, 1, 3)
  | 9 => (3, 4, 0, 1, 2)

def deltaEpsilon (i : Fin 10) (w : Word) : Int :=
  let (a, b, c, d, e) := slots i
  if w a = w b then epsilon (w c) (w d) (w e) else 0

/-- Sign supplied by the first compatible adjacent wire and complementary Y.
Only the gauge-corrected tensor is used on inadmissible inputs. -/
def boundaryGauge (w : Word) : Int :=
  if w 0 = w 1 then epsilon (w 2) (w 3) (w 4)
  else if w 1 = w 2 then epsilon (w 0) (w 3) (w 4)
  else if w 2 = w 3 then epsilon (w 0) (w 1) (w 4)
  else if w 3 = w 4 then epsilon (w 0) (w 1) (w 2)
  else if w 0 = w 4 then epsilon (w 1) (w 2) (w 3) else 1

def basisValue (i : Fin 10) (w : Word) : Int := boundaryGauge w * deltaEpsilon i w

def tensor (c : Coordinates) (w : Word) : Int := ∑ i, c i * basisValue i w

/-- The majority colour is zero; the two singleton positions label the orbit. -/
def orbitWord (i : Fin 10) : Word := fun k =>
  if k = (slots i).1 then 1 else if k = (slots i).2.1 then 2 else 0

def rowTensor (c : Coordinates) : Coordinates := fun i => tensor c (orbitWord i)

private def basisCoordinates : Fin 10 → Coordinates
  | 0 => ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1]
  | 1 => ![0, 0, 0, 0, 0, -1, -1, 0, 0, 1]
  | 2 => ![0, 0, 0, 0, 1, 0, -1, 0, -1, 0]
  | 3 => ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0]
  | 4 => ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1]
  | 5 => ![0, -1, 0, 1, 0, 0, 0, 0, -1, 0]
  | 6 => ![0, -1, -1, 0, 0, 0, 0, 1, 0, 0]
  | 7 => ![1, 0, 0, 1, 0, 0, 1, 0, 0, 0]
  | 8 => ![1, 0, -1, 0, 0, -1, 0, 0, 0, 0]
  | 9 => ![1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

private theorem basisCoordinates_correct : ∀ i j,
    basisValue j (orbitWord i) = basisCoordinates i j := by decide +kernel

def Relations (f : Coordinates) : Prop :=
  -f 0 + f 1 - f 2 + f 3 = 0 ∧
  -f 0 + f 4 - f 5 + f 6 = 0 ∧
  -f 1 + f 4 - f 7 + f 8 = 0 ∧
  -f 2 + f 5 - f 7 + f 9 = 0

def PentagonZero (f : Coordinates) : Prop :=
  f 0 = 0 ∧ f 3 = 0 ∧ f 4 = 0 ∧ f 7 = 0 ∧ f 9 = 0

def badVector : Coordinates := ![0, 1, 1, 0, 0, 1, 1, 0, 1, 0]
def coefficients : Coordinates := ![0, -1, 0, 0, 1, -1, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem tensor_relations (c : Coordinates) : Relations (rowTensor c) := by
  simp only [Relations, rowTensor, tensor, basisCoordinates_correct]
  norm_num [Fin.sum_univ_succ, basisCoordinates]
  omega

theorem ray_of_relations (f : Coordinates) (hr : Relations f) (hz : PentagonZero f) :
    ∀ i, f i = f 1 * badVector i := by
  rcases hr with ⟨h1, h2, h3, h4⟩
  rcases hz with ⟨z0, z3, z4, z7, z9⟩
  have r2 : f 2 = f 1 := by omega
  have r5 : f 5 = f 1 := by omega
  have r6 : f 6 = f 1 := by omega
  have r8 : f 8 = f 1 := by omega
  intro i
  fin_cases i <;> simp [badVector, z0, z3, z4, z7, z9, r2, r5, r6, r8]

theorem positive_ray_of_relations (f : Coordinates) (hr : Relations f)
    (hz : PentagonZero f) (hn : ∀ i, 0 ≤ f i) :
    ∃ t : Int, 0 ≤ t ∧ ∀ i, f i = t * badVector i :=
  ⟨f 1, hn 1, ray_of_relations f hr hz⟩

theorem explicit_ray : rowTensor coefficients = badVector := by
  decide +kernel

def color : Fin 3 → Color
  | 0 => red
  | 1 => blue
  | 2 => purple

def admissible (w : Word) : Prop :=
  ∀ c : Fin 3, (Finset.univ.filter fun i => w i = c).card % 2 = 1

instance (w : Word) : Decidable (admissible w) := by
  unfold admissible
  infer_instance

def adversary (w : Word) : Int := basisValue 4 w - basisValue 1 w - basisValue 5 w

/-- Once one cycle edge is chosen, all others are forced by the boundary word. -/
def fastPentagonCount (w : Word) : Nat :=
  ((List.range 3).filter fun start =>
    ((List.ofFn w).foldl (fun edge port => edge.bind fun e =>
      if e = port.val then none else some (3 - e - port.val)) (some start)) ==
        some start).length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem count_rows : ∀ a b c d e : Fin 3,
    PentagonPositiveResolution.pentagonCount (color ∘ ![a, b, c, d, e]) =
      fastPentagonCount ![a, b, c, d, e] := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem pentagonCount_eq_fast (w : Word) :
    PentagonPositiveResolution.pentagonCount (color ∘ w) = fastPentagonCount w := by
  have hw : (![w 0, w 1, w 2, w 3, w 4] : Word) = w := by
    funext i
    fin_cases i <;> rfl
  simpa only [hw] using count_rows (w 0) (w 1) (w 2) (w 3) (w 4)

theorem adversary_eq_tensor (w : Word) : adversary w = tensor coefficients w := by
  simp [adversary, tensor, coefficients, Fin.sum_univ_succ]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem adversary_value : ∀ w : Word,
    adversary w = if admissible w ∧
      PentagonPositiveResolution.pentagonCount (color ∘ w) = 0 then 1 else 0 := by
  simp only [pentagonCount_eq_fast]
  decide +kernel

theorem adversary_nonnegative (w : Word) : 0 ≤ adversary w := by
  rw [adversary_value]
  split_ifs <;> norm_num

theorem adversary_zero_of_pentagon_pos (w : Word)
    (h : 0 < PentagonPositiveResolution.pentagonCount (color ∘ w)) :
    adversary w = 0 := by
  rw [adversary_value]
  simp [Nat.ne_of_gt h]

theorem adversary_nonzero : adversary (orbitWord 1) = 1 := by decide +kernel

/-- Each summand is a Y with an adjacent terminal wire, in cyclic order. -/
def cyclicStarWire (r : Fin 5) (w : Word) : Nat :=
  PentagonPositiveResolution.starWireCount (fun i => color (w (i + r)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The surviving vector is already in the signed span of six plane pieces:
the five cyclic Y-wires and the pentagon. -/
theorem signed_physical_identity : ∀ w : Word,
    adversary w = (∑ r : Fin 5, (cyclicStarWire r w : Int)) -
      2 * (PentagonPositiveResolution.pentagonCount (color ∘ w) : Int) := by
  simp only [pentagonCount_eq_fast]
  decide +kernel

def cyclicTree (r : Fin 5) (w : Word) : Nat :=
  PentagonPositiveResolution.treeCount (fun i => color (w (i + r)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Connected controls suffice too: five three-vertex trees and the pentagon.
In particular, disconnected wires are not responsible for the linear gap. -/
theorem signed_connected_identity : ∀ w : Word,
    3 * adversary w = (∑ r : Fin 5, (cyclicTree r w : Int)) -
      (PentagonPositiveResolution.pentagonCount (color ∘ w) : Int) := by
  simp only [pentagonCount_eq_fast]
  decide +kernel

/-- No homogeneous linear identity valid for these six connected count profiles
can distinguish the adversary from their linear span. This does not rule out
additional inequalities or information about a common physical realization. -/
theorem no_homogeneous_separator (L : (Word → Int) →ₗ[ℤ] Int)
    (ht : ∀ r, L (fun w => (cyclicTree r w : Int)) = 0)
    (hp : L (fun w => (PentagonPositiveResolution.pentagonCount (color ∘ w) : Int)) = 0) :
    L adversary = 0 := by
  have hi : (3 : Int) • adversary =
      (∑ r : Fin 5, fun w => (cyclicTree r w : Int)) -
        (fun w => (PentagonPositiveResolution.pentagonCount (color ∘ w) : Int)) := by
    funext w
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply] using
      signed_connected_identity w
  have h := congrArg L hi
  simp only [map_smul, map_sub, map_sum, ht, hp, Finset.sum_const_zero,
    sub_zero, smul_eq_mul] at h
  omega

end Mettapedia.GraphTheory.FourColor.PentagonContextTensor
