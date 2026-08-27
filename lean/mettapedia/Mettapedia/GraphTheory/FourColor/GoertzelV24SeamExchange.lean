import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitExchange
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition

/-!
# The seam exchange: hub closures, and the face count of a glue

Close an open side by adding a hub vertex whose darts are a copy of the
boundary, each paired with its original, with a chosen rotation at the hub.  The
closed side is an ordinary rotation system; its faces through the hub are the
side's *hub faces*, one per boundary segment.

Glue two closed sides along a matching of their ports.  On the joint dart
carrier this changes only the pairing, and only at the ports: a port's real dart
is re-paired across the seam, and its hub dart is re-paired with the opposite
hub dart.  Performing the exchange one port at a time gives a family of
permutations indexed by finite sets of ports, which grows by exactly the two
transpositions the orbit exchange lemma expects.

The upshot: with the two hub rotations reversing each other across the
matching, the exchanged permutation has the same orbit count as the disjoint
union of the two closed sides.  Reading its two summands — the real darts, which
carry the composite's face permutation, and the hub darts, which carry a dipole
with `k` faces — that is the face count `F(comp) + k = F(L̂) + F(R̂)`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SeamExchange

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24OrbitExchange
open GoertzelV24OrbitCountCongr
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData

/-! ## Closing one side with a hub -/

section Hub

variable {V I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]

/-- The pairing of a closed side: interior darts by the interior involution,
each boundary dart with its hub copy. -/
def hubAlphaFun (T : OpenTangleData V I B) : (I ⊕ B) ⊕ B → (I ⊕ B) ⊕ B
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (T.interiorAlpha i))
  | Sum.inl (Sum.inr b) => Sum.inr b
  | Sum.inr b => Sum.inl (Sum.inr b)

theorem hubAlphaFun_involutive (T : OpenTangleData V I B) :
    Function.Involutive (hubAlphaFun T) := by
  rintro ((i | b) | b)
  · simp [hubAlphaFun, T.interiorAlpha_involutive]
  · rfl
  · rfl

/-- The pairing of a closed side, as a permutation. -/
def hubAlpha (T : OpenTangleData V I B) : Perm ((I ⊕ B) ⊕ B) :=
  (hubAlphaFun_involutive T).toPerm

@[simp] theorem hubAlpha_apply (T : OpenTangleData V I B) (x : (I ⊕ B) ⊕ B) :
    hubAlpha T x = hubAlphaFun T x := rfl

/-- The face permutation of a closed side, with hub rotation `ρhub`. -/
def hubPhi (T : OpenTangleData V I B) (ρhub : Perm B) : Perm ((I ⊕ B) ⊕ B) :=
  Equiv.sumCongr T.rho ρhub * hubAlpha T

/-- **A side is a disc**: its hub faces are distinct — no face orbit passes the
hub twice. -/
def HubFacesDistinct (T : OpenTangleData V I B) (ρhub : Perm B) : Prop :=
  ∀ b b' : B, (hubPhi T ρhub).SameCycle (Sum.inr b) (Sum.inr b') → b = b'

end Hub

/-! ## The joint carrier and the exchanged pairings -/

section Joint

variable {V W I L J R : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (left : OpenTangleData V I L) (right : OpenTangleData W J R)
  (matching : L ≃ R) (ρL : Perm L) (ρR : Perm R)

/-- Both closed sides on one carrier. -/
abbrev Joint (I L J R : Type*) := ((I ⊕ L) ⊕ L) ⊕ ((J ⊕ R) ⊕ R)

/-- The rotation of the joint carrier: each side's rotation on its real darts,
each hub rotation on its hub darts. -/
def jointRho : Perm (Joint I L J R) :=
  Equiv.sumCongr (Equiv.sumCongr left.rho ρL) (Equiv.sumCongr right.rho ρR)

/-- The pairing after exchanging the ports in `S`.  A port `b` is *seamed* once
`b ∈ S` and its hub is *rehung* once `ρL⁻¹ b ∈ S`; the two conditions differ
because a port's split is paired with the merge of the port before it in hub
order. -/
def alphaFun (S : Finset L) : Joint I L J R → Joint I L J R
  | Sum.inl (Sum.inl (Sum.inl i)) => Sum.inl (Sum.inl (Sum.inl (left.interiorAlpha i)))
  | Sum.inl (Sum.inl (Sum.inr b)) =>
      if b ∈ S then Sum.inr (Sum.inl (Sum.inr (matching b))) else Sum.inl (Sum.inr b)
  | Sum.inl (Sum.inr b) =>
      if ρL.symm b ∈ S then Sum.inr (Sum.inr (matching b)) else Sum.inl (Sum.inl (Sum.inr b))
  | Sum.inr (Sum.inl (Sum.inl j)) => Sum.inr (Sum.inl (Sum.inl (right.interiorAlpha j)))
  | Sum.inr (Sum.inl (Sum.inr c)) =>
      if ρL.symm (matching.symm c) ∈ S then Sum.inl (Sum.inl (Sum.inr (matching.symm c)))
      else Sum.inr (Sum.inr c)
  | Sum.inr (Sum.inr c) =>
      if matching.symm c ∈ S then Sum.inl (Sum.inr (matching.symm c))
      else Sum.inr (Sum.inl (Sum.inr c))

/-- The inverse pairing: the same map with the two port conditions swapped. -/
def alphaInv (S : Finset L) : Joint I L J R → Joint I L J R
  | Sum.inl (Sum.inl (Sum.inl i)) => Sum.inl (Sum.inl (Sum.inl (left.interiorAlpha i)))
  | Sum.inl (Sum.inl (Sum.inr b)) =>
      if ρL.symm b ∈ S then Sum.inr (Sum.inl (Sum.inr (matching b))) else Sum.inl (Sum.inr b)
  | Sum.inl (Sum.inr b) =>
      if b ∈ S then Sum.inr (Sum.inr (matching b)) else Sum.inl (Sum.inl (Sum.inr b))
  | Sum.inr (Sum.inl (Sum.inl j)) => Sum.inr (Sum.inl (Sum.inl (right.interiorAlpha j)))
  | Sum.inr (Sum.inl (Sum.inr c)) =>
      if matching.symm c ∈ S then Sum.inl (Sum.inl (Sum.inr (matching.symm c)))
      else Sum.inr (Sum.inr c)
  | Sum.inr (Sum.inr c) =>
      if ρL.symm (matching.symm c) ∈ S then Sum.inl (Sum.inr (matching.symm c))
      else Sum.inr (Sum.inl (Sum.inr c))

theorem alphaInv_alphaFun (S : Finset L) (x : Joint I L J R) :
    alphaInv left right matching ρL S (alphaFun left right matching ρL S x) = x := by
  rcases x with ((i | b) | b) | ((j | c) | c)
  · simp [alphaFun, alphaInv, left.interiorAlpha_involutive]
  · by_cases h : b ∈ S <;> simp [alphaFun, alphaInv, h]
  · by_cases h : ρL.symm b ∈ S <;> simp [alphaFun, alphaInv, h]
  · simp [alphaFun, alphaInv, right.interiorAlpha_involutive]
  · by_cases h : ρL.symm (matching.symm c) ∈ S <;> simp [alphaFun, alphaInv, h]
  · by_cases h : matching.symm c ∈ S <;> simp [alphaFun, alphaInv, h]

theorem alphaFun_alphaInv (S : Finset L) (x : Joint I L J R) :
    alphaFun left right matching ρL S (alphaInv left right matching ρL S x) = x := by
  rcases x with ((i | b) | b) | ((j | c) | c)
  · simp [alphaFun, alphaInv, left.interiorAlpha_involutive]
  · by_cases h : ρL.symm b ∈ S <;> simp [alphaFun, alphaInv, h]
  · by_cases h : b ∈ S <;> simp [alphaFun, alphaInv, h]
  · simp [alphaFun, alphaInv, right.interiorAlpha_involutive]
  · by_cases h : matching.symm c ∈ S <;> simp [alphaFun, alphaInv, h]
  · by_cases h : ρL.symm (matching.symm c) ∈ S <;> simp [alphaFun, alphaInv, h]

/-- The exchanged pairing, as a permutation. -/
def alphaS (S : Finset L) : Perm (Joint I L J R) where
  toFun := alphaFun left right matching ρL S
  invFun := alphaInv left right matching ρL S
  left_inv := alphaInv_alphaFun left right matching ρL S
  right_inv := alphaFun_alphaInv left right matching ρL S

@[simp] theorem alphaS_apply (S : Finset L) (x : Joint I L J R) :
    alphaS left right matching ρL S x = alphaFun left right matching ρL S x := rfl

/-- The face permutation after exchanging the ports in `S`. -/
def phiS (S : Finset L) : Perm (Joint I L J R) :=
  jointRho left right ρL ρR * alphaS left right matching ρL S

/-! ## The four transposition points of one port -/

/-- The merging transposition of port `q` acts on the images of its real dart
and of the opposite hub dart; the splitting transposition of port `q` acts on
the images of the hub dart at `ρL q` and of the opposite real dart there. -/
def mergeA (q : L) : Joint I L J R := Sum.inl (Sum.inl (Sum.inr q))
def mergeB (q : L) : Joint I L J R := Sum.inr (Sum.inr (matching q))
def splitA (q : L) : Joint I L J R := Sum.inl (Sum.inr (ρL q))
def splitB (q : L) : Joint I L J R := Sum.inr (Sum.inl (Sum.inr (matching (ρL q))))

/-- Their images: the four points the orbit exchange lemma swaps. -/
def uPt (q : L) : Joint I L J R := Sum.inl (Sum.inr (ρL q))
def vPt (q : L) : Joint I L J R := Sum.inr (Sum.inl (right.rho (Sum.inr (matching q))))
def uPt' (q : L) : Joint I L J R := Sum.inl (Sum.inl (left.rho (Sum.inr (ρL q))))
def vPt' (q : L) : Joint I L J R := Sum.inr (Sum.inr (ρR (matching (ρL q))))

/-- **Adding a port to the exchanged set is two right transpositions of the
pairing.** -/
theorem alphaS_insert (S : Finset L) (q : L) (hq : q ∉ S) :
    alphaS left right matching ρL (insert q S) =
      alphaS left right matching ρL S *
        swap (mergeA (I := I) (J := J) (R := R) q) (mergeB matching (I := I) (J := J) q) *
          swap (splitA ρL (I := I) (J := J) (R := R) q)
            (splitB matching ρL (I := I) (J := J) q) := by
  ext x
  simp only [Perm.mul_apply, alphaS_apply]
  rcases x with ((i | b) | b) | ((j | c) | c)
  · simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB]
  · by_cases hb : b = q
    · subst hb
      simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hq]
    · simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hb, Finset.mem_insert]
  · by_cases hb : b = ρL q
    · subst hb
      simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hq]
    · have h1 : ρL.symm b ≠ q := fun h => hb (by rw [← h, Equiv.apply_symm_apply])
      simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hb, h1, Finset.mem_insert]
  · simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB]
  · by_cases hc : c = matching (ρL q)
    · subst hc
      simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hq]
    · have h1 : ρL.symm (matching.symm c) ≠ q := fun h =>
        hc (by rw [← Equiv.apply_symm_apply matching c, ← Equiv.apply_symm_apply ρL (matching.symm c), h])
      simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hc, h1, Finset.mem_insert]
  · by_cases hc : c = matching q
    · subst hc
      simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hq]
    · have h1 : matching.symm c ≠ q := fun h => hc (by rw [← h, Equiv.apply_symm_apply])
      simp [alphaFun, swap_apply_def, mergeA, mergeB, splitA, splitB, hc, h1, Finset.mem_insert]

/-- The images of the four transposition points under the unexchanged
permutation at `q`. -/
theorem phiS_mergeA (S : Finset L) (q : L) (hq : q ∉ S) :
    phiS left right matching ρL ρR S (mergeA (I := I) (J := J) (R := R) q) =
      uPt ρL (I := I) (J := J) (R := R) q := by
  simp [phiS, jointRho, alphaFun, mergeA, uPt, Perm.mul_apply, hq]

theorem phiS_mergeB (S : Finset L) (q : L) (hq : q ∉ S) :
    phiS left right matching ρL ρR S (mergeB matching (I := I) (J := J) q) =
      vPt right matching (I := I) (L := L) q := by
  simp [phiS, jointRho, alphaFun, mergeB, vPt, Perm.mul_apply, hq]

theorem phiS_splitA (S : Finset L) (q : L) (hq : q ∉ S) :
    phiS left right matching ρL ρR S (splitA ρL (I := I) (J := J) (R := R) q) =
      uPt' left ρL (I := I) (J := J) (R := R) q := by
  simp [phiS, jointRho, alphaFun, splitA, uPt', Perm.mul_apply, hq]

theorem phiS_splitB (S : Finset L) (q : L) (hq : q ∉ S) :
    phiS left right matching ρL ρR S (splitB matching ρL (I := I) (J := J) q) =
      vPt' matching ρL ρR (I := I) (J := J) q := by
  simp [phiS, jointRho, alphaFun, splitB, vPt', Perm.mul_apply, hq]

/-- **The step equation**, in the form the orbit exchange lemma consumes. -/
theorem phiS_insert (S : Finset L) (q : L) (hq : q ∉ S) :
    phiS left right matching ρL ρR (insert q S) =
      swap (uPt' left ρL (I := I) (J := J) (R := R) q) (vPt' matching ρL ρR (I := I) (J := J) q) *
        (swap (uPt ρL (I := I) (J := J) (R := R) q) (vPt right matching (I := I) (L := L) q) *
          phiS left right matching ρL ρR S) := by
  have hα := alphaS_insert left right matching ρL S q hq
  rw [phiS, hα, ← mul_assoc, ← mul_assoc]
  change (phiS left right matching ρL ρR S * _) * _ = _
  rw [GoertzelV24OrbitCountCongr.mul_swap_eq_swap_mul (phiS left right matching ρL ρR S)
      (mergeA (I := I) (J := J) (R := R) q) (mergeB matching (I := I) (J := J) q),
    mul_assoc,
    GoertzelV24OrbitCountCongr.mul_swap_eq_swap_mul (phiS left right matching ρL ρR S)
      (splitA ρL (I := I) (J := J) (R := R) q) (splitB matching ρL (I := I) (J := J) q),
    phiS_mergeA left right matching ρL ρR S q hq, phiS_mergeB left right matching ρL ρR S q hq,
    phiS_splitA left right matching ρL ρR S q hq, phiS_splitB left right matching ρL ρR S q hq,
    ← mul_assoc, swap_mul_swap_comm, mul_assoc]
  · simp [uPt, uPt']
  · simp [uPt, vPt']
  · simp [vPt, uPt']
  · simp [vPt, vPt']

/-! ## Before any exchange: the two closed sides -/

/-- The unexchanged permutation is the disjoint sum of the two closed sides'
face permutations. -/
theorem phiS_empty :
    phiS left right matching ρL ρR ∅ =
      Equiv.sumCongr (hubPhi left ρL) (hubPhi right ρR) := by
  ext x
  rcases x with ((i | b) | b) | ((j | c) | c) <;>
    simp [phiS, jointRho, alphaFun, hubPhi, hubAlphaFun, Perm.mul_apply]

theorem hubPhi_inr {V' I' B' : Type*} [Fintype I'] [DecidableEq I'] [Fintype B'] [DecidableEq B']
    (T : OpenTangleData V' I' B') (ρ : Perm B') (b : B') :
    hubPhi T ρ (Sum.inr b) = Sum.inl (T.rho (Sum.inr b)) := by
  simp [hubPhi, hubAlphaFun, Perm.mul_apply]

/-! ## The face count of the glue -/

/-- **Orientation reversal**: the right hub rotation is the inverse of the left
one, read through the matching. -/
def OrientationReversing (matching : L ≃ R) (ρL : Perm L) (ρR : Perm R) : Prop :=
  ∀ b : L, ρR (matching b) = matching (ρL.symm b)

/-- **The seam exchange preserves the orbit count.**  With both sides discs and
the matching orientation reversing, the fully exchanged permutation has as many
orbits as the two closed sides together. -/
theorem orbitCount_phiS_univ
    (hL : HubFacesDistinct left ρL) (hR : HubFacesDistinct right ρR)
    (hrev : OrientationReversing matching ρL ρR) :
    orbitCount (phiS left right matching ρL ρR Finset.univ) =
      orbitCount (hubPhi left ρL) + orbitCount (hubPhi right ρR) := by
  rw [← orbitCount_sumCongr, ← phiS_empty left right matching ρL ρR]
  refine orbitCount_exchange_univ (phiS left right matching ρL ρR)
    (uPt ρL) (vPt right matching) (uPt' left ρL) (vPt' matching ρL ρR)
    (fun S q hq => phiS_insert left right matching ρL ρR S q hq) ?_ ?_ ?_ ?_ ?_
  · -- distinct ports have distinct hub faces
    intro p q hpq
    rw [phiS_empty]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      rw [uPt, uPt, sameCycle_sumCongr_inl_iff] at h
      exact hpq (ρL.injective (hL _ _ h))
    · exact not_sameCycle_sumCongr_inl_inr _ _ _ _
    · intro h
      exact not_sameCycle_sumCongr_inl_inr _ _ _ _ h.symm
    · intro h
      rw [vPt, vPt, sameCycle_sumCongr_inr_iff, ← hubPhi_inr, ← hubPhi_inr,
        sameCycle_apply_left, sameCycle_apply_right] at h
      exact hpq (matching.injective (hR _ _ h))
  · intro p
    rw [phiS_empty]
    exact not_sameCycle_sumCongr_inl_inr _ _ _ _
  · intro p
    rw [phiS_empty, uPt, uPt', sameCycle_sumCongr_inl_iff, ← hubPhi_inr, sameCycle_apply_right]
    try exact SameCycle.refl _ _
  · intro p
    rw [phiS_empty, vPt, vPt', hrev, Equiv.symm_apply_apply, sameCycle_sumCongr_inr_iff,
      ← hubPhi_inr, sameCycle_apply_left]
    try exact SameCycle.refl _ _
  · intro p
    simp [uPt', vPt']

end Joint

end GoertzelV24SeamExchange

end Mettapedia.GraphTheory.FourColor
