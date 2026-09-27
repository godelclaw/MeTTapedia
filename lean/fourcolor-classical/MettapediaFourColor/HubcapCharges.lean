import MettapediaFourColor.ChargeBound

/-!
# Hubcaps assembled from semantic charge bounds

The weighted-cover argument of Gonthier and Werner, formalized in Lean by
Chris Emery in `FourColor.HubCap`, applies to arbitrary integer charges.
Separating this arithmetic from the checker lets one combine checked and
transported bounds, including hubcaps with two-edge constraints.
-/

namespace FourColor

open scoped BigOperators

namespace Hubcap

/-- The constraints hold at every index belonging to the hub. -/
def Satisfies (n : ℕ) (q : ℕ → ℤ) : Hubcap → Prop
  | .nil => True
  | .one i b hc => (i < n → q i ≤ b) ∧ Satisfies n q hc
  | .two i j b hc => (i < n → j < n → q i + q j ≤ b) ∧ Satisfies n q hc

/-- The charge accounted for by a partial tally against the full cover. -/
def weightedCharge (n : ℕ) (v w : List ℕ) (q : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range n, (hubWeight (w.getD i 0) (v.getD i 0) : ℤ) * q i

theorem weightedCharge_incrNth {n i : ℕ} {v w : List ℕ} {q : ℕ → ℤ}
    (hi : i < n) (hle : w.getD i 0 + 1 ≤ v.getD i 0) (hv2 : v.getD i 0 ≤ 2) :
    weightedCharge n v (incrNth w i) q =
      (if v.getD i 0 = 1 then 2 else 1) * q i + weightedCharge n v w q := by
  have key : ∀ k,
      (hubWeight ((incrNth w i).getD k 0) (v.getD k 0) : ℤ) * q k =
        (hubWeight (w.getD k 0) (v.getD k 0) : ℤ) * q k +
          (if k = i then ((if v.getD i 0 = 1 then 2 else 1) : ℤ) * q i else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      have hstep : hubWeight (1 + w.getD k 0) (v.getD k 0) =
          hubWeight (w.getD k 0) (v.getD k 0) + (if v.getD k 0 = 1 then 2 else 1) := by
        unfold hubWeight
        split_ifs <;> omega
      have hgetD : (incrNth w k).getD k 0 = 1 + w.getD k 0 := by
        rw [getD_incrNth]
        simp [Nat.add_comm]
      rw [hgetD, hstep]
      simp only [ite_true]
      push_cast
      ring
    · simp only [getD_incrNth, Ne.symm hk, hk, ite_false, Nat.add_zero, add_zero]
  simp only [weightedCharge]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range n) i]
  simp only [Finset.mem_range, hi, ite_true]
  ring

/-- Cover recursion bounds the weighted sum independently of its source. -/
theorem coverRec_le {n : ℕ} {v : List ℕ} {q : ℕ → ℤ} (hvlen : v.length = n) :
    ∀ (hc : Hubcap) (b : ℤ), hubcapCoverRec v b hc = true → Satisfies n q hc →
      (∀ k, (tallyHubcap hc).getD k 0 ≤ v.getD k 0) →
      b ≤ -weightedCharge n v (tallyHubcap hc) q := by
  have hout : ∀ k, n ≤ k → v.getD k 0 = 0 := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  intro hc
  induction hc with
  | nil =>
    intro b hcov _ _
    have hb : ¬ (0 < b) := by simpa [hubcapCoverRec] using hcov
    simpa [weightedCharge, tallyHubcap, hubWeight] using (le_of_not_gt hb)
  | one i b' hc ih =>
    intro b hcov hfit hvb
    rw [hubcapCoverRec, Bool.and_eq_true] at hcov
    obtain ⟨hvi, hcov⟩ := hcov
    obtain ⟨hb', hfit⟩ := hfit
    have hvi1 : v.getD i 0 = 1 := by simpa using hvi
    have hi : i < n := by
      by_contra hi
      rw [hout i (by omega)] at hvi1
      omega
    have hvb' : ∀ k, (tallyHubcap hc).getD k 0 ≤ v.getD k 0 := by
      intro k
      have := hvb k
      rw [tallyHubcap, getD_incrNth] at this
      omega
    have hle : (tallyHubcap hc).getD i 0 + 1 ≤ v.getD i 0 := by
      have h := hvb i
      rw [tallyHubcap, getD_incrNth] at h
      simpa using h
    have hstep := weightedCharge_incrNth (q := q) hi hle (by omega)
    have hd := hb' hi
    have hih := ih (2 * b' + b) hcov hfit hvb'
    rw [tallyHubcap, hstep, hvi1]
    norm_num
    linarith
  | two i j b' hc ih =>
    intro b hcov hfit hvb
    rw [hubcapCoverRec, Bool.and_eq_true, Bool.and_eq_true] at hcov
    obtain ⟨⟨hvij, hv2⟩, hcov⟩ := hcov
    obtain ⟨hb', hfit⟩ := hfit
    have hvij' : v.getD i 0 = v.getD j 0 := by simpa using hvij
    have hv2' : v.getD i 0 ≤ 2 := by simpa using hv2
    have hvb1 : ∀ k, (incrNth (tallyHubcap hc) i).getD k 0 ≤ v.getD k 0 := by
      intro k
      have := hvb k
      rw [tallyHubcap, getD_incrNth] at this
      omega
    have hvb' : ∀ k, (tallyHubcap hc).getD k 0 ≤ v.getD k 0 := by
      intro k
      have := hvb1 k
      rw [getD_incrNth] at this
      omega
    have hlei : (tallyHubcap hc).getD i 0 + 1 ≤ v.getD i 0 := by
      have h := hvb1 i
      rw [getD_incrNth] at h
      simpa using h
    have hlej : (incrNth (tallyHubcap hc) i).getD j 0 + 1 ≤ v.getD j 0 := by
      have h := hvb j
      rw [tallyHubcap, getD_incrNth] at h
      simpa using h
    have hi : i < n := by
      by_contra hi
      rw [hout i (by omega)] at hlei
      omega
    have hj : j < n := by
      by_contra hj
      rw [hout j (by omega)] at hlej
      omega
    have hstepj := weightedCharge_incrNth (q := q) hj hlej (by omega)
    have hstepi := weightedCharge_incrNth (q := q) hi hlei hv2'
    have hd := hb' hi hj
    have hih := ih _ hcov hfit hvb'
    rw [tallyHubcap, hstepj, hstepi, ← hvij']
    by_cases hv1 : v.getD i 0 = 1
    · rw [hv1] at hih ⊢
      norm_num at hih ⊢
      linarith
    · simp only [hv1, ite_false] at hih ⊢
      linarith

/-- A checked cover and its semantic constraints bound the total hub charge. -/
theorem charge_le {n : ℕ} {hc : Hubcap} {q : ℕ → ℤ}
    (hcover : hubcapCover n hc = true) (hfit : Satisfies n q hc) :
    dboundK n + ∑ i ∈ Finset.range n, q i ≤ 0 := by
  set v := tallyHubcap hc with hv
  rw [hubcapCover, Bool.and_eq_true, Bool.and_eq_true] at hcover
  obtain ⟨⟨hvlen, hv0⟩, hcov⟩ := hcover
  have hvlen' : v.length = n := by simpa using hvlen
  have hvpos : ∀ k, k < n → 1 ≤ v.getD k 0 := by
    intro k hk
    have hk' : k < v.length := by omega
    have hmem : v[k] ∈ v := List.getElem_mem hk'
    have hne : v[k] ≠ 0 := by
      intro h0
      rw [h0] at hmem
      have hcontains : v.contains 0 = true := List.contains_iff_mem.mpr hmem
      rw [hcontains] at hv0
      simp at hv0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    omega
  have hbound := coverRec_le hvlen' hc _ hcov hfit (fun _ => le_rfl)
  have hfull : weightedCharge n v v q = 2 * ∑ i ∈ Finset.range n, q i := by
    rw [weightedCharge, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := hvpos k (Finset.mem_range.mp hk)
    have hw : hubWeight (v.getD k 0) (v.getD k 0) = 2 := by
      unfold hubWeight
      split_ifs <;> omega
    rw [hw]
    rfl
  rw [← hv, hfull] at hbound
  omega

end Hubcap

/-- A bound on the sum of the two edge charges selected by a fitting part. -/
def PairChargeBound (p : Part) (j : ℕ) (b : ℤ) : Prop :=
  ∀ {D : Type} [Finite D] (G : Hypermap D) (x : D),
    ValidHub G x → G.ExactFitp x p →
      G.dscore2 (G.face (G.face x)) +
        G.dscore2 (G.face (G.face (G.face^[j] x))) ≤ b

/-- Convert a two-edge check into a bound on the actual transferred charge. -/
theorem PairChargeBound.of_check {redp : Part → Bool} (hred : RedpartSound redp)
    {n : ℕ} (rf : DruleFork Part.conversePart n) {p : Part} {j : ℕ} {b : ℤ}
    (hsize : p.size = n) (hj : j ≤ n)
    (hcheck : check2Dbound2 redp rf p j b = true) : PairChargeBound p j b := by
  intro D _ G x hx hfit
  have harity : G.arity x = n := hfit.1.trans hsize
  have hb := Hypermap.check2Dbound2_le
    (fun y q hq => hred G hx.mce y q hq) harity hfit hj hcheck
  rw [rf.target_eq, rf.source_eq] at hb
  have conv := converseSpec_conversePart hx.mce.plain hx.mce.cubic hx.pentagonal
  have h₁ := G.dbound2_le hx.mce.plain conv harity
  have h₂ := G.dbound2_le hx.mce.plain conv
    (show G.arity (G.face^[j] x) = n by rw [G.arity_iterate_face, harity])
  exact (add_le_add h₁ h₂).trans hb

namespace Hubcap

/-- A hubcap whose entries have semantic certificates, independent of how
those certificates were obtained. -/
def SemanticFit (n : ℕ) (p : Part) : Hubcap → Prop
  | .nil => True
  | .one j b hc => ChargeBound (hubcapRot n j p) b ∧ SemanticFit n p hc
  | .two i j b hc =>
      PairChargeBound (hubcapRot n i p) (hubSubn n j i) b ∧ SemanticFit n p hc

/-- Semantic bounds suffice for the same weighted cover used by the checker. -/
theorem successful {n : ℕ} {p : Part} {hc : Hubcap}
    (hsize : p.size = n) (h2 : 2 ≤ n) (hcover : hubcapCover n hc = true)
    (hsem : SemanticFit n p hc) : Successful p := by
  intro D _ G x hx hfit
  have harity : G.arity x = n := hfit.1.trans hsize
  have hy : ValidHub G (G.invFace2 x) := by
    rw [Hypermap.invFace2_eq_iterate G x (by omega)]
    exact hx.iterate_face _
  have hyr : G.arity (G.invFace2 x) = n := by
    rw [Hypermap.invFace2_eq_iterate G x (by omega), G.arity_iterate_face, harity]
  let q := fun j => G.dscore2 (G.face (G.face (G.face^[j] (G.invFace2 x))))
  have holds : ∀ hc, SemanticFit n p hc → Satisfies n q hc := by
    intro cap
    induction cap with
    | nil => intro _; trivial
    | one j b cap ih =>
      rintro ⟨hj, ht⟩
      refine ⟨fun hjn => ?_, ih ht⟩
      exact hj G _ (hy.iterate_face j) (G.exactFitp_hubcapRot harity h2 hjn hfit)
    | two i j b cap ih =>
      rintro ⟨hij, ht⟩
      refine ⟨fun hin _ => ?_, ih ht⟩
      have hb := hij G _ (hy.iterate_face i)
        (G.exactFitp_hubcapRot harity h2 hin hfit)
      rw [G.iterate_hubSubn hin (G.invFace2 x) hyr] at hb
      exact hb
  have budget := charge_le hcover (holds hc hsem)
  have hpos := hy.pos
  rw [Hypermap.dscore, ← G.sum_map_face_face _ G.dscore2,
    G.sum_orbitList_face, hyr] at hpos
  unfold dboundK at budget
  dsimp [q] at budget
  omega

/-- Use a semantic hubcap at any presentation goal. -/
theorem succeeds {n : ℕ} {p : Part} (p₀ : Part) (hc : Hubcap)
    (hsize : p.size = n) (h2 : 2 ≤ n) (hcover : hubcapCover n hc = true)
    (hsem : SemanticFit n p hc) : SucceedsIn p₀ p := by
  intro _
  exact successful hsize h2 hcover hsem

end Hubcap

end FourColor
