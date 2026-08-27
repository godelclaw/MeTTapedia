import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonFaceExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonTwoEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFirstReturnCap

/-!
# The facial walk through a digon

At the two digon vertices the facial walk does exactly two things.  The digon
itself is a face of length two, and each exterior half-edge re-enters the
retained region after a detour of length three:

```
a' -> (dart at u) -> (dart at v) -> rho b'
b' -> (dart at v) -> (dart at u) -> rho a'
```

Which named darts appear in the middle depends only on which of the two
parallel edges bounds the digon face, and the two cases are mirror images.

Two consequences: the first return of the ambient face permutation to the
retained darts sends `a'` to `rho b'` and `b'` to `rho a'`, which is exactly
the seam law of the two-edge-cut cap; and the digon face is the *only* ambient
face buried entirely in the deleted region.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFirstReturnCap
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable section

/-- A fixed-point-free permutation of a three-element set is a three-cycle:
one transition determines the other two. -/
theorem perm_three_cycle_of_step {A : Type*} (perm : Equiv.Perm A) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmem : ∀ x, x = a ∨ x = b ∨ x = c →
      perm x = a ∨ perm x = b ∨ perm x = c)
    (hfix : ∀ x, x = a ∨ x = b ∨ x = c → perm x ≠ x)
    (hstep : perm a = b) :
    perm b = c ∧ perm c = a := by
  have hbc' : perm b = c := by
    rcases hmem b (Or.inr (Or.inl rfl)) with hone | htwo | hthree
    · exfalso
      rcases hmem c (Or.inr (Or.inr rfl)) with hone' | htwo' | hthree'
      · exact hbc (perm.injective (hone.trans hone'.symm))
      · exact hac (perm.injective (hstep.trans htwo'.symm))
      · exact hfix c (Or.inr (Or.inr rfl)) hthree'
    · exact absurd htwo (hfix b (Or.inr (Or.inl rfl)))
    · exact hthree
  refine ⟨hbc', ?_⟩
  rcases hmem c (Or.inr (Or.inr rfl)) with hone | htwo | hthree
  · exact hone
  · exact absurd (perm.injective (hstep.trans htwo.symm)) hac
  · exact absurd hthree (hfix c (Or.inr (Or.inr rfl)))

namespace DigonPatchData

variable {RS : RotationSystem V E} (D : @DigonPatchData V E)

theorem phi_apply (dart : RS.D) : RS.phi dart = RS.rho (RS.alpha dart) := rfl

/-! ## The rotation at the two digon vertices is a three-cycle -/

theorem rho_ne_self_at_u (hD : D.WellFormed RS)
    (hrotation : VertexRotationCyclic RS) {dart : RS.D}
    (hdart : RS.vertOf dart = D.u) : RS.rho dart ≠ dart := by
  intro hfixed
  have hone : dart = D.p₁ hD :=
    (hrotation dart (D.p₁ hD) (by rw [hdart, D.vertOf_p₁ hD])).eq_of_left hfixed
  have htwo : dart = D.p₂ hD :=
    (hrotation dart (D.p₂ hD) (by rw [hdart, D.vertOf_p₂ hD])).eq_of_left hfixed
  exact D.p₁_ne_p₂ hD (hone.symm.trans htwo)

theorem rho_ne_self_at_v (hD : D.WellFormed RS)
    (hrotation : VertexRotationCyclic RS) {dart : RS.D}
    (hdart : RS.vertOf dart = D.v) : RS.rho dart ≠ dart := by
  intro hfixed
  have hone : dart = D.q₁ hD :=
    (hrotation dart (D.q₁ hD) (by rw [hdart, D.vertOf_q₁ hD])).eq_of_left hfixed
  have htwo : dart = D.q₂ hD :=
    (hrotation dart (D.q₂ hD) (by rw [hdart, D.vertOf_q₂ hD])).eq_of_left hfixed
  exact D.q₁_ne_q₂ hD (hone.symm.trans htwo)

/-- The three named darts at `u`, as a membership test. -/
theorem eq_of_vertOf_eq_u (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    {dart : RS.D} (hdart : RS.vertOf dart = D.u) :
    dart = D.p₁ hD ∨ dart = D.p₂ hD ∨ dart = D.pₐ hD := by
  have hmem : dart ∈ RS.dartsAt D.u := by
    simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hdart
  rw [D.dartsAt_u_eq hD hCubic] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem eq_of_vertOf_eq_v (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    {dart : RS.D} (hdart : RS.vertOf dart = D.v) :
    dart = D.q₁ hD ∨ dart = D.q₂ hD ∨ dart = D.qᵦ hD := by
  have hmem : dart ∈ RS.dartsAt D.v := by
    simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hdart
  rw [D.dartsAt_v_eq hD hCubic] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem darts_u_pairwise_ne (hD : D.WellFormed RS) (hCubic : RS.IsCubic) :
    D.p₁ hD ≠ D.p₂ hD ∧ D.p₁ hD ≠ D.pₐ hD ∧ D.p₂ hD ≠ D.pₐ hD := by
  have hedges := D.edges_u_pairwise_ne hD hCubic
  refine ⟨D.p₁_ne_p₂ hD, ?_, ?_⟩
  · intro h
    exact hedges.1 (by simpa using (congrArg RS.edgeOf h).symm)
  · intro h
    exact hedges.2.1 (by simpa using (congrArg RS.edgeOf h).symm)

theorem darts_v_pairwise_ne (hD : D.WellFormed RS) (hCubic : RS.IsCubic) :
    D.q₁ hD ≠ D.q₂ hD ∧ D.q₁ hD ≠ D.qᵦ hD ∧ D.q₂ hD ≠ D.qᵦ hD := by
  have hedges := D.edges_v_pairwise_ne hD hCubic
  refine ⟨D.q₁_ne_q₂ hD, ?_, ?_⟩
  · intro h
    exact hedges.1 (by simpa using (congrArg RS.edgeOf h).symm)
  · intro h
    exact hedges.2.1 (by simpa using (congrArg RS.edgeOf h).symm)

theorem rho_mem_u (hD : D.WellFormed RS) (hCubic : RS.IsCubic) {dart : RS.D}
    (hdart : dart = D.p₁ hD ∨ dart = D.p₂ hD ∨ dart = D.pₐ hD) :
    RS.rho dart = D.p₁ hD ∨ RS.rho dart = D.p₂ hD ∨
      RS.rho dart = D.pₐ hD := by
  refine D.eq_of_vertOf_eq_u hD hCubic ?_
  rw [RS.vert_rho]
  rcases hdart with rfl | rfl | rfl
  · exact D.vertOf_p₁ hD
  · exact D.vertOf_p₂ hD
  · exact D.vertOf_pₐ hD

theorem rho_mem_v (hD : D.WellFormed RS) (hCubic : RS.IsCubic) {dart : RS.D}
    (hdart : dart = D.q₁ hD ∨ dart = D.q₂ hD ∨ dart = D.qᵦ hD) :
    RS.rho dart = D.q₁ hD ∨ RS.rho dart = D.q₂ hD ∨
      RS.rho dart = D.qᵦ hD := by
  refine D.eq_of_vertOf_eq_v hD hCubic ?_
  rw [RS.vert_rho]
  rcases hdart with rfl | rfl | rfl
  · exact D.vertOf_q₁ hD
  · exact D.vertOf_q₂ hD
  · exact D.vertOf_qᵦ hD

/-- One rotation step at `u` determines the whole star. -/
theorem rho_u_cycle (hD : D.WellFormed RS)
    (hrotation : VertexRotationCyclic RS) {a b c : RS.D}
    (hlist : ({a, b, c} : Finset RS.D) = RS.dartsAt D.u)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hstep : RS.rho a = b) :
    RS.rho b = c ∧ RS.rho c = a := by
  have hverts : ∀ x, x = a ∨ x = b ∨ x = c → RS.vertOf x = D.u := by
    intro x hx
    have hmem : x ∈ ({a, b, c} : Finset RS.D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hx
    rw [hlist] at hmem
    simpa only [RotationSystem.dartsAt, Finset.mem_filter,
      Finset.mem_univ, true_and] using hmem
  refine perm_three_cycle_of_step RS.rho habc.1 habc.2.1 habc.2.2 ?_ ?_ hstep
  · intro x hx
    have hmem : RS.rho x ∈ ({a, b, c} : Finset RS.D) := by
      rw [hlist]
      simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [RS.vert_rho]
      exact hverts x hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  · intro x hx
    exact D.rho_ne_self_at_u hD hrotation (hverts x hx)

theorem rho_v_cycle (hD : D.WellFormed RS)
    (hrotation : VertexRotationCyclic RS) {a b c : RS.D}
    (hlist : ({a, b, c} : Finset RS.D) = RS.dartsAt D.v)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hstep : RS.rho a = b) :
    RS.rho b = c ∧ RS.rho c = a := by
  have hverts : ∀ x, x = a ∨ x = b ∨ x = c → RS.vertOf x = D.v := by
    intro x hx
    have hmem : x ∈ ({a, b, c} : Finset RS.D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hx
    rw [hlist] at hmem
    simpa only [RotationSystem.dartsAt, Finset.mem_filter,
      Finset.mem_univ, true_and] using hmem
  refine perm_three_cycle_of_step RS.rho habc.1 habc.2.1 habc.2.2 ?_ ?_ hstep
  · intro x hx
    have hmem : RS.rho x ∈ ({a, b, c} : Finset RS.D) := by
      rw [hlist]
      simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [RS.vert_rho]
      exact hverts x hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  · intro x hx
    exact D.rho_ne_self_at_v hD hrotation (hverts x hx)

/-! ## The facial walk around the digon -/

/-- **The digon detour.**  Both exterior half-edges return to the retained
region after exactly three face steps, through one dart at each digon vertex,
and the digon face itself is a two-cycle on the remaining two darts.  The six
listed darts are exactly the darts at the two digon vertices. -/
theorem digon_facial_walk (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (hface : D.HasExactDigonFace hD) :
    ∃ x y z w root other : RS.D,
      RS.phi (D.a' hD) = x ∧ RS.phi x = y ∧ RS.phi y = RS.rho (D.b' hD) ∧
      RS.phi (D.b' hD) = z ∧ RS.phi z = w ∧ RS.phi w = RS.rho (D.a' hD) ∧
      (∀ point, RS.phi.SameCycle root point ↔
        point = root ∨ point = other) ∧
      (∀ dart : RS.D,
        dart = x ∨ dart = y ∨ dart = z ∨ dart = w ∨
          dart = root ∨ dart = other →
        RS.vertOf dart = D.u ∨ RS.vertOf dart = D.v) ∧
      (∀ dart : RS.D, RS.vertOf dart = D.u ∨ RS.vertOf dart = D.v →
        dart = x ∨ dart = y ∨ dart = z ∨ dart = w ∨
          dart = root ∨ dart = other) := by
  have hphi : ∀ dart : RS.D, RS.phi dart = RS.rho (RS.alpha dart) :=
    fun _ => rfl
  have hu := D.darts_u_pairwise_ne hD hCubic
  have hv := D.darts_v_pairwise_ne hD hCubic
  have hcover : ∀ dart : RS.D, RS.vertOf dart = D.u ∨ RS.vertOf dart = D.v →
      dart = D.p₁ hD ∨ dart = D.p₂ hD ∨ dart = D.pₐ hD ∨
        dart = D.q₁ hD ∨ dart = D.q₂ hD ∨ dart = D.qᵦ hD := by
    intro dart hdart
    rcases hdart with hup | hvp
    · rcases D.eq_of_vertOf_eq_u hD hCubic hup with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases D.eq_of_vertOf_eq_v hD hCubic hvp with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  rcases hface with ⟨hq₁p₂, hp₂q₁, hcycle⟩ | ⟨hq₂p₁, hp₁q₂, hcycle⟩
  · -- the digon face is bounded on the `p₂`, `q₁` side
    have hrhop₁ : RS.rho (D.p₁ hD) = D.p₂ hD := by
      rw [← D.alpha_q₁ hD, ← hphi]; exact hq₁p₂
    have hrhoq₂ : RS.rho (D.q₂ hD) = D.q₁ hD := by
      rw [← D.alpha_p₂ hD, ← hphi]; exact hp₂q₁
    obtain ⟨hrhop₂, hrhopₐ⟩ :=
      D.rho_u_cycle hD hrotation
        (by rw [D.dartsAt_u_eq hD hCubic]) ⟨hu.1, hu.2.1, hu.2.2⟩ hrhop₁
    obtain ⟨hrhoq₁, hrhoqᵦ⟩ :=
      D.rho_v_cycle hD hrotation
        (by rw [D.dartsAt_v_eq hD hCubic, Finset.insert_comm])
        ⟨hv.1.symm, hv.2.2, hv.2.1⟩ hrhoq₂
    refine ⟨D.p₁ hD, D.qᵦ hD, D.q₂ hD, D.pₐ hD, D.q₁ hD, D.p₂ hD,
      ?_, ?_, ?_, ?_, ?_, ?_, hcycle, ?_, ?_⟩
    · rw [hphi, D.alpha_a' hD, hrhopₐ]
    · rw [hphi, D.alpha_p₁ hD, hrhoq₁]
    · rw [hphi, D.alpha_qᵦ hD]
    · rw [hphi, D.alpha_b' hD, hrhoqᵦ]
    · rw [hphi, D.alpha_q₂ hD, hrhop₂]
    · rw [hphi, D.alpha_pₐ hD]
    · rintro dart (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Or.inl (D.vertOf_p₁ hD)
      · exact Or.inr (D.vertOf_qᵦ hD)
      · exact Or.inr (D.vertOf_q₂ hD)
      · exact Or.inl (D.vertOf_pₐ hD)
      · exact Or.inr (D.vertOf_q₁ hD)
      · exact Or.inl (D.vertOf_p₂ hD)
    · intro dart hdart
      have := hcover dart hdart
      tauto
  · -- the mirror case: the digon face is bounded on the `p₁`, `q₂` side
    have hrhop₂ : RS.rho (D.p₂ hD) = D.p₁ hD := by
      rw [← D.alpha_q₂ hD, ← hphi]; exact hq₂p₁
    have hrhoq₁ : RS.rho (D.q₁ hD) = D.q₂ hD := by
      rw [← D.alpha_p₁ hD, ← hphi]; exact hp₁q₂
    obtain ⟨hrhop₁, hrhopₐ⟩ :=
      D.rho_u_cycle hD hrotation
        (by rw [D.dartsAt_u_eq hD hCubic, Finset.insert_comm])
        ⟨hu.1.symm, hu.2.2, hu.2.1⟩ hrhop₂
    obtain ⟨hrhoq₂, hrhoqᵦ⟩ :=
      D.rho_v_cycle hD hrotation
        (by rw [D.dartsAt_v_eq hD hCubic]) ⟨hv.1, hv.2.1, hv.2.2⟩ hrhoq₁
    refine ⟨D.p₂ hD, D.qᵦ hD, D.q₁ hD, D.pₐ hD, D.q₂ hD, D.p₁ hD,
      ?_, ?_, ?_, ?_, ?_, ?_, hcycle, ?_, ?_⟩
    · rw [hphi, D.alpha_a' hD, hrhopₐ]
    · rw [hphi, D.alpha_p₂ hD, hrhoq₂]
    · rw [hphi, D.alpha_qᵦ hD]
    · rw [hphi, D.alpha_b' hD, hrhoqᵦ]
    · rw [hphi, D.alpha_q₁ hD, hrhop₁]
    · rw [hphi, D.alpha_pₐ hD]
    · rintro dart (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Or.inl (D.vertOf_p₂ hD)
      · exact Or.inr (D.vertOf_qᵦ hD)
      · exact Or.inr (D.vertOf_q₁ hD)
      · exact Or.inl (D.vertOf_pₐ hD)
      · exact Or.inr (D.vertOf_q₂ hD)
      · exact Or.inl (D.vertOf_p₁ hD)
    · intro dart hdart
      have := hcover dart hdart
      tauto

/-! ## First returns and the buried face -/

section Retained

variable {keep : V → Prop}

theorem pow_two_phi (dart : RS.D) :
    (RS.phi ^ 2) dart = RS.phi (RS.phi dart) := by
  rw [pow_two]; rfl

theorem pow_three_phi (dart : RS.D) :
    (RS.phi ^ 3) dart = RS.phi (RS.phi (RS.phi dart)) := by
  rw [show (3 : Nat) = 2 + 1 from rfl, pow_succ, pow_two]; rfl

/-- The ambient facial walk first returns from `a'` to `rho b'`. -/
theorem nextHit_a'_eq (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (hface : D.HasExactDigonFace hD)
    (hkeep : ∀ vertex, ¬ keep vertex ↔ (vertex = D.u ∨ vertex = D.v))
    (ha : keep (RS.vertOf (D.a' hD))) (hb : keep (RS.vertOf (D.b' hD))) :
    (nextHit RS.phi (RetainedDartMark RS keep)
      (⟨D.a' hD, ha⟩ : {point // RetainedDartMark RS keep point})).1 =
      RS.rho (D.b' hD) := by
  obtain ⟨x, y, z, w, root, other, h1, h2, h3, h4, h5, h6, hcycle,
    hverts, hcover⟩ := D.digon_facial_walk hD hCubic hrotation hface
  have hone : (RS.phi ^ 1) (D.a' hD) = x := by rw [pow_one]; exact h1
  have htwo : (RS.phi ^ 2) (D.a' hD) = y := by
    rw [pow_two_phi, h1, h2]
  have hthree : (RS.phi ^ 3) (D.a' hD) = RS.rho (D.b' hD) := by
    rw [pow_three_phi, h1, h2, h3]
  have hhit : RetainedDartMark RS keep ((RS.phi ^ 3) (D.a' hD)) := by
    rw [hthree]
    change keep (RS.vertOf (RS.rho (D.b' hD)))
    rw [RS.vert_rho]
    exact hb
  have hbefore : ∀ step, 0 < step → step < 3 →
      ¬ RetainedDartMark RS keep ((RS.phi ^ step) (D.a' hD)) := by
    intro step hpos hlt
    interval_cases step
    · rw [hone]
      exact (hkeep _).2 (hverts x (by tauto))
    · rw [htwo]
      exact (hkeep _).2 (hverts y (by tauto))
  rw [nextHit_val_of_first_return RS.phi (RetainedDartMark RS keep)
    ⟨D.a' hD, ha⟩ (by norm_num) hbefore hhit]
  exact hthree

/-- The ambient facial walk first returns from `b'` to `rho a'`. -/
theorem nextHit_b'_eq (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (hface : D.HasExactDigonFace hD)
    (hkeep : ∀ vertex, ¬ keep vertex ↔ (vertex = D.u ∨ vertex = D.v))
    (ha : keep (RS.vertOf (D.a' hD))) (hb : keep (RS.vertOf (D.b' hD))) :
    (nextHit RS.phi (RetainedDartMark RS keep)
      (⟨D.b' hD, hb⟩ : {point // RetainedDartMark RS keep point})).1 =
      RS.rho (D.a' hD) := by
  obtain ⟨x, y, z, w, root, other, h1, h2, h3, h4, h5, h6, hcycle,
    hverts, hcover⟩ := D.digon_facial_walk hD hCubic hrotation hface
  have hone : (RS.phi ^ 1) (D.b' hD) = z := by rw [pow_one]; exact h4
  have htwo : (RS.phi ^ 2) (D.b' hD) = w := by
    rw [pow_two_phi, h4, h5]
  have hthree : (RS.phi ^ 3) (D.b' hD) = RS.rho (D.a' hD) := by
    rw [pow_three_phi, h4, h5, h6]
  have hhit : RetainedDartMark RS keep ((RS.phi ^ 3) (D.b' hD)) := by
    rw [hthree]
    change keep (RS.vertOf (RS.rho (D.a' hD)))
    rw [RS.vert_rho]
    exact ha
  have hbefore : ∀ step, 0 < step → step < 3 →
      ¬ RetainedDartMark RS keep ((RS.phi ^ step) (D.b' hD)) := by
    intro step hpos hlt
    interval_cases step
    · rw [hone]
      exact (hkeep _).2 (hverts z (by tauto))
    · rw [htwo]
      exact (hkeep _).2 (hverts w (by tauto))
  rw [nextHit_val_of_first_return RS.phi (RetainedDartMark RS keep)
    ⟨D.b' hD, hb⟩ (by norm_num) hbefore hhit]
  exact hthree

/-- **The digon face is the only buried face.**  Every other ambient facial
cycle still meets a retained dart. -/
theorem card_nonHitOrbit_eq_one (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (hface : D.HasExactDigonFace hD)
    (hkeep : ∀ vertex, ¬ keep vertex ↔ (vertex = D.u ∨ vertex = D.v))
    (ha : keep (RS.vertOf (D.a' hD))) (hb : keep (RS.vertOf (D.b' hD))) :
    Fintype.card (NonHitOrbit RS.phi (RetainedDartMark RS keep)) = 1 := by
  classical
  obtain ⟨x, y, z, w, root, other, h1, h2, h3, h4, h5, h6, hcycle,
    hverts, hcover⟩ := D.digon_facial_walk hD hCubic hrotation hface
  have hburied : ¬ ∃ point, RetainedDartMark RS keep point ∧
      (Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) point) =
        Quotient.mk _ root := by
    rintro ⟨point, hpoint, hq⟩
    have hsame : RS.phi.SameCycle root point :=
      (Quotient.exact hq : RS.phi.SameCycle point root).symm
    have hcase := (hcycle point).1 hsame
    have hvert : RS.vertOf point = D.u ∨ RS.vertOf point = D.v := by
      rcases hcase with hr | ho
      · exact hverts point (by tauto)
      · exact hverts point (by tauto)
    exact ((hkeep (RS.vertOf point)).2 hvert) hpoint
  refine Fintype.card_eq_one_iff.2 ⟨⟨Quotient.mk _ root, hburied⟩, ?_⟩
  intro orbit
  apply Subtype.ext
  have hnot : ¬ RetainedDartMark RS keep orbit.1.out :=
    nonHitOrbit_not_hit_of_sameCycle RS.phi (RetainedDartMark RS keep)
      orbit orbit.1.out (Equiv.Perm.SameCycle.refl _ _)
  have hvert : RS.vertOf orbit.1.out = D.u ∨ RS.vertOf orbit.1.out = D.v :=
    (hkeep _).1 hnot
  have hout : (Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
      orbit.1.out) = orbit.1 := Quotient.out_eq orbit.1
  have hexterior : ∀ (base : RS.D), keep (RS.vertOf base) →
      RS.phi.SameCycle base orbit.1.out → False := by
    intro base hbase hsame
    exact nonHitOrbit_not_hit_of_sameCycle RS.phi (RetainedDartMark RS keep)
      orbit base hsame.symm hbase
  have hsx : RS.phi.SameCycle (D.a' hD) x := ⟨1, by simpa using h1⟩
  have hxy : RS.phi.SameCycle x y := ⟨1, by simpa using h2⟩
  have hsz : RS.phi.SameCycle (D.b' hD) z := ⟨1, by simpa using h4⟩
  have hzw : RS.phi.SameCycle z w := ⟨1, by simpa using h5⟩
  rcases hcover orbit.1.out hvert with hx | hy | hz | hw | hr | ho
  · exact (hexterior (D.a' hD) ha (by rw [hx]; exact hsx)).elim
  · exact (hexterior (D.a' hD) ha (by rw [hy]; exact hsx.trans hxy)).elim
  · exact (hexterior (D.b' hD) hb (by rw [hz]; exact hsz)).elim
  · exact (hexterior (D.b' hD) hb (by rw [hw]; exact hsz.trans hzw)).elim
  · rw [← hout]
    exact Quotient.sound ((hcycle orbit.1.out).2 (Or.inl hr)).symm
  · rw [← hout]
    exact Quotient.sound ((hcycle orbit.1.out).2 (Or.inr ho)).symm

end Retained

end DigonPatchData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
