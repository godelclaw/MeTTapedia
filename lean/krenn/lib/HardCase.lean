import Mathlib
import Amplitude
import MatchingSum
import PurePartner
import SingleFlip
import Degenerate
import FanStructure
import MinimalSupport
import LiveDegree
import Separation

/-!
# The hard case, with its hypotheses discharged

What is left of the conjecture is one configuration: a support-minimal system, a site whose
live partners are its three named ones and a single extra, and a complementary sum at that
extra which vanishes in every colour.  There the constant colourings supply no certificate at
all — and yet minimality forces one to exist, non-constant.

This file assembles that entry point.  Everything the site-local arguments need is derived
rather than assumed: diagonality of the named blocks from the vanishing constant sums, and
the certificate from minimality.  What comes out is a colouring that pins the named partner
of every live row of the extra block.
-/

namespace HardCase

open Amplitude MatchingSum SingleFlip Degenerate FanStructure MinimalSupport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The hard case, entered.**  In a support-minimal system, at a site whose live partners
are its three named ones and a single live extra with all complementary constant sums
vanishing, there is a colouring of the complement whose matching sum survives, and it pins the
named partner of every live row of the extra block. -/
theorem certificate_pins (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (hdegen : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0) :
    ∃ c : V → Fin 3, pmSum W c ((Finset.univ.erase u).erase v) ≠ 0
      ∧ ∀ α b : Fin 3, W s((u, α), (v, b)) ≠ 0 → c (wn α) = α := by
  classical
  obtain ⟨hone, hzero⟩ := hmin.1
  -- the named blocks are single diagonal entries
  have hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0 := by
    intro j a b hab
    rcases hab with ha | hb
    · by_cases hbj : b = j
      · rw [hbj]
        exact diag_of_complement_zero W hone hzero hvu wn hwu hvw hcol hlone j
          (hdegen j) a ha
      · exact hcol j a b hbj
    · exact hcol j a b hb
  -- minimality supplies a surviving colouring
  have hni : ¬ Inert W u v := not_inert_of_supportMinimal hmin hvu hlive
  obtain ⟨c, hc⟩ : ∃ c : V → Fin 3,
      pmSum W c ((Finset.univ.erase u).erase v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hni h
  refine ⟨c, hc, ?_⟩
  intro α b hab
  set c' : V → Fin 3 := Function.update (Function.update c u α) v b with hc'
  have hcv : c' v = b := by rw [hc']; simp
  have hcu : c' u = α := by
    rw [hc', Function.update_of_ne (Ne.symm hvu), Function.update_self]
  have hoff : ∀ z : V, z ≠ u → z ≠ v → c' z = c z := by
    intro z hzu hzv
    rw [hc', Function.update_of_ne hzv, Function.update_of_ne hzu]
  have hP : pmSum W c' ((Finset.univ.erase u).erase v) ≠ 0 := by
    have : pmSum W c' ((Finset.univ.erase u).erase v)
        = pmSum W c ((Finset.univ.erase u).erase v) := by
      refine pmSum_congr_colour W fun z hz => ?_
      exact hoff z (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1
        (Finset.mem_erase.mp hz).1
    rw [this]; exact hc
  have hnc : ¬ Amplitude.Monochromatic c' := by
    rintro ⟨k, hk⟩
    refine hP ?_
    have : pmSum W c' ((Finset.univ.erase u).erase v)
        = pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) :=
      pmSum_congr_colour W fun z _ => hk z
    rw [this, hdegen k]
  have hrow : W s((u, α), (v, c' v)) ≠ 0 := by rw [hcv]; exact hab
  have := named_pinned_of_certificate W hzero hvu wn hwu hvw hdiag hlone α c' hcu hnc hP hrow
  rwa [hoff (wn α) (hwu α) (fun h => hvw α h.symm)] at this

/-! ### Both ends of a thick edge -/

/-- **A thick edge forces degree four at both ends.**  If the block over a pair has two
distinct live rows, then neither endpoint sees the other as a column-supported partner: the
column fan at the far end names three partners, none of them this one, so the far end has at
least four live neighbours.

This is the compatibility the two ends of an edge force on each other.  A fourth live
partner is not a local accident: unless the block is confined to a single row, it propagates
across the edge. -/
theorem four_live_at_far_end (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u v : V} (hvu : v ≠ u)
    {a a' : Fin 3} (haa : a ≠ a')
    (hb : ∃ b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (hb' : ∃ b' : Fin 3, W s((u, a'), (v, b')) ≠ 0) :
    4 ≤ (LiveDegree.liveNbrs W v).card := by
  classical
  have hv2 : 2 ≤ (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    have : (Finset.univ : Finset V).card = Fintype.card V := rfl
    omega
  obtain ⟨vn, hinj, hne, hcolv, hlivev⟩ :=
    PurePartner.exists_column_fan W hone hzero hv2
  -- `u` is not one of `v`'s named partners
  have hunot : ∀ j : Fin 3, u ≠ vn j := by
    intro j hj
    have hkill : ∀ (x : Fin 3) (y : Fin 3), y ≠ j → W s((u, y), (v, x)) = 0 := by
      intro x y hy
      have := hcolv j x y hy
      rw [hj]
      rw [Sym2.eq_swap]
      exact this
    obtain ⟨b, hbne⟩ := hb
    obtain ⟨b', hbne'⟩ := hb'
    by_cases haj : a = j
    · exact hbne' (hkill b' a' (fun h => haa (haj.trans h.symm)))
    · exact hbne (hkill b a haj)
  -- four distinct live neighbours of `v`
  have hsub : ({vn 0, vn 1, vn 2, u} : Finset V) ⊆ LiveDegree.liveNbrs W v := by
    intro z hz
    rw [LiveDegree.mem_liveNbrs]
    have hmem : (∃ j : Fin 3, z = vn j) ∨ z = u := by
      rcases Finset.mem_insert.mp hz with h | h
      · exact Or.inl ⟨0, h⟩
      · rcases Finset.mem_insert.mp h with h | h
        · exact Or.inl ⟨1, h⟩
        · rcases Finset.mem_insert.mp h with h | h
          · exact Or.inl ⟨2, h⟩
          · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hmem with ⟨j, rfl⟩ | rfl
    · obtain ⟨x, hx⟩ := hlivev j
      exact ⟨hne j, x, j, hx⟩
    · obtain ⟨b, hbne⟩ := hb
      refine ⟨fun h => hvu h.symm, b, a, ?_⟩
      rw [Sym2.eq_swap]
      exact hbne
  have hcard4 : ({vn 0, vn 1, vn 2, u} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => hunot 2 h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (hinj h) (by decide), fun h => hunot 1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (hinj h) (by decide), fun h => absurd (hinj h) (by decide),
        fun h => hunot 0 h.symm⟩
  calc 4 = ({vn 0, vn 1, vn 2, u} : Finset V).card := hcard4.symm
    _ ≤ (LiveDegree.liveNbrs W v).card := Finset.card_le_card hsub

/-- **A block between two three-regular sites is a single entry.**  Degree three at the far
end confines the block to one row; degree three at the near end confines it to one column.
Together they leave one entry, so an edge between two three-regular sites is monochromatic at
each end --- the compatibility the two ends force on each other. -/
theorem single_entry_of_deg_three (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u v : V} (hvu : v ≠ u)
    (hu3 : (LiveDegree.liveNbrs W u).card ≤ 3)
    (hv3 : (LiveDegree.liveNbrs W v).card ≤ 3) :
    ∃ a₀ b₀ : Fin 3, ∀ a b : Fin 3, (a ≠ a₀ ∨ b ≠ b₀) → W s((u, a), (v, b)) = 0 := by
  classical
  -- at most one live row, read from `u`
  have hrow : ∀ a a' : Fin 3, a ≠ a' →
      (∃ b, W s((u, a), (v, b)) ≠ 0) → (∃ b', W s((u, a'), (v, b')) ≠ 0) → False := by
    intro a a' haa hb hb'
    exact absurd (four_live_at_far_end W hone hzero hcard hvu haa hb hb') (by omega)
  -- at most one live column, read from `v`
  have hcolm : ∀ b b' : Fin 3, b ≠ b' →
      (∃ a, W s((u, a), (v, b)) ≠ 0) → (∃ a', W s((u, a'), (v, b')) ≠ 0) → False := by
    intro b b' hbb hb hb'
    have huv : u ≠ v := fun h => hvu h.symm
    have hb2 : ∃ a, W s((v, b), (u, a)) ≠ 0 := by
      obtain ⟨a, ha⟩ := hb; exact ⟨a, by rw [Sym2.eq_swap]; exact ha⟩
    have hb2' : ∃ a', W s((v, b'), (u, a')) ≠ 0 := by
      obtain ⟨a', ha'⟩ := hb'; exact ⟨a', by rw [Sym2.eq_swap]; exact ha'⟩
    exact absurd (four_live_at_far_end W hone hzero hcard huv hbb hb2 hb2') (by omega)
  by_cases hzeroblock : ∀ a b : Fin 3, W s((u, a), (v, b)) = 0
  · exact ⟨0, 0, fun a b _ => hzeroblock a b⟩
  · push_neg at hzeroblock
    obtain ⟨a₀, b₀, hab⟩ := hzeroblock
    refine ⟨a₀, b₀, fun a b hne => ?_⟩
    by_contra hlive
    rcases hne with ha | hb
    · exact hrow a a₀ ha ⟨b, hlive⟩ ⟨b₀, hab⟩
    · exact hcolm b b₀ hb ⟨a, hlive⟩ ⟨a₀, hab⟩

/-! ### A three-regular end cannot be degenerate -/

/-- **A three-regular neighbour forbids degeneracy in its own colour.**  At a site of degree
three the live partners are exactly the three the fan names, so the blocks there are single
diagonal entries.  The flip relation at that site, in the colour naming this edge, then has a
single surviving term: the edge back, times the complementary sum.  It equals the amplitude,
which is non-zero — so the complementary sum is non-zero too.

Consequently a site whose complementary sums with an extra vanish in *every* colour cannot
have that extra be three-regular: the excess degree sits at both ends of such an edge. -/
theorem complement_ne_zero_of_deg_three (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u v : V} (hvu : v ≠ u)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (hv3 : (LiveDegree.liveNbrs W v).card ≤ 3) :
    ∃ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) ≠ 0 := by
  classical
  have hv2 : 2 ≤ (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    have : (Finset.univ : Finset V).card = Fintype.card V := rfl
    omega
  obtain ⟨vn, hinj, hne, hcolv, hlivev⟩ :=
    PurePartner.exists_column_fan W hone hzero hv2
  -- the fan exhausts the live neighbourhood
  have hsub : ({vn 0, vn 1, vn 2} : Finset V) ⊆ LiveDegree.liveNbrs W v := by
    intro z hz
    have hmem : ∃ j : Fin 3, z = vn j := by
      rcases Finset.mem_insert.mp hz with h | h
      · exact ⟨0, h⟩
      · rcases Finset.mem_insert.mp h with h | h
        · exact ⟨1, h⟩
        · exact ⟨2, Finset.mem_singleton.mp h⟩
    obtain ⟨j, rfl⟩ := hmem
    obtain ⟨x, hx⟩ := hlivev j
    exact LiveDegree.mem_liveNbrs.mpr ⟨hne j, x, j, hx⟩
  have hcard3 : ({vn 0, vn 1, vn 2} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => absurd (hinj h) (by decide)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (hinj h) (by decide), fun h => absurd (hinj h) (by decide)⟩
  have heq : LiveDegree.liveNbrs W v = {vn 0, vn 1, vn 2} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3]; exact hv3)).symm
  have hdead : ∀ y : V, y ≠ v → (∀ j, y ≠ vn j) → ∀ a b : Fin 3, W s((v, a), (y, b)) = 0 := by
    intro y hyv hyn a b
    by_contra hne'
    have hmem : y ∈ LiveDegree.liveNbrs W v :=
      LiveDegree.mem_liveNbrs.mpr ⟨hyv, a, b, hne'⟩
    rw [heq] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hyn 0 h
    · rcases Finset.mem_insert.mp h with h | h
      · exact hyn 1 h
      · exact hyn 2 (Finset.mem_singleton.mp h)
  -- the blocks at `v` are single diagonal entries
  have hdiagv : ∀ (k a : Fin 3), a ≠ k → W s((v, a), (vn k, k)) = 0 := fun k a ha =>
    PurePartner.diag_of_three_partners W hone hzero
      (Finset.card_pos.mp (by omega) : (Finset.univ.erase v).Nonempty) vn hcolv hdead k a ha
  -- `u` is one of the three
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin 3, u = vn j := by
    obtain ⟨a, b, hab⟩ := hlive
    have hmem : u ∈ LiveDegree.liveNbrs W v := by
      refine LiveDegree.mem_liveNbrs.mpr ⟨fun h => hvu h.symm, b, a, ?_⟩
      rw [Sym2.eq_swap]; exact hab
    rw [heq] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact ⟨0, h⟩
    · rcases Finset.mem_insert.mp h with h | h
      · exact ⟨1, h⟩
      · exact ⟨2, Finset.mem_singleton.mp h⟩
  refine ⟨j₀, ?_⟩
  intro hzeroSum
  -- the flip relation at `v` in colour `j₀` has one surviving term
  have htot := flip_diag_eq W v j₀
  have humem : u ∈ Finset.univ.erase v :=
    Finset.mem_erase.mpr ⟨fun h => hvu h.symm, Finset.mem_univ u⟩
  have hsingle : ∑ z ∈ Finset.univ.erase v, W s((v, j₀), (z, j₀))
      * pmSum W (Amplitude.const (V := V) j₀) ((Finset.univ.erase v).erase z)
      = W s((v, j₀), (u, j₀))
        * pmSum W (Amplitude.const (V := V) j₀) ((Finset.univ.erase v).erase u) := by
    rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr humem), Finset.sum_singleton]
    intro z hzmem hz
    have hzv : z ≠ v := (Finset.mem_erase.mp hzmem).1
    have hzu : z ≠ u := fun h => hz (by rw [h]; exact Finset.mem_singleton_self _)
    by_cases hj : ∀ j, z ≠ vn j
    · rw [hdead z hzv hj j₀ j₀, zero_mul]
    · push_neg at hj
      obtain ⟨j, hjz⟩ := hj
      have hjj : j₀ ≠ j := by
        intro h
        exact hzu (by rw [hjz, ← h, ← hj₀])
      rw [hjz, hcolv j j₀ j₀ hjj, zero_mul]
  rw [hsingle] at htot
  have hcomm : (Finset.univ.erase v).erase u = (Finset.univ.erase u).erase v :=
    Finset.erase_right_comm
  rw [hcomm, hzeroSum, mul_zero] at htot
  exact hone j₀ htot.symm

/-- **The hard case has excess degree at both ends.**  If every complementary constant sum at
an extra vanishes, that extra cannot be three-regular. -/
theorem four_live_at_degenerate_end (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u v : V} (hvu : v ≠ u)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (hdegen : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0) :
    4 ≤ (LiveDegree.liveNbrs W v).card := by
  by_contra h
  obtain ⟨k, hk⟩ := complement_ne_zero_of_deg_three W hone hzero hcard hvu hlive (by omega)
  exact hk (hdegen k)

/-! ### One three-regular end already rigidifies the block -/

/-- At a site of degree three the fan exhausts the live neighbourhood, so the blocks there are
single diagonal entries and everything else is dead. -/
theorem structure_of_deg_three (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {v : V}
    (hv3 : (LiveDegree.liveNbrs W v).card ≤ 3) :
    ∃ vn : Fin 3 → V, Function.Injective vn ∧ (∀ j, vn j ≠ v) ∧
      (∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((v, a), (vn j, b)) = 0) ∧
      (∀ y : V, y ≠ v → (∀ j, y ≠ vn j) → ∀ a b : Fin 3, W s((v, a), (y, b)) = 0) ∧
      LiveDegree.liveNbrs W v = {vn 0, vn 1, vn 2} := by
  classical
  have hv2 : 2 ≤ (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    have : (Finset.univ : Finset V).card = Fintype.card V := rfl
    omega
  obtain ⟨vn, hinj, hne, hcolv, hlivev⟩ :=
    PurePartner.exists_column_fan W hone hzero hv2
  have hsub : ({vn 0, vn 1, vn 2} : Finset V) ⊆ LiveDegree.liveNbrs W v := by
    intro z hz
    have hmem : ∃ j : Fin 3, z = vn j := by
      rcases Finset.mem_insert.mp hz with h | h
      · exact ⟨0, h⟩
      · rcases Finset.mem_insert.mp h with h | h
        · exact ⟨1, h⟩
        · exact ⟨2, Finset.mem_singleton.mp h⟩
    obtain ⟨j, rfl⟩ := hmem
    obtain ⟨x, hx⟩ := hlivev j
    exact LiveDegree.mem_liveNbrs.mpr ⟨hne j, x, j, hx⟩
  have hcard3 : ({vn 0, vn 1, vn 2} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => absurd (hinj h) (by decide)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (hinj h) (by decide), fun h => absurd (hinj h) (by decide)⟩
  have heq : LiveDegree.liveNbrs W v = {vn 0, vn 1, vn 2} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3]; exact hv3)).symm
  have hdead : ∀ y : V, y ≠ v → (∀ j, y ≠ vn j) → ∀ a b : Fin 3, W s((v, a), (y, b)) = 0 := by
    intro y hyv hyn a b
    by_contra hne'
    have hmem : y ∈ LiveDegree.liveNbrs W v :=
      LiveDegree.mem_liveNbrs.mpr ⟨hyv, a, b, hne'⟩
    rw [heq] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hyn 0 h
    · rcases Finset.mem_insert.mp h with h | h
      · exact hyn 1 h
      · exact hyn 2 (Finset.mem_singleton.mp h)
  refine ⟨vn, hinj, hne, ?_, hdead, heq⟩
  intro j a b hab
  rcases hab with ha | hb
  · by_cases hbj : b = j
    · rw [hbj]
      exact PurePartner.diag_of_three_partners W hone hzero
        (Finset.card_pos.mp (by omega) : (Finset.univ.erase v).Nonempty) vn hcolv hdead j a ha
    · exact hcolv j a b hbj
  · exact hcolv j a b hb

/-- **One three-regular end makes the block a single entry.**  If a site has degree three,
then every block at it is the single diagonal entry of the colour naming that partner --- so
the edge is monochromatic, in the same colour at both ends.  This strictly strengthens the
two-ended version: only one end need be three-regular. -/
theorem single_entry_of_one_deg_three (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u v : V} (hvu : v ≠ u)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (hv3 : (LiveDegree.liveNbrs W v).card ≤ 3) :
    ∃ j₀ : Fin 3, ∀ a b : Fin 3, (a ≠ j₀ ∨ b ≠ j₀) → W s((u, a), (v, b)) = 0 := by
  classical
  obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
    structure_of_deg_three W hone hzero hcard hv3
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin 3, u = vn j := by
    obtain ⟨a, b, hab⟩ := hlive
    have hmem : u ∈ LiveDegree.liveNbrs W v := by
      refine LiveDegree.mem_liveNbrs.mpr ⟨fun h => hvu h.symm, b, a, ?_⟩
      rw [Sym2.eq_swap]; exact hab
    rw [heq] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact ⟨0, h⟩
    · rcases Finset.mem_insert.mp h with h | h
      · exact ⟨1, h⟩
      · exact ⟨2, Finset.mem_singleton.mp h⟩
  refine ⟨j₀, fun a b hab => ?_⟩
  have := hdiagv j₀ b a (by rcases hab with h | h; exacts [Or.inr h, Or.inl h])
  rw [← hj₀] at this
  rw [Sym2.eq_swap]
  exact this

/-! ### Excess degree cannot sit alone -/

/-- A three-regular site has exactly one live partner in the colour naming a given edge, and
it is the far end of that edge. -/
theorem unique_colour_partner_of_deg_three (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u y : V} (hyu : y ≠ u)
    (hlive : ∃ a b : Fin 3, W s((u, a), (y, b)) ≠ 0)
    (hy3 : (LiveDegree.liveNbrs W y).card ≤ 3) :
    ∃ k : Fin 3, ∀ z : V, z ≠ y → W s((y, k), (z, k)) ≠ 0 → z = u := by
  classical
  obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
    structure_of_deg_three W hone hzero hcard hy3
  obtain ⟨k, hk⟩ : ∃ j : Fin 3, u = vn j := by
    obtain ⟨a, b, hab⟩ := hlive
    have hmem : u ∈ LiveDegree.liveNbrs W y := by
      refine LiveDegree.mem_liveNbrs.mpr ⟨fun h => hyu h.symm, b, a, ?_⟩
      rw [Sym2.eq_swap]; exact hab
    rw [heq] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact ⟨0, h⟩
    · rcases Finset.mem_insert.mp h with h | h
      · exact ⟨1, h⟩
      · exact ⟨2, Finset.mem_singleton.mp h⟩
  refine ⟨k, fun z hzy hz => ?_⟩
  by_cases hj : ∀ j, z ≠ vn j
  · exact absurd (hdead z hzy hj k k) hz
  · push_neg at hj
    obtain ⟨j, hjz⟩ := hj
    by_cases hjk : j = k
    · rw [hjz, hjk, hk]
    · exact absurd (by rw [hjz]; exact hdiagv j k k (Or.inl fun h => hjk h.symm)) hz

/-- **Excess degree cannot sit alone.**  A site with four live partners has a live partner
that also has four.  Otherwise every one of its blocks is a single diagonal entry, and four
blocks in three colours must repeat a colour; the two partners sharing it are then both left
with `u` as their only live partner in that colour, and no perfect matching in that colour can
match them both. -/
theorem exists_excess_neighbour (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u : V}
    (hu4 : 4 ≤ (LiveDegree.liveNbrs W u).card) :
    ∃ y ∈ LiveDegree.liveNbrs W u, 4 ≤ (LiveDegree.liveNbrs W y).card := by
  classical
  by_contra hall
  push_neg at hall
  have hcolour : ∀ y : V, ∃ k : Fin 3, y ∈ LiveDegree.liveNbrs W u →
      ∀ z : V, z ≠ y → W s((y, k), (z, k)) ≠ 0 → z = u := by
    intro y
    by_cases hy : y ∈ LiveDegree.liveNbrs W u
    · obtain ⟨hyu, a, b, hab⟩ := LiveDegree.mem_liveNbrs.mp hy
      obtain ⟨k, hk⟩ := unique_colour_partner_of_deg_three W hone hzero hcard hyu ⟨a, b, hab⟩
        (by have := hall y hy; omega)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose kf hkf using hcolour
  obtain ⟨y, hy, y', hy', hyy', hsame⟩ :
      ∃ y ∈ LiveDegree.liveNbrs W u, ∃ y' ∈ LiveDegree.liveNbrs W u,
        y ≠ y' ∧ kf y = kf y' := by
    refine Finset.exists_ne_map_eq_of_card_lt_of_maps_to ?_ (fun a _ => Finset.mem_univ (kf a))
    calc (Finset.univ : Finset (Fin 3)).card = 3 := by simp
      _ < 4 := by omega
      _ ≤ (LiveDegree.liveNbrs W u).card := hu4
  have hky : ∀ z : V, z ≠ y → W s((y, kf y), (z, kf y)) ≠ 0 → z = u := hkf y hy
  have hky' : ∀ z : V, z ≠ y' → W s((y', kf y), (z, kf y)) ≠ 0 → z = u := by
    rw [hsame]; exact hkf y' hy'
  refine hone (kf y) ?_
  rw [← pmSum_univ, pmSum]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  obtain ⟨-, hfix, -⟩ := mem_pairingsOn.mp hσ
  by_cases h : σ y = u
  · have hy'u : σ y' ≠ u := by
      intro h'
      exact hyy' (σ.injective (h.trans h'.symm))
    refine Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ y')) ?_
    by_contra hne'
    exact hy'u (hky' (σ y') (hfix y' (Finset.mem_univ y')) hne')
  · refine Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ y)) ?_
    by_contra hne'
    exact h (hky (σ y) (hfix y (Finset.mem_univ y)) hne')

/-! ### A three-regular named partner kills the certificate -/

/-- **A named partner of degree three destroys the certificate.**  Suppose the named blocks
at a site are single diagonal entries, and a colouring of the complement sends the
`α`-named partner to colour `α`.  If that partner is three-regular, its only live partner in
colour `α` is the site itself --- which the complement excludes.  So it can be matched to
nothing, and the complement's matching sum vanishes.

Read against the pinning, this says: in the hard case every named partner of a live row of the
extra block carries excess degree. -/
theorem certificate_zero_of_named_deg_three (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u) (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hfanlive : ∀ j : Fin 3, ∃ a : Fin 3, W s((u, a), (wn j, j)) ≠ 0)
    (α : Fin 3) (h3 : (LiveDegree.liveNbrs W (wn α)).card ≤ 3)
    (c : V → Fin 3) (hcα : c (wn α) = α) :
    pmSum W c ((Finset.univ.erase u).erase v) = 0 := by
  classical
  obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
    structure_of_deg_three W hone hzero hcard h3
  -- the edge back to `u` is `wn α`'s colour-`α` edge
  have huα : W s((u, α), (wn α, α)) ≠ 0 := by
    obtain ⟨a, ha⟩ := hfanlive α
    by_cases haα : a = α
    · rwa [haα] at ha
    · exact absurd (hdiag α a α (Or.inl haα)) ha
  have huvn : u = vn α := by
    have hlive : W s((wn α, α), (u, α)) ≠ 0 := by rw [Sym2.eq_swap]; exact huα
    by_cases hj : ∀ j, u ≠ vn j
    · exact absurd (hdead u (fun h => hwu α h.symm) hj α α) hlive
    · push_neg at hj
      obtain ⟨j, hju⟩ := hj
      by_cases hjα : j = α
      · rw [hju, hjα]
      · exact absurd (by rw [hju]; exact hdiagv j α α (Or.inl fun h => hjα h.symm)) hlive
  -- expand at `wn α`: no partner is available
  have hmem : wn α ∈ (Finset.univ.erase u).erase v :=
    Finset.mem_erase.mpr ⟨fun h => hvw α h.symm, Finset.mem_erase.mpr ⟨hwu α, Finset.mem_univ _⟩⟩
  rw [pmSum_expand W c hmem]
  refine Finset.sum_eq_zero fun z hz => ?_
  have hzw : z ≠ wn α := (Finset.mem_erase.mp hz).1
  have hzu : z ≠ u := by
    have := Finset.mem_of_mem_erase hz
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase this)).1
  have hkill : W s((wn α, c (wn α)), (z, c z)) = 0 := by
    rw [hcα]
    by_cases hj : ∀ j, z ≠ vn j
    · exact hdead z hzw hj α (c z)
    · push_neg at hj
      obtain ⟨j, hjz⟩ := hj
      by_cases hjα : j = α
      · exact absurd (by rw [hjz, hjα, ← huvn]) hzu
      · rw [hjz]
        exact hdiagv j α (c (vn j)) (Or.inl fun h => hjα h.symm)
  have : W (Sym2.map (paint c) s(wn α, z)) = 0 := hkill
  rw [this, zero_mul]

/-! ### At most three three-regular neighbours -/

/-- Two distinct sites cannot share their unique live partner in one colour: a perfect
matching in that colour would have to send both to it. -/
theorem not_two_pendant_same (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    {u y y' : V} (hyy' : y ≠ y') (k : Fin 3)
    (hky : ∀ z : V, z ≠ y → W s((y, k), (z, k)) ≠ 0 → z = u)
    (hky' : ∀ z : V, z ≠ y' → W s((y', k), (z, k)) ≠ 0 → z = u) : False := by
  classical
  refine hone k ?_
  rw [← pmSum_univ, pmSum]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  obtain ⟨-, hfix, -⟩ := mem_pairingsOn.mp hσ
  by_cases h : σ y = u
  · have hy'u : σ y' ≠ u := by
      intro h'
      exact hyy' (σ.injective (h.trans h'.symm))
    refine Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ y')) ?_
    by_contra hne'
    exact hy'u (hky' (σ y') (hfix y' (Finset.mem_univ y')) hne')
  · refine Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ y)) ?_
    by_contra hne'
    exact h (hky (σ y) (hfix y (Finset.mem_univ y)) hne')

/-- **At most three three-regular neighbours.**  A site's three-regular live partners occupy
distinct colours, so there are at most three of them --- and a site of degree `d` therefore
has at least `d - 3` partners of excess degree. -/
theorem three_regular_nbrs_card_le (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) (u : V) :
    ((LiveDegree.liveNbrs W u).filter
      (fun y => (LiveDegree.liveNbrs W y).card ≤ 3)).card ≤ 3 := by
  classical
  set F := (LiveDegree.liveNbrs W u).filter
    (fun y => (LiveDegree.liveNbrs W y).card ≤ 3) with hF
  have hcol : ∀ y ∈ F, ∃ k : Fin 3, ∀ z : V, z ≠ y → W s((y, k), (z, k)) ≠ 0 → z = u := by
    intro y hy
    rw [hF, Finset.mem_filter] at hy
    obtain ⟨hyu, a, b, hab⟩ := LiveDegree.mem_liveNbrs.mp hy.1
    exact unique_colour_partner_of_deg_three W hone hzero hcard hyu ⟨a, b, hab⟩ hy.2
  choose! kf hkf using hcol
  have hinj : Set.InjOn kf F := by
    intro y hy y' hy' hkk
    by_contra hyy'
    exact not_two_pendant_same W hone hyy' (kf y) (hkf y hy)
      (by rw [hkk]; exact hkf y' hy')
  calc F.card = (F.image kf).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 3 := by simp

/-! ### Every two-colour component carries excess -/

/-- **A two-colour closed set must contain a site of excess degree.**  If every site of the
set were three-regular, its blocks would be single diagonal entries, so no edge could leave it
carrying one colour inside and another outside --- and then the two-colour closure theorem
applies.

Taking the set to be a connected component of the union of two colour graphs: every such
component meets the sites of excess degree. In particular a cycle alternating two colours
inside the three-regular part is impossible. -/
theorem exists_excess_in_two_colour_closed (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V)
    (C : Finset V) (hCne : C.Nonempty) (hCc : (Finset.univ \ C).Nonempty)
    {k l : Fin 3} (hkl : k ≠ l)
    (hcutk : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, k), (y, k)) = 0)
    (hcutl : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, l), (y, l)) = 0) :
    ∃ x ∈ C, 4 ≤ (LiveDegree.liveNbrs W x).card := by
  classical
  by_contra hall
  push_neg at hall
  refine Separation.no_two_colour_closed W hone hzero C hCne hCc hkl hcutk hcutl ?_
  intro x hx y hy
  have hx3 : (LiveDegree.liveNbrs W x).card ≤ 3 := by
    have := hall x hx
    omega
  obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
    structure_of_deg_three W hone hzero hcard hx3
  have hyx : y ≠ x := by
    intro h
    exact (Finset.mem_sdiff.mp hy).2 (h ▸ hx)
  by_cases hj : ∀ j, y ≠ vn j
  · exact hdead y hyx hj l k
  · push_neg at hj
    obtain ⟨j, hjy⟩ := hj
    rw [hjy]
    by_cases hjl : j = l
    · exact hdiagv j l k (Or.inr fun h => hkl ((h.trans hjl)))
    · exact hdiagv j l k (Or.inl fun h => hjl h.symm)

/-- **Excess degree comes in pairs.**  If any site has a fourth live partner, at least two
sites do. -/
theorem two_excess_of_excess (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {u : V}
    (hu4 : 4 ≤ (LiveDegree.liveNbrs W u).card) :
    ∃ y : V, y ≠ u ∧ 4 ≤ (LiveDegree.liveNbrs W y).card := by
  obtain ⟨y, hy, hy4⟩ := exists_excess_neighbour W hone hzero hcard hu4
  exact ⟨y, (LiveDegree.mem_liveNbrs.mp hy).1, hy4⟩

/-- **Two colours cannot share a partner at a three-regular site.**  A site of degree three
has single diagonal entries for blocks, so each partner carries exactly one colour.  A site
joined to the same partner by live edges in two colours therefore has excess degree.

In matching terms: if two colour matchings agree on an edge, both its endpoints carry excess
degree.  The doubled edges of any two colours live entirely inside the excess subgraph, and
every three-regular site lies on an alternating cycle of the two. -/
theorem excess_of_two_colours_same_partner (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {x y : V} (hxy : y ≠ x)
    {k l : Fin 3} (hkl : k ≠ l)
    (hk : W s((x, k), (y, k)) ≠ 0) (hl : W s((x, l), (y, l)) ≠ 0) :
    4 ≤ (LiveDegree.liveNbrs W x).card := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
    structure_of_deg_three W hone hzero hcard (by omega : (LiveDegree.liveNbrs W x).card ≤ 3)
  -- `y` must be one of the named partners
  obtain ⟨j, hjy⟩ : ∃ j : Fin 3, y = vn j := by
    by_contra hno
    push_neg at hno
    exact hk (hdead y hxy hno k k)
  -- and its colour is forced twice over
  have hjk : j = k := by
    by_contra hjk
    exact hk (by rw [hjy]; exact hdiagv j k k (Or.inl fun h' => hjk h'.symm))
  have hjl : j = l := by
    by_contra hjl
    exact hl (by rw [hjy]; exact hdiagv j l l (Or.inl fun h' => hjl h'.symm))
  exact hkl (hjk.symm.trans hjl)

/-- **A three-regular site has exactly one live partner per colour, and they are distinct.**
This is the whole colour structure at such a site, packaged: the three colour matchings meet
it in three different places, so their pairwise unions decompose the three-regular part into
alternating cycles with no doubled edges. -/
theorem colour_partner_of_deg_three (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V) {x : V}
    (h3 : (LiveDegree.liveNbrs W x).card ≤ 3) :
    ∃ p : Fin 3 → V, Function.Injective p ∧ (∀ k, p k ≠ x) ∧
      (∀ k : Fin 3, W s((x, k), (p k, k)) ≠ 0) ∧
      (∀ (k : Fin 3) (z : V), z ≠ x → W s((x, k), (z, k)) ≠ 0 → z = p k) := by
  classical
  obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
    structure_of_deg_three W hone hzero hcard h3
  refine ⟨vn, hinj, hne, ?_, ?_⟩
  · intro k
    have hmem : vn k ∈ LiveDegree.liveNbrs W x := by
      rw [heq]
      fin_cases k
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _))
    obtain ⟨-, a, b, hab⟩ := LiveDegree.mem_liveNbrs.mp hmem
    by_cases hak : a = k
    · by_cases hbk : b = k
      · rwa [hak, hbk] at hab
      · exact absurd (hdiagv k a b (Or.inr hbk)) hab
    · exact absurd (hdiagv k a b (Or.inl hak)) hab
  · intro k z hzx hz
    by_cases hj : ∀ j, z ≠ vn j
    · exact absurd (hdead z hzx hj k k) hz
    · push_neg at hj
      obtain ⟨j, hjz⟩ := hj
      by_cases hjk : j = k
      · rw [hjz, hjk]
      · exact absurd (by rw [hjz]; exact hdiagv j k k (Or.inl fun h => hjk h.symm)) hz

/-- **The mixed crossing edge starts at an excess site.**  A two-colour closed proper set has a
live edge leaving it that carries one of the two colours inside and the other outside; and
that edge cannot start at a three-regular site, whose blocks are single diagonal entries.

So the boundary of any two-colour closed set is carried by sites of excess degree, and those
sites have mixed blocks --- dead on the diagonal in both colours, live off it. -/
theorem exists_excess_mixed_crossing (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V)
    (C : Finset V) (hCne : C.Nonempty) (hCc : (Finset.univ \ C).Nonempty)
    {k l : Fin 3} (hkl : k ≠ l)
    (hcutk : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, k), (y, k)) = 0)
    (hcutl : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, l), (y, l)) = 0) :
    ∃ x ∈ C, 4 ≤ (LiveDegree.liveNbrs W x).card
      ∧ ∃ y ∈ Finset.univ \ C, W s((x, l), (y, k)) ≠ 0 := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Separation.exists_mixed_crossing W hone hzero C hCne hCc hkl hcutk hcutl
  refine ⟨x, hx, ?_, y, hy, hxy⟩
  by_contra h
  push_neg at h
  obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
    structure_of_deg_three W hone hzero hcard (by omega : (LiveDegree.liveNbrs W x).card ≤ 3)
  have hyx : y ≠ x := fun h' => (Finset.mem_sdiff.mp hy).2 (h' ▸ hx)
  by_cases hj : ∀ j, y ≠ vn j
  · exact hxy (hdead y hyx hj l k)
  · push_neg at hj
    obtain ⟨j, hjy⟩ := hj
    by_cases hjl : j = l
    · exact hxy (by rw [hjy]; exact hdiagv j l k (Or.inr fun h' => hkl (h'.trans hjl)))
    · exact hxy (by rw [hjy]; exact hdiagv j l k (Or.inl fun h' => hjl h'.symm))

/-! ### A site cannot have all three named partners three-regular -/

/-- If a site of a set has no live partner of a colour inside that set, the colour's matching
sum over the set vanishes: it can be matched to nothing. -/
theorem pmSum_const_zero_of_no_partner (W : Sym2 (V × Fin 3) → ℂ)
    {t : V} (k : Fin 3) (S : Finset V) (htS : t ∈ S)
    (hout : ∀ z ∈ S, z ≠ t → W s((t, k), (z, k)) = 0) :
    pmSum W (Amplitude.const (V := V) k) S = 0 := by
  classical
  rw [pmSum_expand W _ htS]
  refine Finset.sum_eq_zero fun z hz => ?_
  have : W (Sym2.map (paint (Amplitude.const (V := V) k)) s(t, z)) = W s((t, k), (z, k)) := rfl
  rw [this, hout z (Finset.mem_of_mem_erase hz) (Finset.mem_erase.mp hz).1, zero_mul]

/-- **A site with one extra partner cannot have all three named partners three-regular.**

If they were, each would have this site as its unique live partner in its own colour, so the
complementary sums with the extra would vanish in every colour --- and then support minimality
still forces a surviving colouring, whose pinning puts a live row's named partner on its own
colour, which is exactly what a three-regular named partner cannot survive. -/
theorem not_all_named_three_regular (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W) (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hfanlive : ∀ j : Fin 3, ∃ a : Fin 3, W s((u, a), (wn j, j)) ≠ 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0)
    (h3 : ∀ j : Fin 3, (LiveDegree.liveNbrs W (wn j)).card ≤ 3) : False := by
  classical
  obtain ⟨hone, hzero⟩ := hmin.1
  -- each named partner's unique colour-`j` live partner is `u`
  have hunique : ∀ j : Fin 3, ∀ z : V, z ≠ wn j → W s((wn j, j), (z, j)) ≠ 0 → z = u := by
    intro j z hzw hz
    obtain ⟨vn, hinj, hne, hdiagv, hdead, heq⟩ :=
      structure_of_deg_three W hone hzero hcard (h3 j)
    obtain ⟨a, ha⟩ := hfanlive j
    have hua : W s((wn j, j), (u, a)) ≠ 0 := by rw [Sym2.eq_swap]; exact ha
    obtain ⟨m, hm⟩ : ∃ m : Fin 3, u = vn m := by
      by_contra hno
      push_neg at hno
      exact hua (hdead u (fun h => hwu j h.symm) hno j a)
    have hmj : m = j := by
      by_contra hmj
      exact hua (by rw [hm]; exact hdiagv m j a (Or.inl fun h => hmj h.symm))
    obtain ⟨m', hm'⟩ : ∃ m' : Fin 3, z = vn m' := by
      by_contra hno
      push_neg at hno
      exact hz (hdead z hzw hno j j)
    have hm'j : m' = j := by
      by_contra hm'j
      exact hz (by rw [hm']; exact hdiagv m' j j (Or.inl fun h => hm'j h.symm))
    rw [hm', hm'j, ← hmj, ← hm]
  -- so every complementary constant sum vanishes
  have hdegen : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0 := by
    intro k
    refine pmSum_const_zero_of_no_partner W k _
      (Finset.mem_erase.mpr ⟨fun h => hvw k h.symm,
        Finset.mem_erase.mpr ⟨hwu k, Finset.mem_univ _⟩⟩) ?_
    intro z hz hzw
    by_contra hne
    have := hunique k z hzw hne
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1 this
  -- minimality still supplies a certificate, and it pins a live row
  obtain ⟨c, hc, hpin⟩ :=
    certificate_pins W hmin hvu wn hwu hvw hcol hlone hlive hdegen
  obtain ⟨a, b, hab⟩ := hlive
  have hca : c (wn a) = a := hpin a b hab
  -- but a three-regular named partner destroys it
  have hdiag : ∀ j a' b' : Fin 3, (a' ≠ j ∨ b' ≠ j) → W s((u, a'), (wn j, b')) = 0 := by
    intro j a' b' hab'
    rcases hab' with ha' | hb'
    · by_cases hbj : b' = j
      · rw [hbj]
        exact diag_of_complement_zero W hone hzero hvu wn hwu hvw hcol hlone j
          (hdegen j) a' ha'
      · exact hcol j a' b' hbj
    · exact hcol j a' b' hb'
  exact hc (certificate_zero_of_named_deg_three W hone hzero hcard hvu wn hwu hvw hdiag
    hfanlive a (h3 a) c hca)

/-- **In the all-degenerate case every live row's named partner carries excess.**  This is the
general form behind the previous theorem: with all complementary constant sums vanishing, the
certificate forced by minimality pins a live row's named partner to that row's colour, and a
three-regular partner cannot survive being pinned there. -/
theorem excess_of_live_row_named (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W) (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hfanlive : ∀ j : Fin 3, ∃ a : Fin 3, W s((u, a), (wn j, j)) ≠ 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (hdegen : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0)
    {a b : Fin 3} (hab : W s((u, a), (v, b)) ≠ 0) :
    4 ≤ (LiveDegree.liveNbrs W (wn a)).card := by
  classical
  obtain ⟨hone, hzero⟩ := hmin.1
  by_contra h
  push_neg at h
  obtain ⟨c, hc, hpin⟩ :=
    certificate_pins W hmin hvu wn hwu hvw hcol hlone ⟨a, b, hab⟩ hdegen
  have hdiag : ∀ j a' b' : Fin 3, (a' ≠ j ∨ b' ≠ j) → W s((u, a'), (wn j, b')) = 0 := by
    intro j a' b' hab'
    rcases hab' with ha' | hb'
    · by_cases hbj : b' = j
      · rw [hbj]
        exact diag_of_complement_zero W hone hzero hvu wn hwu hvw hcol hlone j
          (hdegen j) a' ha'
      · exact hcol j a' b' hbj
    · exact hcol j a' b' hb'
  exact hc (certificate_zero_of_named_deg_three W hone hzero hcard hvu wn hwu hvw hdiag
    hfanlive a (by omega) c (hpin a b hab))

/-- **Two excess neighbours in the all-degenerate case.**  Both the extra and the named partner
of any live row of its block carry excess degree, and they are distinct.  So a site carrying an
all-degenerate extra has at least two neighbours of excess degree: the excess subgraph has no
pendant attachment at such a site. -/
theorem two_excess_neighbours_of_all_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hmin : IsSupportMinimal W) (hcard : 4 < Fintype.card V)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hfanlive : ∀ j : Fin 3, ∃ a : Fin 3, W s((u, a), (wn j, j)) ≠ 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (hdegen : ∀ k : Fin 3,
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0)
    {a b : Fin 3} (hab : W s((u, a), (v, b)) ≠ 0) :
    ∃ y z : V, y ≠ z ∧ y ∈ LiveDegree.liveNbrs W u ∧ z ∈ LiveDegree.liveNbrs W u
      ∧ 4 ≤ (LiveDegree.liveNbrs W y).card ∧ 4 ≤ (LiveDegree.liveNbrs W z).card := by
  classical
  obtain ⟨hone, hzero⟩ := hmin.1
  have hv4 : 4 ≤ (LiveDegree.liveNbrs W v).card :=
    four_live_at_degenerate_end W hone hzero hcard hvu ⟨a, b, hab⟩ hdegen
  have hw4 : 4 ≤ (LiveDegree.liveNbrs W (wn a)).card :=
    excess_of_live_row_named W hmin hcard hvu wn hwu hvw hcol hfanlive hlone hdegen hab
  refine ⟨v, wn a, fun h => hvw a h, ?_, ?_, hv4, hw4⟩
  · exact LiveDegree.mem_liveNbrs.mpr ⟨hvu, a, b, hab⟩
  · obtain ⟨a', ha'⟩ := hfanlive a
    exact LiveDegree.mem_liveNbrs.mpr ⟨hwu a, a', a, ha'⟩

end HardCase
