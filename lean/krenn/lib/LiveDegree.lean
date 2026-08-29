import Mathlib
import Amplitude
import MatchingSum
import PurePartner
import Mettapedia.Combinatorics.Matching.Loopless
import Mettapedia.Combinatorics.Matching.Support

/-!
# The remaining hypothesis is about degree

The column fan gives every site three live partners, one supported in each colour, and they
are distinct.  So three-regularity is not a statement about colour structure at all: it says
only that no site has a *fourth* live partner.

This file makes that exact.  With loop weights normalised away — they appear in no matching
and so in no amplitude — a bound of three on the live degree at every site produces the
three-regular structure outright.
-/

namespace LiveDegree

open Amplitude MatchingSum MatchingLoopless MatchingSupport

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The live partners of a site. -/
noncomputable def liveNbrs (W : Sym2 (V × Fin 3) → ℂ) (u : V) : Finset V :=
  MatchingSupport.liveNeighbours W u

lemma mem_liveNbrs {W : Sym2 (V × Fin 3) → ℂ} {u y : V} :
    y ∈ liveNbrs W u ↔ y ≠ u ∧ ∃ a b : Fin 3, W s((u, a), (y, b)) ≠ 0 :=
  MatchingSupport.mem_liveNeighbours

/-- **Degree three is three-regularity.**  A site with no fourth live partner has exactly the
three the fan names, and the whole structure follows. -/
theorem threeRegular_of_liveDegree (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hcard : 4 < Fintype.card V)
    (hloop : ∀ (x : V) (a b : Fin 3), W s((x, a), (x, b)) = 0)
    (hdeg : ∀ u : V, (liveNbrs W u).card ≤ 3) :
    Nonempty (PurePartner.ThreeRegular W) := by
  classical
  have hu2 : ∀ u : V, 2 ≤ (Finset.univ.erase u).card := by
    intro u
    rw [Finset.card_erase_of_mem (Finset.mem_univ u)]
    have : (Finset.univ : Finset V).card = Fintype.card V := rfl
    omega
  choose wn hinj hne hcol hlive using
    fun u : V => PurePartner.exists_column_fan W hone hzero (hu2 u)
  have hsub : ∀ u : V, ({wn u 0, wn u 1, wn u 2} : Finset V) ⊆ liveNbrs W u := by
    intro u z hz
    have hmem : ∃ k : Fin 3, z = wn u k := by
      rcases Finset.mem_insert.mp hz with h | h
      · exact ⟨0, h⟩
      · rcases Finset.mem_insert.mp h with h | h
        · exact ⟨1, h⟩
        · exact ⟨2, Finset.mem_singleton.mp h⟩
    obtain ⟨k, rfl⟩ := hmem
    obtain ⟨a, ha⟩ := hlive u k
    exact mem_liveNbrs.mpr ⟨hne u k, a, k, ha⟩
  have hcard3 : ∀ u : V, ({wn u 0, wn u 1, wn u 2} : Finset V).card = 3 := by
    intro u
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => absurd (hinj u h) (by decide)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (hinj u h) (by decide), fun h => absurd (hinj u h) (by decide)⟩
  have heq : ∀ u : V, liveNbrs W u = {wn u 0, wn u 1, wn u 2} := by
    intro u
    exact (Finset.eq_of_subset_of_card_le (hsub u) (by rw [hcard3 u]; exact hdeg u)).symm
  refine ⟨{ partner := wn
            ne_self := hne
            no_loop := hloop
            col := fun x k a b hb => hcol x k a b hb
            live := hlive
            dead := ?_ }⟩
  intro x y hyx hnp a b
  by_contra hne'
  have hmem : y ∈ liveNbrs W x := mem_liveNbrs.mpr ⟨hyx, a, b, hne'⟩
  rw [heq x] at hmem
  rcases Finset.mem_insert.mp hmem with h | h
  · exact hnp 0 h
  · rcases Finset.mem_insert.mp h with h | h
    · exact hnp 1 h
    · exact hnp 2 (Finset.mem_singleton.mp h)

/-- Loop weights appear in no matching, so changing them changes no amplitude. -/
theorem amplitude_ignore_loops (W W' : Sym2 (V × Fin 3) → ℂ)
    (h : ∀ (x y : V) (a b : Fin 3), x ≠ y → W' s((x, a), (y, b)) = W s((x, a), (y, b)))
    (c : V → Fin 3) : amplitude W' c = amplitude W c :=
  MatchingLoopless.amplitude_ignore_loops W W' h c

/-- The loop-free normalisation of a weighting. -/
noncomputable def deloop (W : Sym2 (V × Fin 3) → ℂ) : Sym2 (V × Fin 3) → ℂ :=
  MatchingLoopless.deloop W

omit [Fintype V] in
lemma deloop_off {W : Sym2 (V × Fin 3) → ℂ} {x y : V} (hxy : x ≠ y) (a b : Fin 3) :
    deloop W s((x, a), (y, b)) = W s((x, a), (y, b)) :=
  MatchingLoopless.deloop_off hxy a b

omit [Fintype V] in
lemma deloop_loop (W : Sym2 (V × Fin 3) → ℂ) (x : V) (a b : Fin 3) :
    deloop W s((x, a), (x, b)) = 0 :=
  MatchingLoopless.deloop_loop W x a b

lemma amplitude_deloop (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) :
    amplitude (deloop W) c = amplitude W c :=
  MatchingLoopless.amplitude_deloop W c

lemma liveNbrs_deloop (W : Sym2 (V × Fin 3) → ℂ) (u : V) :
    liveNbrs (deloop W) u = liveNbrs W u :=
  MatchingSupport.liveNeighbours_deloop W u

end LiveDegree
