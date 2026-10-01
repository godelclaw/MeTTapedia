import Mettapedia.GraphTheory.OrderedBoundaryColouring
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.IntervalCases

/-!
# Finite path selection for coupled three-colour extension

The path keeps two initial neighbours and their common closing vertex.
Maximality is constructed from the finite vertex bound, not supplied as
a colouring certificate. This is the path-selection part of M. Zając,
*A short proof of Brooks' theorem* (2018), arXiv:1805.11176.
-/

namespace Mettapedia.GraphTheory.SubcubicPathSelection

open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Only the first `n` values are path vertices. Natural indices make
the two path-colouring directions and their junction explicit. -/
structure StartedPath (a r b : V) (n : ℕ) where
  vertex : ℕ → V
  three_le : 3 ≤ n
  injective : ∀ i j, i < n → j < n → vertex i = vertex j → i = j
  step : ∀ i, i + 1 < n → G.Adj (vertex i) (vertex (i + 1))
  first : vertex 0 = a
  second : vertex 1 = r
  third : vertex 2 = b

namespace StartedPath

variable {G} {a r b : V} {n : ℕ}

theorem length_le (p : StartedPath G a r b n) : n ≤ Fintype.card V := by
  have h := Fintype.card_le_of_injective (fun i : Fin n => p.vertex i.val) (by
    intro i j he
    exact Fin.ext (p.injective i.val j.val i.isLt j.isLt he))
  simpa using h

def seed (hab : a ≠ b) (har : G.Adj r a) (hbr : G.Adj r b) :
    StartedPath G a r b 3 where
  vertex i := if i = 0 then a else if i = 1 then r else b
  three_le := le_rfl
  injective := by
    intro i j hi hj he
    have hai : a ≠ r := har.ne.symm
    have hbi : b ≠ r := hbr.ne.symm
    interval_cases i <;> interval_cases j <;> simp_all
  step := by
    intro i hi
    have hi' : i ≤ 1 := by omega
    interval_cases i
    · simpa using har.symm
    · simpa using hbr
  first := by simp
  second := by simp
  third := by simp

/-- Append an actual new neighbour of the endpoint. -/
def append (p : StartedPath G a r b n) (x : V)
    (hx : ∀ i, i < n → p.vertex i ≠ x)
    (ha : G.Adj (p.vertex (n - 1)) x) : StartedPath G a r b (n + 1) where
  vertex i := if i = n then x else p.vertex i
  three_le := p.three_le.trans (Nat.le_succ _)
  injective := by
    intro i j hi hj he
    by_cases hin : i = n <;> by_cases hjn : j = n
    · omega
    · simp only [hin, hjn, if_true, if_false] at he
      exact (hx j (by omega) he.symm).elim
    · simp only [hin, hjn, if_true, if_false] at he
      exact (hx i (by omega) he).elim
    · simp only [hin, hjn, if_false] at he
      exact p.injective i j (by omega) (by omega) he
  step := by
    intro i hi
    have hin : i ≠ n := by omega
    by_cases hjn : i + 1 = n
    · have hi' : i = n - 1 := by omega
      rw [if_neg hin, if_pos hjn]
      simpa only [hi'] using ha
    · simpa [hin, hjn] using p.step i (by omega)
  first := by have := p.three_le; simpa [show 0 ≠ n by omega] using p.first
  second := by have := p.three_le; simpa [show 1 ≠ n by omega] using p.second
  third := by have := p.three_le; simpa [show 2 ≠ n by omega] using p.third

def vertices (p : StartedPath G a r b n) : Finset V := (Finset.range n).image p.vertex

theorem mem_vertices (p : StartedPath G a r b n) (v : V) :
    v ∈ p.vertices ↔ ∃ i, i < n ∧ p.vertex i = v := by
  simp [vertices]

theorem vertices_card (p : StartedPath G a r b n) : p.vertices.card = n := by
  rw [vertices, Finset.card_image_of_injOn]
  · exact Finset.card_range n
  · intro i hi j hj he
    exact p.injective i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) he

def indexEquiv (p : StartedPath G a r b n) (hcover : ∀ v, v ∈ p.vertices) : Fin n ≃ V :=
  Equiv.ofBijective (fun i => p.vertex i.val) ⟨by
    intro i j he
    exact Fin.ext (p.injective _ _ i.isLt j.isLt he), by
    intro v
    obtain ⟨i, hi, he⟩ := (p.mem_vertices v).mp (hcover v)
    exact ⟨⟨i, hi⟩, he⟩⟩

end StartedPath

/-- A maximal started path exists and its endpoint has no neighbour
outside the path. No global connectivity assumption is needed. -/
theorem exists_maximal {a r b : V} (hab : a ≠ b)
    (har : G.Adj r a) (hbr : G.Adj r b) :
    ∃ n, ∃ p : StartedPath G a r b n,
      ∀ w, G.Adj (p.vertex (n - 1)) w → w ∈ p.vertices := by
  classical
  let P : ℕ → Prop := fun n => Nonempty (StartedPath G a r b n)
  let s := StartedPath.seed hab har hbr
  have hs : P 3 := ⟨s⟩
  have hbnd : 3 ≤ Fintype.card V := s.length_le
  let n := Nat.findGreatest P (Fintype.card V)
  obtain ⟨p⟩ := Nat.findGreatest_spec hbnd hs
  refine ⟨n, p, ?_⟩
  intro w hw
  by_contra hnot
  have hx : ∀ i, i < n → p.vertex i ≠ w := by
    intro i hi he
    exact hnot ((p.mem_vertices w).mpr ⟨i, hi, he⟩)
  let p' := p.append w hx hw
  have hmax : n + 1 ≤ n := Nat.le_findGreatest p'.length_le (show P (n + 1) from ⟨p'⟩)
  omega

/-- The full-path ordering retains the shared initial choice and closes
at the common neighbour after two opposite insertion directions. -/
def fullPathOrder {a r b : V} {n j : ℕ} (p : StartedPath G a r b n)
    (hcover : ∀ v, v ∈ p.vertices) (hj : 3 ≤ j) (hjn : j < n)
    (hrj : G.Adj r (p.vertex j)) : CoupledThreeColouring.CoupledOrder G a b r := by
  classical
  let e := p.indexEquiv hcover
  let f : ℕ → ℕ := fun i =>
    if i = 0 then 0 else if i = 2 then 1 else if i = 1 then n - 1
    else if i < j then i - 1 else n - i + j - 2
  have hzero : e ⟨0, by omega⟩ = a := p.first
  have hone : e ⟨1, by omega⟩ = r := p.second
  have htwo : e ⟨2, by omega⟩ = b := p.third
  have hidx0 : (e.symm a).val = 0 := by rw [← hzero]; simp
  have hidx1 : (e.symm r).val = 1 := by rw [← hone]; simp
  have hidx2 : (e.symm b).val = 2 := by rw [← htwo]; simp
  refine ⟨fun v => f (e.symm v).val, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y he
    apply e.symm.injective
    apply Fin.ext
    have hx := (e.symm x).isLt
    have hy := (e.symm y).isLt
    simp only [f] at he
    split_ifs at he <;> first | contradiction | omega
  · simp [f, hidx0]
  · simp [f, hidx2]
  · intro v hva hvb
    have hi0 : (e.symm v).val ≠ 0 := by
      intro he
      apply hva
      exact e.symm.injective (Fin.ext (he.trans hidx0.symm))
    have hi2 : (e.symm v).val ≠ 2 := by
      intro he
      apply hvb
      exact e.symm.injective (Fin.ext (he.trans hidx2.symm))
    have hi := (e.symm v).isLt
    simp only [f]
    split_ifs <;> first | contradiction | omega
  · intro v hva hvb hvr
    let i := (e.symm v).val
    have hin : i < n := (e.symm v).isLt
    have hi : 3 ≤ i := by
      have hi0 : i ≠ 0 := fun he => hva (e.symm.injective (Fin.ext (he.trans hidx0.symm)))
      have hi1 : i ≠ 1 := fun he => hvr (e.symm.injective (Fin.ext (he.trans hidx1.symm)))
      have hi2 : i ≠ 2 := fun he => hvb (e.symm.injective (Fin.ext (he.trans hidx2.symm)))
      omega
    have hev : p.vertex i = v := e.apply_symm_apply v
    have index : ∀ k (hk : k < n), (e.symm (p.vertex k)).val = k := by
      intro k hk
      exact congrArg Fin.val (e.symm_apply_apply ⟨k, hk⟩)
    by_cases hij : i < j
    · refine ⟨p.vertex (i + 1), ?_, ?_⟩
      · simpa [hev] using p.step i (by omega)
      · rw [index (i + 1) (by omega)]
        change f i < f (i + 1)
        clear_value i
        simp only [f]; split_ifs <;> first | contradiction | omega
    · by_cases heq : i = j
      · refine ⟨r, ?_, ?_⟩
        · simpa [← hev, heq] using hrj.symm
        · rw [hidx1]
          change f i < f 1
          clear_value i
          simp only [f]; split_ifs <;> first | contradiction | omega
      · refine ⟨p.vertex (i - 1), ?_, ?_⟩
        · have hstep := p.step (i - 1) (by omega)
          have hsub : i - 1 + 1 = i := by omega
          simpa [hsub, hev] using hstep.symm
        · rw [index (i - 1) (by omega)]
          change f i < f (i - 1)
          clear_value i
          simp only [f]; split_ifs <;> first | contradiction | omega

end
end Mettapedia.GraphTheory.SubcubicPathSelection
