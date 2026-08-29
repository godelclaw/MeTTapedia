import KrennRank
import OfficialKrennDefinitions

open SimpleGraph

namespace Krenn.OfficialBridge

open MonochromaticQuantumGraph

def restrictOfficial (W : WeightsN 6 3 ℂ) : WeightSystem K6 3 :=
  fun e i j => W (MonochromaticQuantumGraph.mkEdge
    (e : Sym2 (Fin 6)).inf (e : Sym2 (Fin 6)).sup i j)

def edge (u v : Fin 6) (h : u ≠ v) : K6.edgeSet :=
  ⟨s(u, v), by simpa using h⟩

def matchingList : List (Finset K6.edgeSet) :=
  [ {edge 0 1 (by decide), edge 2 3 (by decide), edge 4 5 (by decide)},
    {edge 0 1 (by decide), edge 2 4 (by decide), edge 3 5 (by decide)},
    {edge 0 1 (by decide), edge 2 5 (by decide), edge 3 4 (by decide)},
    {edge 0 2 (by decide), edge 1 3 (by decide), edge 4 5 (by decide)},
    {edge 0 2 (by decide), edge 1 4 (by decide), edge 3 5 (by decide)},
    {edge 0 2 (by decide), edge 1 5 (by decide), edge 3 4 (by decide)},
    {edge 0 3 (by decide), edge 1 2 (by decide), edge 4 5 (by decide)},
    {edge 0 3 (by decide), edge 1 4 (by decide), edge 2 5 (by decide)},
    {edge 0 3 (by decide), edge 1 5 (by decide), edge 2 4 (by decide)},
    {edge 0 4 (by decide), edge 1 2 (by decide), edge 3 5 (by decide)},
    {edge 0 4 (by decide), edge 1 3 (by decide), edge 2 5 (by decide)},
    {edge 0 4 (by decide), edge 1 5 (by decide), edge 2 3 (by decide)},
    {edge 0 5 (by decide), edge 1 2 (by decide), edge 3 4 (by decide)},
    {edge 0 5 (by decide), edge 1 3 (by decide), edge 2 4 (by decide)},
    {edge 0 5 (by decide), edge 1 4 (by decide), edge 2 3 (by decide)} ]

def allPMs : Finset (Finset K6.edgeSet) := matchingList.toFinset

set_option maxRecDepth 100000 in
theorem matchingList_nodup : matchingList.Nodup := by
  decide

local instance (M : Finset K6.edgeSet) : Decidable (IsPMFinset K6 M) :=
  decidableIsPMFinset M

theorem exists_outside1 (e₀ : K6.edgeSet) :
    ∃ v : Fin 6, v ∉ (e₀ : Sym2 (Fin 6)) := by
  revert e₀; decide

theorem exists_outside2 (e₀ e₁ : K6.edgeSet) :
    ∃ w : Fin 6, w ∉ (e₀ : Sym2 (Fin 6)) ∧ w ∉ (e₁ : Sym2 (Fin 6)) := by
  revert e₁ e₀; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem covers_or_shares (e₀ e₁ e₂ : K6.edgeSet) :
    (∀ v : Fin 6, v ∈ (e₀ : Sym2 (Fin 6)) ∨ v ∈ (e₁ : Sym2 (Fin 6))
        ∨ v ∈ (e₂ : Sym2 (Fin 6)))
      ∨ (∃ x : Fin 6, x ∈ (e₀ : Sym2 (Fin 6)) ∧ x ∈ (e₁ : Sym2 (Fin 6)))
      ∨ (∃ x : Fin 6, x ∈ (e₀ : Sym2 (Fin 6)) ∧ x ∈ (e₂ : Sym2 (Fin 6)))
      ∨ (∃ x : Fin 6, x ∈ (e₁ : Sym2 (Fin 6)) ∧ x ∈ (e₂ : Sym2 (Fin 6))) := by
  revert e₂ e₁ e₀; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem triple_mem (e₀ e₁ e₂ : K6.edgeSet)
    (hcov : ∀ v : Fin 6, v ∈ (e₀ : Sym2 (Fin 6)) ∨ v ∈ (e₁ : Sym2 (Fin 6))
      ∨ v ∈ (e₂ : Sym2 (Fin 6))) :
    ({e₀, e₁, e₂} : Finset K6.edgeSet) ∈ allPMs := by
  revert hcov; revert e₂ e₁ e₀; decide

set_option maxRecDepth 100000 in
theorem mem_allPMs_isPM (M : Finset K6.edgeSet) (hM : M ∈ allPMs) :
    IsPMFinset K6 M := by
  simp only [allPMs, List.mem_toFinset, matchingList, List.mem_cons,
    List.not_mem_nil, or_false] at hM
  rcases hM with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

noncomputable def edgeAt {M : Finset K6.edgeSet} (h : IsPMFinset K6 M)
    (v : Fin 6) : K6.edgeSet := (h v).choose

theorem edgeAt_mem {M : Finset K6.edgeSet} (h : IsPMFinset K6 M) (v : Fin 6) :
    edgeAt h v ∈ M := (h v).choose_spec.1.1

theorem edgeAt_covers {M : Finset K6.edgeSet} (h : IsPMFinset K6 M) (v : Fin 6) :
    v ∈ ((edgeAt h v : K6.edgeSet) : Sym2 (Fin 6)) := (h v).choose_spec.1.2

theorem eq_edgeAt {M : Finset K6.edgeSet} (h : IsPMFinset K6 M) (v : Fin 6)
    (g : K6.edgeSet) (hg : g ∈ M) (hgv : v ∈ (g : Sym2 (Fin 6))) :
    g = edgeAt h v := (h v).choose_spec.2 g ⟨hg, hgv⟩

theorem eq_of_shared {M : Finset K6.edgeSet} (h : IsPMFinset K6 M)
    (g g' : K6.edgeSet) (hg : g ∈ M) (hg' : g' ∈ M) (x : Fin 6)
    (hx : x ∈ (g : Sym2 (Fin 6))) (hx' : x ∈ (g' : Sym2 (Fin 6))) : g = g' := by
  rw [eq_edgeAt h x g hg hx, eq_edgeAt h x g' hg' hx']

theorem pm_eq_triple {M : Finset K6.edgeSet} (h : IsPMFinset K6 M)
    (e₀ e₁ e₂ : K6.edgeSet) (h₀ : e₀ ∈ M) (h₁ : e₁ ∈ M) (h₂ : e₂ ∈ M)
    (hcov : ∀ v : Fin 6, v ∈ (e₀ : Sym2 (Fin 6)) ∨ v ∈ (e₁ : Sym2 (Fin 6))
      ∨ v ∈ (e₂ : Sym2 (Fin 6))) :
    M = {e₀, e₁, e₂} := by
  apply Finset.Subset.antisymm
  · intro e heM
    obtain ⟨v, hv⟩ : ∃ v : Fin 6, v ∈ (e : Sym2 (Fin 6)) := by
      induction (e : Sym2 (Fin 6)) using Sym2.ind with
      | _ a b => exact ⟨a, by simp⟩
    obtain ⟨f, hf, huniq⟩ := h v
    have hcollapse : ∀ g : K6.edgeSet, g ∈ M → v ∈ (g : Sym2 (Fin 6)) → g = f :=
      fun g hgM hgv => huniq g ⟨hgM, hgv⟩
    have he : e = f := hcollapse e heM hv
    rcases hcov v with hv0 | hv1 | hv2
    · have : e₀ = f := hcollapse e₀ h₀ hv0
      simp [he, ← this]
    · have : e₁ = f := hcollapse e₁ h₁ hv1
      simp [he, ← this]
    · have : e₂ = f := hcollapse e₂ h₂ hv2
      simp [he, ← this]
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption

theorem exists_covering_triple {M : Finset K6.edgeSet} (h : IsPMFinset K6 M) :
    ∃ e₀ e₁ e₂ : K6.edgeSet, e₀ ∈ M ∧ e₁ ∈ M ∧ e₂ ∈ M ∧
      ∀ v : Fin 6, v ∈ (e₀ : Sym2 (Fin 6)) ∨ v ∈ (e₁ : Sym2 (Fin 6))
        ∨ v ∈ (e₂ : Sym2 (Fin 6)) := by
  obtain ⟨v, hv⟩ := exists_outside1 (edgeAt h 0)
  obtain ⟨w, hw0, hw1⟩ := exists_outside2 (edgeAt h 0) (edgeAt h v)
  refine ⟨edgeAt h 0, edgeAt h v, edgeAt h w, edgeAt_mem h 0, edgeAt_mem h v,
    edgeAt_mem h w, ?_⟩
  rcases covers_or_shares (edgeAt h 0) (edgeAt h v) (edgeAt h w) with
    hc | ⟨x, hx0, hx1⟩ | ⟨x, hx0, hx2⟩ | ⟨x, hx1, hx2⟩
  · exact hc
  · exact absurd ((eq_of_shared h _ _ (edgeAt_mem h 0) (edgeAt_mem h v) x hx0 hx1)
      ▸ edgeAt_covers h v) hv
  · exact absurd ((eq_of_shared h _ _ (edgeAt_mem h 0) (edgeAt_mem h w) x hx0 hx2)
      ▸ edgeAt_covers h w) hw0
  · exact absurd ((eq_of_shared h _ _ (edgeAt_mem h v) (edgeAt_mem h w) x hx1 hx2)
      ▸ edgeAt_covers h w) hw1

/-- The fifteen listed matchings are exactly the perfect matchings of `K6`.

Proved without `native_decide`.  Quantifying over `Finset K6.edgeSet` would
force the kernel through 2^15 finsets built on `Sym2` quotients; quantifying
over `K6.edgeSet` itself is cheap, so the forward direction picks three edges
via the uniqueness in `IsPMFinset` and leaves the combinatorics to
edge-indexed decisions. -/
theorem allPMs_complete : ∀ M : Finset K6.edgeSet,
    IsPMFinset K6 M ↔ M ∈ allPMs := by
  intro M
  constructor
  · intro h
    obtain ⟨e₀, e₁, e₂, h₀, h₁, h₂, hcov⟩ := exists_covering_triple h
    rw [pm_eq_triple h e₀ e₁ e₂ h₀ h₁ h₂ hcov]
    exact triple_mem e₀ e₁ e₂ hcov
  · exact mem_allPMs_isPM M

def w (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) (u v : Fin 6) : ℂ :=
  W (MonochromaticQuantumGraph.mkEdge u v (ι u) (ι v))

def pm15 (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) : ℂ :=
    w W ι 0 1 * w W ι 2 3 * w W ι 4 5
  + w W ι 0 1 * w W ι 2 4 * w W ι 3 5
  + w W ι 0 1 * w W ι 2 5 * w W ι 3 4
  + w W ι 0 2 * w W ι 1 3 * w W ι 4 5
  + w W ι 0 2 * w W ι 1 4 * w W ι 3 5
  + w W ι 0 2 * w W ι 1 5 * w W ι 3 4
  + w W ι 0 3 * w W ι 1 2 * w W ι 4 5
  + w W ι 0 3 * w W ι 1 4 * w W ι 2 5
  + w W ι 0 3 * w W ι 1 5 * w W ι 2 4
  + w W ι 0 4 * w W ι 1 2 * w W ι 3 5
  + w W ι 0 4 * w W ι 1 3 * w W ι 2 5
  + w W ι 0 4 * w W ι 1 5 * w W ι 2 3
  + w W ι 0 5 * w W ι 1 2 * w W ι 3 4
  + w W ι 0 5 * w W ι 1 3 * w W ι 2 4
  + w W ι 0 5 * w W ι 1 4 * w W ι 2 3

theorem official_pmSum_eq_pm15 (W : WeightsN 6 3 ℂ)
    (ι : Fin 6 → Fin 3) : pmSumN 6 3 W ι = pm15 W ι := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices, pm15, w]
  ring

theorem local_pmSum_eq_pm15 (W : WeightsN 6 3 ℂ)
    (ι : Fin 6 → Fin 3) : pmSum (restrictOfficial W) ι = pm15 W ι := by
  rw [pmSum_eq_sum_over (restrictOfficial W) ι allPMs allPMs_complete]
  rw [show allPMs = matchingList.toFinset from rfl]
  rw [List.sum_toFinset _ matchingList_nodup]
  simp [matchingList, edgeWeight, restrictOfficial, edge, pm15, w]
  ring

theorem pmSum_bridge (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) :
    pmSumN 6 3 W ι = pmSum (restrictOfficial W) ι := by
  rw [official_pmSum_eq_pm15, local_pmSum_eq_pm15]

theorem allEqual_iff_constant (ι : Fin 6 → Fin 3) :
    allEqual ι ↔ ∃ c : Fin 3, ι = fun _ => c := by
  simp [allEqual, allEqualList, vertices]
  constructor
  · rintro ⟨h01, h12, h23, h34, h45⟩
    refine ⟨ι 0, funext fun v => ?_⟩
    fin_cases v <;> simp_all
  · rintro ⟨c, rfl⟩
    simp

theorem eqSystem_bridge (W : WeightsN 6 3 ℂ) :
    EqSystemN 6 3 W ↔ EqSystem (restrictOfficial W) := by
  unfold EqSystemN EqSystem
  constructor <;> intro h ι
  · rw [← pmSum_bridge]
    simpa [allEqual_iff_constant] using h ι
  · rw [pmSum_bridge]
    simpa [allEqual_iff_constant] using h ι

/-- The direction needed to transfer a completed local impossibility proof to
the fixed official `N = 6`, `D = 3` statement. -/
theorem official_noSolution_of_local
    (hlocal : ¬ ∃ W : WeightSystem K6 3, EqSystem W) :
    ¬ ∃ W : WeightsN 6 3 ℂ, EqSystemN 6 3 W := by
  rintro ⟨W, hW⟩
  exact hlocal ⟨restrictOfficial W, (eqSystem_bridge W).mp hW⟩

/-- **Official specialization of the factorization theorem.**
`pmSum_bridge` composed with `pmSum_factor`: the official `N = 6`, `D = 3`
pmSum is the product of the symmetric-difference component contributions of
two edge-disjoint perfect matchings of `K6`, under the diagonal ansatz (weight
support confined to the union of the two matchings, with `i = j`).

Note: `hsupp` is stated on `restrictOfficial W`, so it constrains only the
normalized entries that `pmSumN` actually reads — fewer entries than a
hypothesis over all official edges, hence a slightly stronger theorem.

Trust base: kernel only.  `allPMs_complete` is now proved by kernel-checked
decisions over edges rather than by `native_decide`, so nothing here depends
on `Lean.ofReduceBool`. -/
theorem pmSum_factor_official (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3)
    (M₁ M₂ : K6.Subgraph)
    (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    (hdisj : Disjoint M₁.edgeSet M₂.edgeSet)
    (hsupp : ∀ (e : K6.edgeSet) (i j : Fin 3), restrictOfficial W e i j ≠ 0 →
      ((e : Sym2 (Fin 6)) ∈ M₁.edgeSet ∨ (e : Sym2 (Fin 6)) ∈ M₂.edgeSet) ∧ i = j)
    [Fintype (altGraph M₁ M₂).ConnectedComponent] :
    pmSumN 6 3 W ι =
      ∏ c, (A M₁ M₂ (restrictOfficial W) ι c +
        B M₁ M₂ (restrictOfficial W) ι c) := by
  rw [pmSum_bridge]
  exact pmSum_factor M₁ M₂ (restrictOfficial W) ι h₁ h₂ hdisj hsupp

#print axioms pmSum_factor_official

end Krenn.OfficialBridge
