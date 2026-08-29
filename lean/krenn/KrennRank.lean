import KrennCounterexamples

open SimpleGraph

namespace Krenn

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Serving one colour needs only one perfect matching. -/
theorem serves_one_of_isPerfectMatching
    {G : SimpleGraph V} {D : ℕ} (_hD : 1 ≤ D)
    {M : Subgraph G} (hM : M.IsPerfectMatching) (c : Fin D) :
    ∃ W : WeightSystem G D, Serves W {c} := by
  classical
  set W : WeightSystem G D := fun e i j =>
    if (e : Sym2 V) ∈ M.edgeSet ∧ i = c ∧ j = c then 1 else 0 with hWdef
  set F : Finset G.edgeSet :=
    Finset.univ.filter (fun e : G.edgeSet => (e : Sym2 V) ∈ M.edgeSet)
    with hFdef
  have memF : ∀ e : G.edgeSet, e ∈ F ↔ (e : Sym2 V) ∈ M.edgeSet := fun e => by
    simp [hFdef]
  have hPMF : IsPMFinset G F := by
    intro v
    obtain ⟨w, hvw, huniq⟩ := hM.1 (hM.2 v)
    refine ⟨⟨s(v, w), M.edgeSet_subset (Subgraph.mem_edgeSet.2 hvw)⟩,
      ⟨(memF _).2 (Subgraph.mem_edgeSet.2 hvw), Sym2.mem_mk_left v w⟩, ?_⟩
    rintro ⟨z, hz⟩ ⟨hzF, hvz⟩
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hvz
    have hadj : M.Adj v u := Subgraph.mem_edgeSet.1 ((memF _).1 hzF)
    have hu : u = w := huniq u hadj
    subst hu
    rfl
  have hsub_eq : ∀ M' : Finset G.edgeSet, IsPMFinset G M' →
      (∀ e ∈ M', (e : Sym2 V) ∈ M.edgeSet) → M' = F := by
    intro M' hPM' hsub
    ext e
    constructor
    · exact fun he => (memF e).2 (hsub e he)
    · intro heF
      have hvmem : (e : Sym2 V).inf ∈ (e : Sym2 V) :=
        mem_iff_eq_inf_or_sup.2 (Or.inl rfl)
      obtain ⟨e', ⟨he'M', hve'⟩, _⟩ := hPM' (e : Sym2 V).inf
      obtain ⟨e'', _, huniqF⟩ := hPMF (e : Sym2 V).inf
      have h1 : e' = e'' := huniqF e' ⟨(memF e').2 (hsub e' he'M'), hve'⟩
      have h2 : e = e'' := huniqF e ⟨heF, hvmem⟩
      rw [h2, ← h1]
      exact he'M'
  refine ⟨W, fun c' hc' => ?_, fun ι hι => ?_⟩
  · rw [Finset.mem_singleton] at hc'
    subst hc'
    have hFmem : F ∈ Finset.univ.filter
        (fun M'' : Finset G.edgeSet => IsPMFinset G M'') := by
      simp [hPMF]
    simp only [pmSum]
    rw [Finset.sum_eq_single_of_mem F hFmem]
    · exact Finset.prod_eq_one fun e heF => by
        simp [edgeWeight, hWdef, (memF e).1 heF]
    · intro M' hM'mem hne
      have hPM' : IsPMFinset G M' := (Finset.mem_filter.1 hM'mem).2
      by_cases hsub : ∀ e ∈ M', (e : Sym2 V) ∈ M.edgeSet
      · exact absurd (hsub_eq M' hPM' hsub) hne
      · push Not at hsub
        obtain ⟨e, heM', hnot⟩ := hsub
        exact Finset.prod_eq_zero heM' (by simp [edgeWeight, hWdef, hnot])
  · have hne : ∃ v, ι v ≠ c := by
      by_contra h
      push Not at h
      exact hι ⟨c, Finset.mem_singleton_self c, funext h⟩
    obtain ⟨v, hv⟩ := hne
    simp only [pmSum]
    refine Finset.sum_eq_zero fun M' hM'mem => ?_
    have hPM' : IsPMFinset G M' := (Finset.mem_filter.1 hM'mem).2
    obtain ⟨e, ⟨heM', hve⟩, _⟩ := hPM' v
    refine Finset.prod_eq_zero heM' ?_
    rcases mem_iff_eq_inf_or_sup.1 hve with h | h
    · simp [edgeWeight, hWdef, ← h, hv]
    · simp [edgeWeight, hWdef, ← h, hv]

/-- Serving a colour exposes a perfect matching with nonzero diagonal
weights in that colour. -/
lemma exists_pm_diag_nonzero_of_serves
    {G : SimpleGraph V} {D : ℕ} {W : WeightSystem G D} {C : Finset (Fin D)}
    (h : Serves W C) {c : Fin D} (hc : c ∈ C) :
    ∃ M : Finset G.edgeSet, IsPMFinset G M ∧ ∀ e ∈ M, W e c c ≠ 0 := by
  classical
  have hne : pmSum W (fun _ => c) ≠ 0 := by
    rw [h.1 c hc]
    exact one_ne_zero
  simp only [pmSum] at hne
  obtain ⟨M, hMmem, hMne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨M, (Finset.mem_filter.1 hMmem).2, fun e heM => ?_⟩
  have hfac := Finset.prod_ne_zero_iff.1 hMne e heM
  simpa [edgeWeight] using hfac

open scoped Classical in
/-- The exact equation-system form used by the complete-graph conjecture:
every constant colouring has amplitude one and every nonconstant colouring
has amplitude zero. -/
def EqSystem {G : SimpleGraph V} {D : ℕ} (W : WeightSystem G D) : Prop :=
  ∀ ι : V → Fin D,
    pmSum W ι = if ∃ c : Fin D, ι = fun _ => c then 1 else 0

open scoped Classical in
theorem eqSystem_iff_serves_univ {G : SimpleGraph V} {D : ℕ}
    (W : WeightSystem G D) : EqSystem W ↔ Serves W Finset.univ := by
  constructor
  · intro h
    constructor
    · intro c _
      rw [h (fun _ => c), if_pos ⟨c, rfl⟩]
    · intro ι hnonconstant
      have hn : ¬ ∃ c : Fin D, ι = fun _ => c := by
        simpa using hnonconstant
      rw [h ι, if_neg hn]
  · intro h ι
    by_cases hconstant : ∃ c : Fin D, ι = fun _ => c
    · obtain ⟨c, rfl⟩ := hconstant
      rw [if_pos ⟨c, rfl⟩]
      exact h.1 c (Finset.mem_univ c)
    · rw [if_neg hconstant]
      apply h.2
      simpa using hconstant

abbrev K6 : SimpleGraph (Fin 6) := ⊤

/-- The open crown target, matching the official `N = 6`, `D = 3`, complex
equation-system instance. This is a proposition, not a claimed theorem. -/
def K6D3NoSolution : Prop :=
  ¬ ∃ W : WeightSystem K6 3, EqSystem W

theorem k6D3NoSolution_iff : K6D3NoSolution ↔
    ¬ ∃ W : WeightSystem K6 3, Serves W Finset.univ := by
  simp only [K6D3NoSolution, eqSystem_iff_serves_univ]

end Krenn
