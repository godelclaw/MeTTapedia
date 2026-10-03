import Mettapedia.GraphTheory.Kempe.Restriction
import Mettapedia.GraphTheory.Kempe.PairDecomposition
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Lifting compatible recolouring across an independent hidden set

The retained graph and the degrees of hidden vertices are arbitrary. Hidden
vertices have no edges between them. Every partial transposition on the
retained vertices whose two endpoints extend lifts to an actual Kempe history.
The proof prepares the hidden colours, performs a proper partial transposition,
and finishes the hidden colours. No enumeration of colouring states is used.
-/

namespace SimpleGraph.KempeIndependentLift

open Relation Mettapedia.Combinatorics.Reconfiguration

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- Two proper colourings differing at only one vertex are joined by a
component switch supported at that vertex. -/
theorem single_vertex {C D : G.Coloring α} (v : V)
    (agree : ∀ x, x ≠ v → C x = D x) (B : Set V) (hvB : v ∉ B) :
    G.KempeStepAvoiding B C D := by
  classical
  have active : v ∈ C.bicoloredSet (C v) (D v) := Or.inl rfl
  let K := (C.bicoloredSubgraph (C v) (D v)).connectedComponentMk ⟨v, active⟩
  have small : C.kempeComponentSet (C v) (D v) K ⊆ {v} :=
    C.kempeComponentSet_subset_of_closed active (Set.mem_singleton v) (by
      intro x y hx hxy hy
      have hxv : x = v := hx
      subst x
      rcases hy with hy | hy
      · exact (C.valid hxy hy.symm).elim
      · exact (D.valid hxy ((agree y hxy.ne.symm).symm.trans hy).symm).elim)
  refine ⟨C v, D v, K, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun x hx hxB => hvB ((small hx) ▸ hxB)
  · apply DFunLike.ext
    intro x
    by_cases hx : x = v
    · subst x
      rw [C.swapOnKempeComponent_apply_of_mem (C.mem_kempeComponentSet_self active)]
      exact (Equiv.swap_apply_left _ _).symm
    · rw [C.swapOnKempeComponent_apply_of_not_mem (fun h => hx (small h))]
      exact (agree x hx).symm

/-- Every fibre over the retained vertices of an independent deletion is
connected by switches that never touch those retained vertices. -/
theorem fibre_path [DecidableEq V] (S : Finset V) (independent : G.IsIndepSet (S : Set V))
    (C D : G.Coloring α) (agree : ∀ x, x ∉ S → C x = D x) :
    ReflTransGen (G.KempeStepAvoiding (↑S)ᶜ) C D := by
  classical
  induction S using Finset.induction_on generalizing C D with
  | empty =>
      have he : C = D := DFunLike.ext _ _ (fun x => agree x (by simp))
      subst D
      exact .refl
  | @insert v S hv ih =>
      have neighbours (x : V) (h : G.Adj v x) : x ∉ insert v S := by
        intro hx
        exact independent (by simp) hx h.ne h
      let next : G.Coloring α := .mk (fun x => if x = v then D x else C x) (by
        intro x y hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · exact (hxy.ne (hx.trans hy.symm)).elim
        · subst x
          simpa [hy, agree y (neighbours y hxy)] using D.valid hxy
        · subst y
          simpa [hx, agree x (neighbours x hxy.symm)] using D.valid hxy
        · simpa [hx, hy] using C.valid hxy)
      have hnext (x : V) : next x = if x = v then D x else C x := rfl
      have first : G.KempeStepAvoiding (↑(insert v S))ᶜ C next :=
        single_vertex v (fun x hx => by simp [hnext, hx]) _ (by simp)
      have rest : ReflTransGen (G.KempeStepAvoiding (↑S)ᶜ) next D := ih
        (independent.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)) next D (by
          intro x hx
          by_cases hxv : x = v
          · simp [hnext, hxv]
          · simpa [hnext, hxv] using agree x (by simp [hx, hxv]))
      exact (ReflTransGen.single first).trans (ReflTransGen.mono (fun _ _ h =>
        h.mono (by intro x hx hxS; exact hx (Finset.mem_insert_of_mem hxS))) _ _ rest)

private theorem fixed_ne {a b z x y : α} (hz : z ≠ a ∧ z ≠ b)
    (hxy : y = x ∨ y = Equiv.swap a b x) (hzy : z ≠ y) : z ≠ x := by
  rcases hxy with rfl | rfl
  · exact hzy
  · intro h
    apply hzy
    rw [← h, Equiv.swap_apply_of_ne_of_ne hz.1 hz.2]

/-- The colour bridge uses endpoint compatibility rather than a degree bound. -/
theorem colour_bridge (a b c d : α) (old next : V → α) (N : Set V)
    (hc : ∀ x ∈ N, c ≠ old x) (hd : ∀ x ∈ N, d ≠ next x)
    (pair : ∀ x ∈ N, next x = old x ∨ next x = Equiv.swap a b (old x)) :
    ∃ z z', (∀ x ∈ N, z ≠ old x) ∧ (∀ x ∈ N, z' ≠ next x) ∧
      (z' = z ∨ z' = Equiv.swap a b z) := by
  classical
  by_cases hca : c = a ∨ c = b
  · by_cases hda : d = a ∨ d = b
    · refine ⟨c, d, hc, hd, ?_⟩
      rcases hca with rfl | rfl <;> rcases hda with rfl | rfl <;> simp
    · have hdab : d ≠ a ∧ d ≠ b := not_or.mp hda
      exact ⟨d, d, fun x hx => fixed_ne hdab (pair x hx) (hd x hx), hd, Or.inl rfl⟩
  · have hcab : c ≠ a ∧ c ≠ b := not_or.mp hca
    refine ⟨c, c, hc, ?_, Or.inl rfl⟩
    intro x hx
    rcases pair x hx with hp | hp
    · simpa [hp] using hc x hx
    · rw [hp, ← Equiv.swap_apply_of_ne_of_ne hcab.1 hcab.2]
      exact (Equiv.swap a b).injective.ne (hc x hx)

/-- If the hidden vertices are independent, every extendable partial pair
swap on the retained vertices lifts. Both full endpoints are retained. -/
theorem partial_swap_avoiding [Fintype V] [DecidableEq V]
    (S : Finset V) (independent : G.IsIndepSet (S : Set V))
    (B : Set V) (retained : B ⊆ (↑S)ᶜ)
    (C D : G.Coloring α) (fixed : ∀ x ∈ B, C x = D x) (a b : α)
    (pair : ∀ x, x ∉ S → D x = C x ∨ D x = Equiv.swap a b (C x)) :
    ReflTransGen (G.KempeStepAvoiding B) C D := by
  classical
  have bridge : ∀ v ∈ S, ∃ z z',
      (∀ x, G.Adj v x → z ≠ C x) ∧ (∀ x, G.Adj v x → z' ≠ D x) ∧
        (z' = z ∨ z' = Equiv.swap a b z) := by
    intro v hv
    exact colour_bridge a b (C v) (D v) C D (G.neighborSet v)
      (fun _ h => C.valid h) (fun _ h => D.valid h) (fun x hx =>
        pair x (fun hs => independent hv hs hx.ne hx))
  choose before after before_ok after_ok related using bridge
  let prepared : G.Coloring α := .mk (fun x => if hx : x ∈ S then before x hx else C x) (by
    intro x y hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · exact (independent hx hy hxy.ne hxy).elim
    · simpa [hx, hy] using before_ok x hx y hxy
    · simpa [hx, hy] using (before_ok y hy x hxy.symm).symm
    · simpa [hx, hy] using C.valid hxy)
  let final : G.Coloring α := .mk (fun x => if hx : x ∈ S then after x hx else D x) (by
    intro x y hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · exact (independent hx hy hxy.ne hxy).elim
    · simpa [hx, hy] using after_ok x hx y hxy
    · simpa [hx, hy] using (after_ok y hy x hxy.symm).symm
    · simpa [hx, hy] using D.valid hxy)
  have prep_apply (x : V) : prepared x = if hx : x ∈ S then before x hx else C x := rfl
  have final_apply (x : V) : final x = if hx : x ∈ S then after x hx else D x := rfl
  have prep : ReflTransGen (G.KempeStepAvoiding B) C prepared :=
    ReflTransGen.mono (fun _ _ h => h.mono retained) _ _
      (fibre_path S independent C prepared (fun x hx => by simp [prep_apply, hx]))
  have finish : ReflTransGen (G.KempeStepAvoiding B) final D :=
    ReflTransGen.mono (fun _ _ h => h.mono retained) _ _
      (fibre_path S independent final D (fun x hx => by simp [final_apply, hx]))
  have middle : ReflTransGen (G.KempeStepAvoiding B) prepared final :=
    prepared.avoiding_of_pointwise_swap final a b B (by
      intro x hx
      have hn : x ∉ S := retained hx
      simpa [prep_apply, final_apply, hn] using fixed x hx) (by
      intro x
      by_cases hx : x ∈ S
      · simpa [prep_apply, final_apply, hx] using related x hx
      · simpa [prep_apply, final_apply, hx] using pair x hx)
  exact prep.trans (middle.trans finish)

/-- The unrestricted-boundary form retains both specified full endpoints. -/
theorem partial_swap [Fintype V] [DecidableEq V]
    (S : Finset V) (independent : G.IsIndepSet (S : Set V))
    (C D : G.Coloring α) (a b : α)
    (pair : ∀ x, x ∉ S → D x = C x ∨ D x = Equiv.swap a b (C x)) :
    D ∈ G.KempeClosure C :=
  ReflTransGen.mono (fun _ _ h => h.kempeStep) _ _
    (partial_swap_avoiding S independent ∅ (Set.empty_subset _) C D (by simp) a b pair)

omit [DecidableEq α] in
/-- Exact joint support after eliminating an independent set: every hidden
vertex must have a colour absent from all its retained neighbours. Shared
retained vertices use one common colouring throughout this condition. -/
theorem extends_iff [DecidableEq V] (S : Finset V)
    (independent : G.IsIndepSet (S : Set V))
    (C : (G.induce (↑S)ᶜ).Coloring α) :
    (∃ D : G.Coloring α, D.restrictInduce (↑S)ᶜ = C) ↔
      ∀ v ∈ S, ∃ c : α, ∀ x : ↥((↑S : Set V)ᶜ), G.Adj v x → c ≠ C x := by
  classical
  constructor
  · rintro ⟨D, hD⟩ v hv
    refine ⟨D v, fun x hx => ?_⟩
    have he : D x = C x := DFunLike.congr_fun hD x
    simpa [← he] using D.valid hx
  · intro h
    choose colour good using h
    let D : G.Coloring α := .mk
      (fun v => if hv : v ∈ S then colour v hv else C ⟨v, hv⟩) (by
        intro x y hxy
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · exact (independent hx hy hxy.ne hxy).elim
        · simpa [hx, hy] using good x hx ⟨y, hy⟩ hxy
        · simpa [hx, hy] using (good y hy ⟨x, hx⟩ hxy.symm).symm
        · simpa [hx, hy] using C.valid (show (G.induce (↑S)ᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))
    refine ⟨D, ?_⟩
    apply DFunLike.ext
    intro x
    exact dite_eq_right x.property

/-- A joint operation may switch several components of one colour pair.
The endpoint is a genuine proper colouring; colours on `B` are fixed. -/
def PairStep (H : SimpleGraph V) (B : Set V) (C D : H.Coloring α) : Prop :=
  (∃ a b, ∀ x, D x = C x ∨ D x = Equiv.swap a b (C x)) ∧
    ∀ x ∈ B, C x = D x

/-- These joint operations already have ordinary physical semantics. -/
theorem pairStep_realized [Fintype V] {B : Set V} {C D : G.Coloring α}
    (h : PairStep G B C D) : ReflTransGen (G.KempeStepAvoiding B) C D := by
  obtain ⟨⟨a, b, pair⟩, fixed⟩ := h
  exact C.avoiding_of_pointwise_swap D a b B fixed pair

/-- Joint operations, rather than only individual small components, give
an exact interface for an independent deletion. -/
theorem pair_fibration [Fintype V] [DecidableEq V]
    (S : Finset V) (independent : G.IsIndepSet (S : Set V))
    (B : Set V) (retained : B ⊆ (↑S)ᶜ) :
    Mettapedia.Combinatorics.Reconfiguration.Fibration (G.KempeStepAvoiding B)
      (ImageStep (PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B))
        (fun C : G.Coloring α => C.restrictInduce (↑S)ᶜ))
      (fun C : G.Coloring α => C.restrictInduce (↑S)ᶜ) where
  fibresConnected C D hCD := ReflTransGen.mono (fun _ _ h => h.mono retained) _ _
    (fibre_path S independent C D (fun x hx => DFunLike.congr_fun hCD ⟨x, hx⟩))
  liftsSteps C next hstep := by
    obtain ⟨⟨⟨a, b, pair⟩, fixed⟩, D, hD⟩ := hstep
    refine ⟨D, hD, partial_swap_avoiding S independent B retained C D ?_ a b ?_⟩
    · intro x hx
      exact (fixed ⟨x, retained hx⟩ hx).trans
        (DFunLike.congr_fun hD ⟨x, retained hx⟩).symm
    · intro x hx
      simpa only [← hD, Coloring.restrictInduce_apply] using pair ⟨x, hx⟩

/-- Every physical component projects to a joint operation. It may split
into several retained components, whose choices must stay coupled. This
direction needs no independence hypothesis. -/
theorem projects_pair_steps [DecidableEq V] (S : Finset V) (B : Set V) :
    ProjectsSteps (G.KempeStepAvoiding (α := α) B)
      (ImageStep (PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B))
        (fun C : G.Coloring α => C.restrictInduce (↑S)ᶜ))
      (fun C : G.Coloring α => C.restrictInduce (↑S)ᶜ) := by
  intro C D step
  apply ReflTransGen.single
  refine ⟨⟨?_, ?_⟩, D, rfl⟩
  · obtain ⟨a, b, K, _, rfl⟩ := step
    refine ⟨a, b, fun x => ?_⟩
    by_cases hx : x.val ∈ C.kempeComponentSet a b K
    · exact Or.inr (C.swapOnKempeComponent_apply_of_mem hx)
    · exact Or.inl (C.swapOnKempeComponent_apply_of_not_mem hx)
  · exact fun x hx => (step.apply_eq_of_mem hx).symm

/-- Exact preservation of reachability, including a fixed surrounding
boundary. Existential witnesses for successive abstract states really compose. -/
theorem projected_history_iff [Fintype V] [DecidableEq V]
    (S : Finset V) (independent : G.IsIndepSet (S : Set V))
    (B : Set V) (retained : B ⊆ (↑S)ᶜ) (C D : G.Coloring α) :
    ReflTransGen
      (ImageStep (PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B))
        (fun C : G.Coloring α => C.restrictInduce (↑S)ᶜ))
      (C.restrictInduce (↑S)ᶜ) (D.restrictInduce (↑S)ᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding B) C D :=
  ⟨(pair_fibration S independent B retained).reach,
    (projects_pair_steps S B).reach⟩

/-- The abstract guard is the explicit local colour-availability formula,
not a new existential search over all hidden assignments. -/
theorem pair_guard_iff [DecidableEq V] (S : Finset V)
    (independent : G.IsIndepSet (S : Set V)) (B : Set V)
    (C D : (G.induce (↑S)ᶜ).Coloring α) :
    ImageStep (PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B))
      (fun E : G.Coloring α => E.restrictInduce (↑S)ᶜ) C D ↔
      PairStep (G.induce (↑S)ᶜ) (Subtype.val ⁻¹' B) C D ∧
      ∀ v ∈ S, ∃ c : α, ∀ x : ↥((↑S : Set V)ᶜ), G.Adj v x → c ≠ D x := by
  exact and_congr_right fun _ => extends_iff S independent D

end SimpleGraph.KempeIndependentLift
