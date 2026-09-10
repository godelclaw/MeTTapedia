import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond

/-!
# Constructing cuts closed under agreeing edges

Reachability constructs the least region containing a seed set and closed
under an edge subgraph. Such a region separates two terminal sets exactly
when that subgraph has no path between the terminals. Applied to the agreeing
edges of two labellings, its ambient crossing edges all disagree.

This construction supplies no uniform width or long nested chain. In particular,
if the agreeing subgraph is connected, every nonempty seed closes to the entire
graph. The separation criterion identifies that failure without assuming a cut.
-/

namespace Mettapedia.GraphTheory.FourColor.AgreementClosedCuts

open SimpleGraph VertexSeparatorBond

variable {V : Type*} (H : SimpleGraph V)

def hull (A : Set V) : Set V := flood H Set.univ A

theorem mem_hull_iff (A : Set V) (v : V) :
    v ∈ hull H A ↔ ∃ a ∈ A, H.Reachable a v := by
  constructor
  · rintro ⟨a, ha, p, _⟩
    exact ⟨a, ha, ⟨p⟩⟩
  · rintro ⟨a, ha, ⟨p⟩⟩
    exact ⟨a, ha, p, fun _ _ => Set.mem_univ _⟩

theorem seed_subset_hull (A : Set V) : A ⊆ hull H A := by
  intro v hv
  exact (mem_hull_iff H A v).mpr ⟨v, hv, SimpleGraph.Reachable.refl _⟩

def Closed (S : Set V) : Prop := ∀ u v, H.Adj u v → u ∈ S → v ∈ S

theorem hull_closed (A : Set V) : Closed H (hull H A) := by
  intro u v huv hu
  exact flood_adj H hu huv (Set.mem_univ _)

theorem Closed.walk {S : Set V} (h : Closed H S) {u v : V} (p : H.Walk u v) :
    u ∈ S → v ∈ S := by
  induction p with
  | nil => exact id
  | cons huv p ih => exact fun hu => ih (h _ _ huv hu)

theorem hull_least {A S : Set V} (hA : A ⊆ S) (hS : Closed H S) : hull H A ⊆ S := by
  intro v hv
  obtain ⟨a, ha, ⟨p⟩⟩ := (mem_hull_iff H A v).mp hv
  exact hS.walk H p (hA ha)

theorem hull_mono {A B : Set V} (h : A ⊆ B) : hull H A ⊆ hull H B :=
  hull_least H (h.trans (seed_subset_hull H B)) (hull_closed H B)

theorem hull_idempotent (A : Set V) : hull H (hull H A) = hull H A :=
  Set.Subset.antisymm (hull_least H (fun _ h => h) (hull_closed H A))
    (seed_subset_hull H (hull H A))

/-- The terminal obstruction is necessary and sufficient; the reverse direction
constructs the shore by reachability, rather than taking one as an input. -/
theorem exists_closed_separator_iff (A B : Set V) :
    (∃ S, A ⊆ S ∧ B ⊆ Sᶜ ∧ Closed H S) ↔
      ∀ a ∈ A, ∀ b ∈ B, ¬ H.Reachable a b := by
  constructor
  · rintro ⟨S, hA, hB, hS⟩ a ha b hb ⟨p⟩
    exact hB hb (hS.walk H p (hA ha))
  · intro h
    refine ⟨hull H A, seed_subset_hull H A, ?_, hull_closed H A⟩
    intro b hb hin
    obtain ⟨a, ha, hab⟩ := (mem_hull_iff H A b).mp hin
    exact h a ha b hb hab

theorem hull_eq_univ_of_preconnected (hH : H.Preconnected) {A : Set V}
    (hA : A.Nonempty) : hull H A = Set.univ := by
  obtain ⟨a, ha⟩ := hA
  apply Set.eq_univ_of_forall
  intro v
  exact (mem_hull_iff H A v).mpr ⟨a, ha, hH a v⟩

section Agreement

variable {C : Type*} (G : SimpleGraph V) (c d : Sym2 V → C)

/-- Equal labels on actual ambient edges. Off-edge values are irrelevant. -/
def agreementGraph : SimpleGraph V where
  Adj u v := G.Adj u v ∧ c s(u, v) = d s(u, v)
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1.ne rfl⟩

instance [DecidableRel G.Adj] [DecidableEq C] :
    DecidableRel (agreementGraph G c d).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Closure concerns the full ambient boundary, not merely a boundary
computed within the disagreement subgraph. -/
theorem closed_iff_boundary_disagrees (S : Set V) :
    Closed (agreementGraph G c d) S ↔
      ∀ u v, G.Adj u v → u ∈ S → v ∉ S → c s(u, v) ≠ d s(u, v) := by
  classical
  constructor
  · intro h u v huv hu hv heq
    exact hv (h u v ⟨huv, heq⟩ hu)
  · intro h u v huv hu
    by_contra hv
    exact h u v huv.1 hu hv huv.2

/-- Exact construction criterion for a separating shore with no agreeing
ambient crossing edges. No width estimate follows from this criterion. -/
theorem exists_disagreeing_separator_iff (A B : Set V) :
    (∃ S, A ⊆ S ∧ B ⊆ Sᶜ ∧
      ∀ u v, G.Adj u v → u ∈ S → v ∉ S → c s(u, v) ≠ d s(u, v)) ↔
      ∀ a ∈ A, ∀ b ∈ B, ¬ (agreementGraph G c d).Reachable a b := by
  simp only [← closed_iff_boundary_disagrees]
  exact exists_closed_separator_iff (agreementGraph G c d) A B

theorem hull_boundary_disagrees (A : Set V) {u v : V} (huv : G.Adj u v)
    (hu : u ∈ hull (agreementGraph G c d) A)
    (hv : v ∉ hull (agreementGraph G c d) A) : c s(u, v) ≠ d s(u, v) := by
  intro heq
  exact hv (hull_closed (agreementGraph G c d) A u v ⟨huv, heq⟩ hu)

end Agreement

end Mettapedia.GraphTheory.FourColor.AgreementClosedCuts
