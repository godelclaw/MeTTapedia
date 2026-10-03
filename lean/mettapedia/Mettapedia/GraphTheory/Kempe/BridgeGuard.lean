import Mettapedia.GraphTheory.Kempe.ForestGuard

/-!
# Composing transition guards across a joining edge

Two pieces joined by one edge exchange possible labels at its endpoints.
Separate satisfiability does not permit arbitrary witnesses to be combined:
the chosen labels must satisfy the joining edge in both orientations.
This exact elimination keeps one label per port, independently of piece size.

For Kempe transitions the label is an old colour and a switch bit. Once the
hidden region is a forest, the assembled guard reconstructs actual physical
histories, including preparation of the compatible local witnesses.
-/

namespace SimpleGraph.BinaryConstraints

variable {V A : Type*} (G : SimpleGraph V) (L : V → A → Prop)
    (R : V → V → A → A → Prop)

/-- A port message retains all labels supported by actual interior witnesses. -/
def Port (U : Set V) (u : U) (s : A) : Prop :=
  ∃ f : U → A, Valid (G.induce U) (fun x => L x) (fun x y => R x y) f ∧ f u = s

/-- Exact composition across a single edge. Internal graphs and constraints
are arbitrary; both orientations of the joining relation are retained. -/
theorem bridge_iff (U : Set V) (u : U) (v : ↥(Uᶜ))
    (edge : G.Adj u v)
    (cut : ∀ (x : U) (y : ↥(Uᶜ)), G.Adj x y → x = u ∧ y = v) :
    (∃ f, Valid G L R f) ↔
      ∃ s t, Port G L R U u s ∧ Port G L R Uᶜ v t ∧
        R u v s t ∧ R v u t s := by
  classical
  constructor
  · rintro ⟨f, unary, binary⟩
    exact ⟨f u, f v,
      ⟨fun x => f x, ⟨fun x => unary x, fun x y hxy => binary x y hxy⟩, rfl⟩,
      ⟨fun x => f x, ⟨fun x => unary x, fun x y hxy => binary x y hxy⟩, rfl⟩,
      binary u v edge, binary v u edge.symm⟩
  · rintro ⟨s, t, ⟨f, hf, hu⟩, ⟨g, hg, hv⟩, forward, backward⟩
    let F (x : V) : A := if hx : x ∈ U then f ⟨x, hx⟩ else g ⟨x, hx⟩
    refine ⟨F, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ U
      · simpa [F, hx] using hf.1 ⟨x, hx⟩
      · simpa [F, hx] using hg.1 ⟨x, hx⟩
    · intro x y hxy
      by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
      · simpa [F, hx, hy] using hf.2 ⟨x, hx⟩ ⟨y, hy⟩ hxy
      · obtain ⟨ex, ey⟩ := cut ⟨x, hx⟩ ⟨y, hy⟩ hxy
        have exv : x = u.val := congrArg Subtype.val ex
        have eyv : y = v.val := congrArg Subtype.val ey
        have relation : R x y (f ⟨x, hx⟩) (g ⟨y, hy⟩) := by
          simpa only [ex, ey, hu, hv, exv, eyv] using forward
        simpa [F, hx, hy] using relation
      · obtain ⟨ey, ex⟩ := cut ⟨y, hy⟩ ⟨x, hx⟩ hxy.symm
        have exv : x = v.val := congrArg Subtype.val ex
        have eyv : y = u.val := congrArg Subtype.val ey
        have relation : R x y (g ⟨x, hx⟩) (f ⟨y, hy⟩) := by
          simpa only [ex, ey, hu, hv, exv, eyv] using backward
        simpa [F, hx, hy] using relation
      · simpa [F, hx, hy] using hg.2 ⟨x, hx⟩ ⟨y, hy⟩ hxy

end SimpleGraph.BinaryConstraints

namespace SimpleGraph.KempeForestGuard

open BinaryConstraints KempeGuardedLift

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- Each piece exposes a possible transition label at its joining port. -/
def Bridge (S : Set V) (C D : (G.induce Sᶜ).Coloring α) (a b : α)
    (U : Set S) (u : U) (v : ↥(Uᶜ)) : Prop :=
  ∃ s t, Port (G.induce S) (Allowed S C D a b) (fun _ _ => Compatible a b) U u s ∧
    Port (G.induce S) (Allowed S C D a b) (fun _ _ => Compatible a b) Uᶜ v t ∧
    Compatible a b s t

/-- The port relation is precisely the full hidden transition guard. -/
theorem transition_bridge_iff (S : Set V) (C D : (G.induce Sᶜ).Coloring α) (a b : α)
    (U : Set S) (u : U) (v : ↥(Uᶜ)) (edge : G.Adj u.val.val v.val.val)
    (cut : ∀ (x : U) (y : ↥(Uᶜ)), G.Adj x.val.val y.val.val → x = u ∧ y = v) :
    Transition S C D a b ↔ Bridge S C D a b U u v := by
  rw [transition_iff, bridge_iff (G.induce S) _ _ U u v edge cut]
  constructor
  · rintro ⟨s, t, hs, ht, hst, _⟩
    exact ⟨s, t, hs, ht, hst⟩
  · rintro ⟨s, t, hs, ht, hst⟩
    exact ⟨s, t, hs, ht, hst, hst.1.symm, hst.2.symm⟩

/-- Compatible port messages construct a full target colouring and a physical
repair to it. Forest connectivity supplies preparation; neither a full target
extension nor reachability is a premise hidden in either message. -/
theorem repair_of_bridge [Fintype V] (S B : Set V) (retained : B ⊆ Sᶜ)
    (forest : (G.induce S).IsAcyclic) (C : G.Coloring α)
    (D : (G.induce Sᶜ).Coloring α) (a b : α)
    (U : Set S) (u : U) (v : ↥(Uᶜ)) (edge : G.Adj u.val.val v.val.val)
    (cut : ∀ (x : U) (y : ↥(Uᶜ)), G.Adj x.val.val y.val.val → x = u ∧ y = v)
    (pair : ∀ x : ↥(Sᶜ), D x = C x ∨ D x = Equiv.swap a b (C x))
    (fixed : ∀ x : ↥(Sᶜ), x.val ∈ B → C x = D x)
    (messages : Bridge S (C.restrictInduce Sᶜ) D a b U u v) :
    ∃ E : G.Coloring α, E.restrictInduce Sᶜ = D ∧
      Relation.ReflTransGen (G.KempeStepAvoiding B) C E := by
  apply (fibration S B retained (KempeForestFibre.fibres S forest)).liftsSteps C D
  exact ⟨⟨a, b, pair, (transition_bridge_iff S _ _ a b U u v edge cut).mpr messages⟩,
    fixed⟩

end SimpleGraph.KempeForestGuard
