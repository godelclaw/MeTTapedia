import Mettapedia.GraphTheory.Kempe.TwoVertexFibre

/-!
# Joint transition guards for interacting hidden vertices

A guard retains hidden colours before and after a chosen transposition,
their internal edges, and their common retained neighbours. It contains
no reachability assertion. Given connected restriction fibres, guarded
histories coincide exactly with physical Kempe histories. For two hidden
vertices the fibre condition is proved for every finite graph and palette.

This is elimination into a constrained transition system, not an ordinary
smaller-graph reduction. Applying another elimination must retain the guards.
-/

namespace SimpleGraph.KempeGuardedLift

open Relation Mettapedia.Combinatorics.Reconfiguration

variable {V α : Type*} {G : SimpleGraph V}

/-- A proper hidden assignment fits a retained colouring when every edge
crossing the interface has different endpoint colours. -/
def Fits (S : Set V) (C : (G.induce Sᶜ).Coloring α)
    (h : (G.induce S).Coloring α) : Prop :=
  ∀ (x : S) (y : ↥(Sᶜ)), G.Adj x y → h x ≠ C y

noncomputable def glue (S : Set V) (C : (G.induce Sᶜ).Coloring α)
    (h : (G.induce S).Coloring α) (fit : Fits S C h) : G.Coloring α := by
  classical
  exact .mk (fun x => if hx : x ∈ S then h ⟨x, hx⟩ else C ⟨x, hx⟩) (by
    intro x y hxy
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simpa [hx, hy] using h.valid (show (G.induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    · simpa [hx, hy] using fit ⟨x, hx⟩ ⟨y, hy⟩ hxy
    · simpa [hx, hy] using (fit ⟨y, hy⟩ ⟨x, hx⟩ hxy.symm).symm
    · simpa [hx, hy] using C.valid (show (G.induce Sᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))

@[simp] theorem glue_hidden (S : Set V) (C : (G.induce Sᶜ).Coloring α)
    (h : (G.induce S).Coloring α) (fit : Fits S C h) (x : S) :
    glue S C h fit x = h x := by classical exact dite_eq_left x.property

@[simp] theorem glue_retained (S : Set V) (C : (G.induce Sᶜ).Coloring α)
    (h : (G.induce S).Coloring α) (fit : Fits S C h) (x : ↥(Sᶜ)) :
    glue S C h fit x = C x := by classical exact dite_eq_right x.property

@[simp] theorem glue_restrict (S : Set V) (C : (G.induce Sᶜ).Coloring α)
    (h : (G.induce S).Coloring α) (fit : Fits S C h) :
    (glue S C h fit).restrictInduce Sᶜ = C :=
  DFunLike.ext _ _ (glue_retained S C h fit)

variable [DecidableEq α]

/-- Two compatible hidden assignments related pointwise by the same colour
transposition. For a hidden pair this involves only four colour variables. -/
def Transition (S : Set V) (C D : (G.induce Sᶜ).Coloring α) (a b : α) : Prop :=
  ∃ h k : (G.induce S).Coloring α, Fits S C h ∧ Fits S D k ∧
    ∀ x, k x = h x ∨ k x = Equiv.swap a b (h x)

/-- One guarded joint operation on the retained graph. -/
def Step (S B : Set V) (C D : (G.induce Sᶜ).Coloring α) : Prop :=
  (∃ a b, (∀ x, D x = C x ∨ D x = Equiv.swap a b (C x)) ∧ Transition S C D a b) ∧
    ∀ x : ↥(Sᶜ), x.val ∈ B → C x = D x

/-- Prepare a compatible hidden witness, realize its joint transposition,
and finish at any prescribed extension of the target. -/
theorem lift [Fintype V] (S B : Set V) (retained : B ⊆ Sᶜ)
    (fibres : G.FibreConnected α Sᶜ) (C D : G.Coloring α)
    (step : Step S B (C.restrictInduce Sᶜ) (D.restrictInduce Sᶜ)) :
    ReflTransGen (G.KempeStepAvoiding B) C D := by
  classical
  obtain ⟨⟨a, b, pair, h, k, hfit, kfit, hidden⟩, fixed⟩ := step
  let E := glue S (C.restrictInduce Sᶜ) h hfit
  let F := glue S (D.restrictInduce Sᶜ) k kfit
  have prep : ReflTransGen (G.KempeStepAvoiding B) C E :=
    ReflTransGen.mono (fun _ _ hs => hs.mono retained) _ _ (fibres C E (by
      apply Coloring.boundaryWord_eq_iff.mpr
      intro x hx
      exact (glue_retained S _ h hfit ⟨x, hx⟩).symm))
  have finish : ReflTransGen (G.KempeStepAvoiding B) F D :=
    ReflTransGen.mono (fun _ _ hs => hs.mono retained) _ _ (fibres F D (by
      apply Coloring.boundaryWord_eq_iff.mpr
      intro x hx
      exact glue_retained S _ k kfit ⟨x, hx⟩))
  have middle : ReflTransGen (G.KempeStepAvoiding B) E F :=
    E.avoiding_of_pointwise_swap F a b B (by
      intro x hx
      simpa only [E, F, glue_retained S _ h hfit ⟨x, retained hx⟩,
        glue_retained S _ k kfit ⟨x, retained hx⟩] using fixed ⟨x, retained hx⟩ hx) (by
      intro x
      by_cases hx : x ∈ S
      · simpa only [E, F, glue_hidden S _ h hfit ⟨x, hx⟩,
          glue_hidden S _ k kfit ⟨x, hx⟩] using hidden ⟨x, hx⟩
      · simpa only [E, F, glue_retained S _ h hfit ⟨x, hx⟩,
          glue_retained S _ k kfit ⟨x, hx⟩] using pair ⟨x, hx⟩)
  exact prep.trans (middle.trans finish)

/-- The target extension is constructed from the guard, rather than assumed. -/
theorem fibration [Fintype V] (S B : Set V) (retained : B ⊆ Sᶜ)
    (fibres : G.FibreConnected α Sᶜ) :
    Mettapedia.Combinatorics.Reconfiguration.Fibration (G.KempeStepAvoiding B) (Step S B)
      (fun C : G.Coloring α => C.restrictInduce Sᶜ) where
  fibresConnected := fibresConnected_nearProj retained fibres
  liftsSteps C next hs := by
    have step := hs
    obtain ⟨⟨a, b, _, h, k, _, kfit, _⟩, _⟩ := hs
    let D := glue S next k kfit
    have hd : D.restrictInduce Sᶜ = next := glue_restrict S next k kfit
    exact ⟨D, hd, lift S B retained fibres C D (hd.symm ▸ step)⟩

/-- Every physical switch supplies the guard using its actual hidden
assignments. This direction requires no fibre-connectivity hypothesis. -/
theorem projects (S B : Set V) :
    ProjectsSteps (G.KempeStepAvoiding (α := α) B) (Step S B)
      (fun C : G.Coloring α => C.restrictInduce Sᶜ) := by
  intro C D hs
  apply ReflTransGen.single
  have fixed : ∀ x : ↥(Sᶜ), x.val ∈ B → C x = D x :=
    fun _ hx => (hs.apply_eq_of_mem hx).symm
  obtain ⟨a, b, K, _, rfl⟩ := hs
  have pair (x : V) : C.swapOnKempeComponent a b K x = C x ∨
      C.swapOnKempeComponent a b K x = Equiv.swap a b (C x) := by
    by_cases hx : x ∈ C.kempeComponentSet a b K
    · exact Or.inr (C.swapOnKempeComponent_apply_of_mem hx)
    · exact Or.inl (C.swapOnKempeComponent_apply_of_not_mem hx)
  refine ⟨⟨a, b, fun x => pair x, C.restrictInduce S,
    (C.swapOnKempeComponent a b K).restrictInduce S, ?_, ?_, fun x => pair x⟩, fixed⟩
  · exact fun _ _ hxy => C.valid hxy
  · exact fun _ _ hxy => (C.swapOnKempeComponent a b K).valid hxy

/-- Exact physical reachability through the guarded interface, with all
intermediate witnesses genuinely composed. -/
theorem history_iff [Fintype V] (S B : Set V) (retained : B ⊆ Sᶜ)
    (fibres : G.FibreConnected α Sᶜ) (C D : G.Coloring α) :
    ReflTransGen (Step S B) (C.restrictInduce Sᶜ) (D.restrictInduce Sᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding B) C D :=
  ⟨(fibration S B retained fibres).reach, (projects S B).reach⟩

/-- The missing fibre hypothesis is discharged uniformly for two hidden
vertices, including adjacent ones. -/
theorem two_vertex_fibres [Fintype V] (u v : V) :
    G.FibreConnected α ({u, v} : Set V)ᶜ := by
  intro C D h
  apply KempeTwoVertexFibre.fibre_path u v C D
  intro x hxu hxv
  exact Coloring.boundaryWord_eq_iff.mp h x (by simp [hxu, hxv])

/-- A complete guarded elimination theorem for an arbitrary hidden pair;
no geometric, degree, or unproved lifting hypothesis remains. -/
theorem two_vertex_history_iff [Fintype V] (u v : V) (B : Set V)
    (retained : B ⊆ ({u, v} : Set V)ᶜ) (C D : G.Coloring α) :
    ReflTransGen (Step {u, v} B)
      (C.restrictInduce ({u, v} : Set V)ᶜ) (D.restrictInduce ({u, v} : Set V)ᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding B) C D :=
  history_iff {u, v} B retained (two_vertex_fibres u v) C D

end SimpleGraph.KempeGuardedLift
