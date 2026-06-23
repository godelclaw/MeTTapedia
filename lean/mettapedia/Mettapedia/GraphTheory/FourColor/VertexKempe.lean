import Mathlib.Logic.Relation

namespace Mettapedia.GraphTheory.FourColor.VertexKempe

open Relation

/-- Swap two vertex colors, leaving every other color fixed. -/
def vertexColorSwap {C : Type*} [DecidableEq C] (α β : C) (c : C) : C :=
  if c = α then β else if c = β then α else c

@[simp]
theorem vertexColorSwap_left {C : Type*} [DecidableEq C] (α β : C) :
    vertexColorSwap α β α = β := by
  simp [vertexColorSwap]

@[simp]
theorem vertexColorSwap_right {C : Type*} [DecidableEq C] {α β : C} (hαβ : α ≠ β) :
    vertexColorSwap α β β = α := by
  simp [vertexColorSwap, hαβ.symm]

@[simp]
theorem vertexColorSwap_of_ne {C : Type*} [DecidableEq C] {α β c : C}
    (hα : c ≠ α) (hβ : c ≠ β) :
    vertexColorSwap α β c = c := by
  simp [vertexColorSwap, hα, hβ]

/-- Perform a Kempe switch on exactly the vertices in `K`. -/
noncomputable def kempeSwitch {V C : Type*} [DecidableEq C]
    (color : V → C) (K : Set V) (α β : C) : V → C := by
  classical
  exact fun v => if v ∈ K then vertexColorSwap α β (color v) else color v

@[simp]
theorem kempeSwitch_of_not_mem {V C : Type*} [DecidableEq C]
    (color : V → C) (K : Set V) (α β : C) {v : V} (hv : v ∉ K) :
    kempeSwitch color K α β v = color v := by
  classical
  simp [kempeSwitch, hv]

@[simp]
theorem kempeSwitch_of_mem_left {V C : Type*} [DecidableEq C]
    (color : V → C) (K : Set V) (α β : C) {v : V}
    (hvK : v ∈ K) (hα : color v = α) :
    kempeSwitch color K α β v = β := by
  classical
  simp [kempeSwitch, hvK, hα]

@[simp]
theorem kempeSwitch_of_mem_right {V C : Type*} [DecidableEq C]
    (color : V → C) (K : Set V) {α β : C} {v : V}
    (hαβ : α ≠ β) (hvK : v ∈ K) (hβ : color v = β) :
    kempeSwitch color K α β v = α := by
  classical
  simpa [kempeSwitch, hvK, hβ] using
    (vertexColorSwap_right (α := α) (β := β) hαβ)

/-- The two-color vertex subgraph induced by an adjacency relation and two colors. -/
def twoColorSubgraph {V C : Type*} (adj : V → V → Prop) (color : V → C)
    (α β : C) (u v : V) : Prop :=
  adj u v ∧ (color u = α ∨ color u = β) ∧ (color v = α ∨ color v = β)

/-- The connected component of `v` in the two-color vertex subgraph. -/
def vertexKempeChain {V C : Type*} (adj : V → V → Prop) (color : V → C)
    (α β : C) (v : V) : Set V :=
  {w | Relation.ReflTransGen (twoColorSubgraph adj color α β) v w}

/-- Every vertex in a two-color Kempe chain has one of the two selected colors,
provided the seed vertex has one of them. -/
theorem kempe_chain_colors {V C : Type*} (adj : V → V → Prop) (color : V → C)
    (α β : C) (v w : V)
    (hv : color v = α ∨ color v = β)
    (hw : w ∈ vertexKempeChain adj color α β v) :
    color w = α ∨ color w = β := by
  unfold vertexKempeChain at hw
  induction hw with
  | refl => exact hv
  | tail _ hstep _ih =>
      exact hstep.2.2

/-- Predicate-based adjacency in the two-color subgraph, requiring endpoints to
have different colors. -/
def twoColorAdjP {V C : Type*} (adj : V → V → Prop) (color : V → C) (α β : C) :
    V → V → Prop :=
  fun u w =>
    adj u w ∧ (color u = α ∨ color u = β) ∧
      (color w = α ∨ color w = β) ∧ color u ≠ color w

/-- Predicate-based two-color Kempe chain. -/
def chainP {V C : Type*} (adj : V → V → Prop) (color : V → C)
    (v : V) (α β : C) : Set V :=
  {u | (color u = α ∨ color u = β) ∧
    Relation.ReflTransGen (twoColorAdjP adj color α β) v u}

/-- If `w` is adjacent to the chain seed by a two-color edge, it is immediately in
the predicate-based chain. -/
theorem chainP_touches_seed_edge {V C : Type*} (adj : V → V → Prop) (color : V → C)
    (v w : V) (α β : C)
    (hadj_w : twoColorAdjP adj color α β v w) :
    w ∈ chainP adj color v α β := by
  unfold chainP
  exact ⟨hadj_w.2.2.1, Relation.ReflTransGen.single hadj_w⟩

/-- If one two-color edge out of the seed is represented in the predicate chain,
then every other two-color edge out of the seed is also represented. -/
theorem chainP_touches_both_edges {V C : Type*} (adj : V → V → Prop) (color : V → C)
    (v u w : V) (α β : C)
    (_hadj_u : twoColorAdjP adj color α β v u)
    (hadj_w : twoColorAdjP adj color α β v w)
    (_hu_in : u ∈ chainP adj color v α β) :
    w ∈ chainP adj color v α β :=
  chainP_touches_seed_edge adj color v w α β hadj_w

/-- A reusable characterization of when a Kempe switch frees color `α` at a
vertex `v`: all `α`-colored neighbors must be switched, and no `β`-colored
neighbor may be switched into `α`. -/
theorem frees_color_at_vertex_iff {V C : Type*} [DecidableEq C]
    (adj : V → V → Prop) (color : V → C)
    (v seed : V) {α β : C} (hαβ : α ≠ β)
    (hseed : color seed = α ∨ color seed = β) :
    let K := vertexKempeChain adj color α β seed
    let color' := kempeSwitch color K α β
    ((∀ w, adj v w → color' w ≠ α) ↔
      ((∀ w, adj v w → color w = α → w ∈ K) ∧
       (∀ w, adj v w → color w = β → w ∉ K))) := by
  classical
  intro K color'
  constructor
  · intro hfree
    constructor
    · intro w hv hαw
      by_cases hwK : w ∈ K
      · exact hwK
      · have hstill : color' w = α := by
          simp [color', hwK, hαw]
        exact False.elim (hfree w hv hstill)
    · intro w hv hβw hwK
      have hswapped : color' w = α :=
        kempeSwitch_of_mem_right color K hαβ hwK hβw
      exact hfree w hv hswapped
  · rintro ⟨hαall, hβnone⟩ w hv
    by_cases hwK : w ∈ K
    · have hcolor : color w = α ∨ color w = β :=
        kempe_chain_colors adj color α β seed w hseed hwK
      cases hcolor with
      | inl hαw =>
          intro hbad
          have hswapped : color' w = β := by
            simp [color', hwK, hαw]
          rw [hswapped] at hbad
          exact hαβ hbad.symm
      | inr hβw =>
          exact False.elim (hβnone w hv hβw hwK)
    · intro hbad
      have hαw : color w = α := by
        simpa [color', hwK] using hbad
      exact hwK (hαall w hv hαw)

/-- If an unswitched `α`-colored neighbor remains outside the Kempe component,
then the Kempe switch does not free `α` at `v`. -/
theorem kempeSwitch_does_not_free_if_other_alpha_outside {V C : Type*} [DecidableEq C]
    (adj : V → V → Prop) (color : V → C)
    (K : Set V) (α β : C) (v w₁ w₃ : V)
    (_hadj₁ : adj v w₁) (_hadj₃ : adj v w₃)
    (_hα₁ : color w₁ = α) (hα₃ : color w₃ = α)
    (_hK₁ : w₁ ∈ K) (hK₃ : w₃ ∉ K) :
    let color' := kempeSwitch color K α β
    color' w₃ = α := by
  classical
  intro color'
  simp [color', hK₃, hα₃]

section Counterexample

/-- Vertex set for a small star graph that refutes the naive color-freeing claim. -/
inductive CounterVertex : Type
  | center
  | w1
  | w2
  | w3
  | w4
  deriving DecidableEq

/-- Four named colors for the finite counterexample. -/
inductive CounterColor : Type
  | red
  | blue
  | green
  | yellow
  deriving DecidableEq

open CounterVertex CounterColor

/-- A star centered at `center`. -/
def counterAdj : CounterVertex → CounterVertex → Prop
  | center, w1 => True
  | w1, center => True
  | center, w2 => True
  | w2, center => True
  | center, w3 => True
  | w3, center => True
  | center, w4 => True
  | w4, center => True
  | _, _ => False

/-- The center is not red or blue, so the red/blue components of its leaves stay
separated. -/
def counterColoring : CounterVertex → CounterColor
  | center => green
  | w1 => red
  | w2 => blue
  | w3 => red
  | w4 => yellow

def counterKempeChain : Set CounterVertex :=
  vertexKempeChain counterAdj counterColoring red blue w1

lemma counter_no_red_blue_edge (u v : CounterVertex) :
    ¬ twoColorSubgraph counterAdj counterColoring red blue u v := by
  cases u <;> cases v <;> simp [twoColorSubgraph, counterAdj, counterColoring]

lemma counter_red_blue_reachable_eq {u v : CounterVertex}
    (h : Relation.ReflTransGen
      (twoColorSubgraph counterAdj counterColoring red blue) u v) :
    u = v := by
  induction h with
  | refl => rfl
  | tail _ hstep _ih =>
      exact False.elim (counter_no_red_blue_edge _ _ hstep)

lemma w3_not_in_counterKempeChain : w3 ∉ counterKempeChain := by
  intro h
  unfold counterKempeChain vertexKempeChain at h
  have h_eq : w1 = w3 := counter_red_blue_reachable_eq h
  cases h_eq

noncomputable def swappedCounterColoring : CounterVertex → CounterColor :=
  kempeSwitch counterColoring counterKempeChain red blue

theorem w3_still_red_after_swap :
    swappedCounterColoring w3 = red := by
  simp [swappedCounterColoring, w3_not_in_counterKempeChain, counterColoring]

theorem red_not_free_after_swap :
    ∃ w, counterAdj center w ∧ swappedCounterColoring w = red := by
  exact ⟨w3, by simp [counterAdj], w3_still_red_after_swap⟩

/-- The naive claim that a Kempe switch always frees the chosen color is false,
even in a five-vertex star. -/
theorem naive_kempe_claim_is_false :
    ¬ (∀ (adj : CounterVertex → CounterVertex → Prop)
        (color : CounterVertex → CounterColor)
        (v seed : CounterVertex) (α β : CounterColor),
        let K := vertexKempeChain adj color α β seed
        let color' := kempeSwitch color K α β
        ∀ w, adj v w → color' w ≠ α) := by
  intro h
  have hfree := h counterAdj counterColoring center w1 red blue
  have hw3_not_red : swappedCounterColoring w3 ≠ red := by
    exact hfree w3 (by simp [counterAdj])
  exact hw3_not_red w3_still_red_after_swap

end Counterexample

end Mettapedia.GraphTheory.FourColor.VertexKempe
