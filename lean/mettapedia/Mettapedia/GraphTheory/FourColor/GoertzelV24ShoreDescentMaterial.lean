import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteTreeInterfacePumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphereCutMaterial

/-!
# Strict material along a decomposition descent

A branch-decomposition tree labelled by edge shores loses at least one edge at
every step, because the discarded sibling subtree carries a leaf of its own.
Along one descent the shores are therefore strictly nested, and two nodes at
tree distance `s` bound shores differing by at least `s` edges.

Combined with the cubic material count, that turns the strict-material clause
of a sphere-cut supply into finite bookkeeping: if two comparable nodes carry
the same typed state *and the same node depth modulo* `6w+1`, then they are at
least `6w+1` steps apart, the slab between their shores holds more than `6w`
edges, and some vertex lies strictly inside the slab.

Nothing here uses planarity, a noose, or the existence of the decomposition;
it is the accounting that the supplier may then rely on.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ShoreDescentMaterial

open GoertzelV24FiniteTreeInterfacePumping
open GoertzelV24FiniteTreeInterfacePumping.DecompTree
open GoertzelV24SphereCutMaterial
open scoped Classical

variable {α : Type*}

/-- The label at the root of a decomposition tree, if there is one. -/
def rootLabel : DecompTree α → Option α
  | .tip => none
  | .node a _ _ => some a

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A decomposition tree whose labels are edge shores that shrink strictly at
every step.  This is the tree-side content of "the discarded sibling subtree
contains a leaf". -/
def StrictShoreTree : DecompTree (Finset E) → Prop
  | .tip => True
  | .node a l r =>
      (∀ b ∈ rootLabel l, b ⊂ a) ∧ (∀ b ∈ rootLabel r, b ⊂ a) ∧
        StrictShoreTree l ∧ StrictShoreTree r

/-- Along a descent of a strict shore tree, consecutive labels strictly
shrink. -/
theorem step_of_onPath {t : DecompTree (Finset E)} {p : List (Finset E)}
    (hpath : OnPath t p) :
    StrictShoreTree t → ∀ k : ℕ, k + 1 < p.length →
      p.getD (k + 1) ∅ ⊂ p.getD k ∅ := by
  induction hpath with
  | tip => intro _ k hk; simp at hk
  | @left a l r xs hleft ih =>
      rintro ⟨hl, -, hlt, -⟩ k hk
      rcases k with _ | m
      · rcases xs with _ | ⟨b, ys⟩
        · simp at hk
        · have hroot : rootLabel l = some b := by
            cases hleft with
            | left _ => rfl
            | right _ => rfl
          simpa using hl b (by simp [hroot])
      · simp only [List.getD_cons_succ]
        exact ih hlt m (by simpa using hk)
  | @right a l r xs hright ih =>
      rintro ⟨-, hr, -, hrt⟩ k hk
      rcases k with _ | m
      · rcases xs with _ | ⟨b, ys⟩
        · simp at hk
        · have hroot : rootLabel r = some b := by
            cases hright with
            | left _ => rfl
            | right _ => rfl
          simpa using hr b (by simp [hroot])
      · simp only [List.getD_cons_succ]
        exact ih hrt m (by simpa using hk)

/-! ## Distance in the tree is material in the slab -/

omit [Fintype E] in
/-- A strictly shrinking finite sequence of finite sets loses at least one
element per step. -/
theorem subset_and_card_add_le_of_step {f : ℕ → Finset E} {n : ℕ}
    (hstep : ∀ k, k + 1 < n → f (k + 1) ⊂ f k)
    {i j : ℕ} (hj : j < n) (hij : i < j) :
    f j ⊆ f i ∧ (f j).card + (j - i) ≤ (f i).card := by
  induction j with
  | zero => omega
  | succ m ih =>
      have hstepm : f (m + 1) ⊂ f m := hstep m hj
      have hcardStep : (f (m + 1)).card < (f m).card :=
        Finset.card_lt_card hstepm
      rcases Nat.lt_or_ge i m with hlt | hge
      · obtain ⟨hsub, hcard⟩ := ih (by omega) hlt
        refine ⟨hstepm.1.trans hsub, ?_⟩
        have hmi : m + 1 - i = (m - i) + 1 := by omega
        omega
      · have him : i = m := by omega
        subst him
        exact ⟨hstepm.1, by omega⟩

/-- Two comparable nodes of a strict shore tree bound nested shores whose
slab holds at least their tree distance many edges. -/
theorem card_slab_of_onPath {t : DecompTree (Finset E)} {p : List (Finset E)}
    (hpath : OnPath t p) (hstrict : StrictShoreTree t)
    {i j : ℕ} (hj : j < p.length) (hij : i < j) :
    p.getD j ∅ ⊆ p.getD i ∅ ∧
      (j - i) ≤ (p.getD i ∅ \ p.getD j ∅).card := by
  classical
  obtain ⟨hsub, hcard⟩ :=
    subset_and_card_add_le_of_step (f := fun k => p.getD k ∅)
      (step_of_onPath hpath hstrict) hj hij
  refine ⟨hsub, ?_⟩
  have hinter : p.getD j ∅ ∩ p.getD i ∅ = p.getD j ∅ :=
    Finset.inter_eq_left.2 hsub
  rw [Finset.card_sdiff, hinter]
  omega

/-! ## The strict-material clause -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Spaced repetition forces strict material.**  Two comparable nodes of a
strict shore tree that are at least `6w+1` steps apart, in a cubic incidence
structure whose shore middle sets have at most `w` vertices, bound a slab
containing a vertex all of whose edges lie in the slab. -/
theorem exists_strict_slab_vertex_of_spaced
    (incident : V → E → Prop) (w : ℕ)
    {t : DecompTree (Finset E)} {p : List (Finset E)}
    (hpath : OnPath t p) (hstrict : StrictShoreTree t)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hcubic : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ 3)
    (hmiddle : ∀ k, k < p.length →
      (middleVertices incident (p.getD k ∅)).card ≤ w)
    {i j : ℕ} (hj : j < p.length) (hij : i < j)
    (hspaced : 6 * w + 1 ≤ j - i) :
    ∃ vertex : V,
      (∃ edge ∈ p.getD i ∅ \ p.getD j ∅, incident vertex edge) ∧
        ∀ edge, incident vertex edge → edge ∈ p.getD i ∅ \ p.getD j ∅ := by
  classical
  obtain ⟨-, hslab⟩ := card_slab_of_onPath hpath hstrict hj hij
  refine exists_strict_slab_vertex_of_cubic incident (p.getD j ∅)
    (p.getD i ∅) w hedge hcubic (hmiddle j hj) (hmiddle i (by omega)) ?_
  omega

/-- **The finite-state form.**  Equal typed states *and* equal node depth
modulo `6w+1` at two comparable nodes produce a strict slab vertex.  This is
the statement that replaces the pictorial strict-material clause of a
sphere-cut supply. -/
theorem exists_strict_slab_vertex_of_phase_repeat
    (incident : V → E → Prop) (w : ℕ)
    {t : DecompTree (Finset E)} {p : List (Finset E)}
    (hpath : OnPath t p) (hstrict : StrictShoreTree t)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hcubic : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ 3)
    (hmiddle : ∀ k, k < p.length →
      (middleVertices incident (p.getD k ∅)).card ≤ w)
    {i j : ℕ} (hj : j < p.length) (hij : i < j)
    (hphase : i % (6 * w + 1) = j % (6 * w + 1)) :
    ∃ vertex : V,
      (∃ edge ∈ p.getD i ∅ \ p.getD j ∅, incident vertex edge) ∧
        ∀ edge, incident vertex edge → edge ∈ p.getD i ∅ \ p.getD j ∅ :=
  exists_strict_slab_vertex_of_spaced incident w hpath hstrict hedge hcubic
    hmiddle hj hij (period_le_sub_of_mod_eq hij hphase)

/-! ## The replacement obligation, localised -/

/-- **A supplier only has to splice at a strict slab vertex.**  On a strict
shore tree with bounded middle sets, augmenting the typed state by node depth
modulo `6w+1` makes every repeated state on a descent exhibit a vertex lying
strictly between the two nested shores.  So the pictorial strict-material
clause of a sphere-cut supply is discharged, and what remains of the
replacement field is the purely local splice at that vertex. -/
theorem replace_of_local_splice
    {Inst : Type*} {size : Inst → ℕ} {Target : Inst → Prop} {X : Inst}
    {Q : Type*} (state : Finset E → Q)
    (incident : V → E → Prop) (w : ℕ)
    {t : DecompTree (Finset E)} {p : List (Finset E)}
    (hpath : OnPath t p) (hstrict : StrictShoreTree t)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hcubic : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ 3)
    (hmiddle : ∀ k, k < p.length →
      (middleVertices incident (p.getD k ∅)).card ≤ w)
    (hsplice : ∀ outer inner : Finset E, inner ⊆ outer →
      state outer = state inner →
      (∃ vertex : V,
        (∃ edge ∈ outer \ inner, incident vertex edge) ∧
          ∀ edge, incident vertex edge → edge ∈ outer \ inner) →
      ∃ Y, Target Y ∧ size Y < size X)
    {i j : ℕ} (hj : j < p.length) (hij : i < j)
    (hphase : i % (6 * w + 1) = j % (6 * w + 1))
    (hstate : state (p.getD i ∅) = state (p.getD j ∅)) :
    ∃ Y, Target Y ∧ size Y < size X := by
  refine hsplice (p.getD i ∅) (p.getD j ∅)
    (card_slab_of_onPath hpath hstrict hj hij).1 hstate ?_
  exact exists_strict_slab_vertex_of_phase_repeat incident w hpath hstrict
    hedge hcubic hmiddle hj hij hphase

end GoertzelV24ShoreDescentMaterial

end Mettapedia.GraphTheory.FourColor
