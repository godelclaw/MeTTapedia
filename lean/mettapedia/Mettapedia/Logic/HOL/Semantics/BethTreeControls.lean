import Mettapedia.Logic.HOL.Semantics.BethTree
import Mettapedia.Logic.HOL.PropositionalSlice

/-!
# Without fairness the tree truth lemma fails

The canonical tree of Henkin runs (`BethTree.theory`) is defined for any
schedules; fairness enters only in the cover clauses.  This file shows that it
cannot be dropped.

The starving pair schedule reads the firing sequence of the least-first run
`PriorityFairness.Controls.starvingRun` through an encoding in which item `0`
is the pair `(⊤, ⊤)` and item `1` the pair `(p, q)` of two propositional
atoms.  The run keeps item `1` pending forever and never fires it
(`Controls.starves`), so it is not a service of its pending items
(`EligibleService.starvingRun_not_service`).

* `starving_never_serves`: the pair `(p, q)` is never served.
* `not_isBar_pairBar_starving`: the nodes past a depth serving `(p, q)` do not
  bar the root.
* `starving_or_clause_fails`: over the theory `{p ∨ q}`, the root proves
  `p ∨ q`, yet no bar of the root decides it.  The disjunction clause of the
  truth lemma (`BethTree.provable_or_iff_bar`) fails.

The proof follows the path that always assumes `⊤`: along it every added
formula is `⊤`, and a classical valuation shows that `{p ∨ q, ⊤}` proves
neither `p` nor `q`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

namespace BethTree

namespace Controls

open PropositionalSlice ClosedTheorySet BethHenkin Mettapedia.Logic.HOL.WithParams
open Mettapedia.GSLT.Dynamics.PriorityFairness

/-- The first atom. -/
abbrev p : ClosedFormula (WithParams Atom) := embedP (.atom 0)

/-- The second atom. -/
abbrev q : ClosedFormula (WithParams Atom) := embedP (.atom 1)

/-- The theory `{p ∨ q}`. -/
def disjTheory : ClosedTheorySet (WithParams Atom) := {.or p q}

theorem paramFree_disjTheory : ParamFree disjTheory := by
  intro ψ hψ σ k
  rw [Set.mem_singleton_iff.mp hψ]
  exact noConstOccurrence_param_of_ge k _ (Nat.zero_le k)

/-- The obligations of the starving run: item `1` is the pair `(p, q)`, every
other item the pair `(⊤, ⊤)`. -/
def obligation : ℕ → ClosedFormulaPair Atom
  | 1 => (p, q)
  | _ => (.top, .top)

/-- **The starving schedules**: pairs read off the firing sequence of the
starving run, and the trivial body. -/
def starving : Schedules Atom where
  pair n := obligation (Controls.starvingRun.fired n)
  body _ := ⟨.prop, .top⟩

theorem starving_pair (n : ℕ) : starving.pair n = (.top, .top) := rfl

/-- The pair `(p, q)`, the obligation of the item the run keeps pending, is
never served. -/
theorem starving_never_serves (n : ℕ) : starving.pair n ≠ (p, q) := by
  rw [starving_pair]
  intro h
  injection h with h₁
  cases h₁

/-- Item `1` stays pending forever and is never fired. -/
theorem starving_item_pending : (∀ t, 1 ∈ Controls.starvingRun.pending t) ∧
    ∀ t, Controls.starvingRun.fired t ≠ 1 :=
  Controls.starves

/-- **The bar property fails**: the nodes past a depth serving `(p, q)` do not
bar the root. -/
theorem not_isBar_pairBar_starving :
    ¬ Bar.IsBar ([] : List (Move Atom)) (pairBar starving [] (p, q)) := by
  intro hB
  obtain ⟨t, ⟨_, n, _, _, hn⟩, _⟩ := hB.2 (fun _ => default) fun i hi => absurd hi (by simp)
  exact starving_never_serves n hn

/-- Every formula added along the path that always plays the default move is
`⊤`. -/
theorem added_replicate_default :
    ∀ (k : ℕ) (φ : ClosedFormula (WithParams Atom)),
      φ ∈ added disjTheory starving (List.replicate k default) → φ = .top := by
  classical
  intro k
  induction k with
  | zero => intro φ hφ; cases hφ
  | succ k ih =>
      intro φ hφ
      rw [List.replicate_succ', added_append_singleton] at hφ
      unfold step witnessStep decideStep assumeStep at hφ
      simp only [List.mem_cons] at hφ
      rcases hφ with h | h | h | h
      · rw [h]
        split_ifs <;> rfl
      · rw [h, starving_pair]
        split_ifs <;> rfl
      · rw [h]
        split_ifs <;> rfl
      · exact ih φ h

/-- The classical valuation with `p` false and `q` true. -/
def vq : ℕ → Prop := fun a => a = 1

/-- The classical valuation with `p` true and `q` false. -/
def vp : ℕ → Prop := fun a => a = 0

/-- A theory whose members are `p ∨ q` or `⊤` proves an atom only if the atom is
true at every valuation making `p ∨ q` true. -/
theorem denote_atom_of_provable {Γ : ClosedTheorySet (WithParams Atom)}
    (hΓ : ∀ ψ ∈ Γ, ψ = .or p q ∨ ψ = .top) (v : ℕ → Prop) (hv : v 0 ∨ v 1) (a : ℕ)
    (h : Provable (Const := WithParams Atom) Γ (embedP (.atom a))) : v a := by
  obtain ⟨Δ, hΔ, d⟩ := h
  have := Soundness.extDerivation_sound d (M := standardModel v)
    (ρ := fun x => nomatch x) (standardModel_extensional v) (fun x => nomatch x)
    (fun γ hγ => by
      rcases hΓ γ (hΔ γ hγ) with rfl | rfl
      · exact hv
      · trivial)
  exact this

/-- **Without fairness the disjunction clause fails.** Over `{p ∨ q}` with the
starving schedules, the root proves `p ∨ q`, but no bar of the root decides
it. -/
theorem starving_or_clause_fails :
    Provable (Const := WithParams Atom) (theory disjTheory starving []) (.or p q) ∧
      ¬ ∃ B, Bar.IsBar ([] : List (Move Atom)) B ∧ ∀ t ∈ B,
        Provable (Const := WithParams Atom) (theory disjTheory starving t) p ∨
          Provable (Const := WithParams Atom) (theory disjTheory starving t) q := by
  refine ⟨provable_of_mem (show _ ∈ withList disjTheory _ from Or.inl rfl), ?_⟩
  rintro ⟨B, hB, hdec⟩
  obtain ⟨t, htB, hpt⟩ := hB.2 (fun _ => default) fun i hi => absurd hi (by simp)
  have ht : t = List.replicate t.length default :=
    List.ext_getElem (by simp) fun i h₁ _ => by rw [hpt i h₁]; simp
  have hmem : ∀ ψ ∈ theory disjTheory starving t, ψ = .or p q ∨ ψ = .top := by
    intro ψ hψ
    rcases hψ with hψ | hψ
    · exact Or.inl (Set.mem_singleton_iff.mp hψ)
    · rw [ht] at hψ
      exact Or.inr (added_replicate_default _ ψ hψ)
  rcases hdec t htB with h | h
  · exact absurd (denote_atom_of_provable hmem vq (Or.inr rfl) 0 h) (by simp [vq])
  · exact absurd (denote_atom_of_provable hmem vp (Or.inl rfl) 1 h) (by simp [vp])

end Controls

end BethTree

end Mettapedia.Logic.HOL
