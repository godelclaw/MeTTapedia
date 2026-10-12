import Mettapedia.SetTheory.OpenTower.Potentialism.Frames

/-!
# Modal axioms on the four frames

A propositional modal formula is an atom, a negation, a conjunction or a box.
A valuation sends each atom to a predicate of worlds. `□φ` holds at a world when
`φ` holds at every accessible world, and `◇φ` is `¬□¬φ`.

The linearity schema used here is the two-disjunct diamond form
`(◇φ ∧ ◇ψ) → ◇((φ ∧ ◇ψ) ∨ (ψ ∧ ◇φ))`. The three-disjunct form follows from it.
The directedness schema is `◇□φ → □◇φ`. Both are read at every world under every
valuation.

On the closed sets, and on the stages of a tower, K, T, 4 and the
linearity schema are valid, and so is the directedness schema. Those are
lower bounds. The schema `◇□φ → φ` fails on the closed sets, at the empty
set, for the valuation "the empty set is a member". On the admitted theories
K, T, and 4 are valid, and the directedness schema fails at the theory of
extensionality, the empty set, union, and power, for the valuation "the
theory contains the well-founded theory". That refutation is one world with
two incompatible extensions. It is separate from the exact logic of the
closed sets, which is not identified here.

Membership of the empty set is a pure button on the closed sets and not a
switch. A transitive total frame carries no two independently necessary pure
buttons. The statement that every formula refuted on some finite chain
`(Fin n, · ≤ ·)` is refuted on the closed sets, given cofinal inaccessibles
and a set to start a tower from, is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Potentialism

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.CarveOuts
open Mettapedia.SetTheory.OpenTower.InternalTower
open Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories
open Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
open Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
open scoped ZFSet
open Classical

universe u

/-- A propositional modal formula. -/
inductive Formula : Type where
  | atom : ℕ → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | box : Formula → Formula
  deriving DecidableEq

/-- The atom `0` is not the atom `1`, and it is not its own negation. -/
example : Formula.atom 0 ≠ Formula.atom 1 ∧ Formula.atom 0 ≠ Formula.neg (Formula.atom 0) := by
  decide

namespace Formula

def diamond (φ : Formula) : Formula := neg (box (neg φ))

/-- Diamond unfolds to the negation of a boxed negation. -/
example : diamond (atom 0) = neg (box (neg (atom 0))) := rfl

/-- Diamond of an atom is not that atom. -/
example : diamond (atom 0) ≠ atom 0 := by decide

def disj (φ ψ : Formula) : Formula := neg (conj (neg φ) (neg ψ))

/-- Disjunction unfolds to the negation of a conjunction of negations. -/
example : disj (atom 0) (atom 1) = neg (conj (neg (atom 0)) (neg (atom 1))) := rfl

/-- A disjunction of atoms is not an atom. -/
example : disj (atom 0) (atom 1) ≠ atom 0 := by decide

def impl (φ ψ : Formula) : Formula := disj (neg φ) ψ

/-- Implication unfolds to a disjunction. -/
example : impl (atom 0) (atom 1) = disj (neg (atom 0)) (atom 1) := rfl

/-- An implication of atoms is not an atom. -/
example : impl (atom 0) (atom 1) ≠ atom 0 := by decide

/-- `(◇φ ∧ ◇ψ) → ◇((φ ∧ ◇ψ) ∨ (ψ ∧ ◇φ))`. -/
@[reducible] def axiomDot3 (φ ψ : Formula) : Formula :=
  impl (conj (diamond φ) (diamond ψ))
    (diamond (disj (conj φ (diamond ψ)) (conj ψ (diamond φ))))

/-- The two-disjunct linearity schema unfolds to that implication. -/
example : axiomDot3 (atom 0) (atom 1) =
    impl (conj (diamond (atom 0)) (diamond (atom 1)))
      (diamond (disj (conj (atom 0) (diamond (atom 1)))
        (conj (atom 1) (diamond (atom 0))))) := rfl

/-- The two-disjunct linearity schema is not an atom. -/
example : axiomDot3 (atom 0) (atom 1) ≠ atom 0 := by decide

/-- `◇φ ∧ ◇ψ → (◇(φ ∧ ◇ψ) ∨ ◇(φ ∧ ψ) ∨ ◇(ψ ∧ ◇φ))`. -/
@[reducible] def axiomDot3Lowe (φ ψ : Formula) : Formula :=
  impl (conj (diamond φ) (diamond ψ))
    (disj (diamond (conj φ (diamond ψ)))
      (disj (diamond (conj φ ψ)) (diamond (conj ψ (diamond φ)))))

/-- The three-disjunct linearity schema unfolds to that implication. -/
example : axiomDot3Lowe (atom 0) (atom 1) =
    impl (conj (diamond (atom 0)) (diamond (atom 1)))
      (disj (diamond (conj (atom 0) (diamond (atom 1))))
        (disj (diamond (conj (atom 0) (atom 1)))
          (diamond (conj (atom 1) (diamond (atom 0)))))) := rfl

/-- The three-disjunct linearity schema is not an atom. -/
example : axiomDot3Lowe (atom 0) (atom 1) ≠ atom 0 := by decide

/-- `◇□φ → □◇φ`. -/
@[reducible] def axiomDot2 (φ : Formula) : Formula :=
  impl (diamond (box φ)) (box (diamond φ))

/-- The directedness schema unfolds to that implication. -/
example : axiomDot2 (atom 0) = impl (diamond (box (atom 0))) (box (diamond (atom 0))) := rfl

/-- The directedness schema is not an atom. -/
example : axiomDot2 (atom 0) ≠ atom 0 := by decide

/-- `□(φ → ψ) → (□φ → □ψ)`. -/
@[reducible] def axiomK (φ ψ : Formula) : Formula :=
  impl (box (impl φ ψ)) (impl (box φ) (box ψ))

/-- The K schema unfolds to that implication. -/
example : axiomK (atom 0) (atom 1) =
    impl (box (impl (atom 0) (atom 1))) (impl (box (atom 0)) (box (atom 1))) := rfl

/-- The K schema is not an atom. -/
example : axiomK (atom 0) (atom 1) ≠ atom 0 := by decide

/-- `□φ → φ`. -/
@[reducible] def axiomT (φ : Formula) : Formula := impl (box φ) φ

/-- The T schema unfolds to an implication from a box. -/
example : axiomT (atom 0) = impl (box (atom 0)) (atom 0) := rfl

/-- The T schema of an atom is not that atom. -/
example : axiomT (atom 0) ≠ atom 0 := by decide

/-- The two-disjunct linearity schema is not the T schema. -/
example : axiomDot3 (atom 0) (atom 1) ≠ axiomT (atom 0) := by decide

/-- The three-disjunct linearity schema is not the T schema. -/
example : axiomDot3Lowe (atom 0) (atom 1) ≠ axiomT (atom 0) := by decide

/-- The directedness schema is not the T schema. -/
example : axiomDot2 (atom 0) ≠ axiomT (atom 0) := by decide

/-- The K schema is not the T schema. -/
example : axiomK (atom 0) (atom 1) ≠ axiomT (atom 0) := by decide

/-- `□φ → □□φ`. -/
@[reducible] def axiomFour (φ : Formula) : Formula := impl (box φ) (box (box φ))

/-- The 4 schema unfolds to an implication into a double box. -/
example : axiomFour (atom 0) = impl (box (atom 0)) (box (box (atom 0))) := rfl

/-- The 4 schema is not the T schema. -/
example : axiomFour (atom 0) ≠ axiomT (atom 0) := by decide

/-- `◇□φ → φ`. -/
@[reducible] def axiomB (φ : Formula) : Formula := impl (diamond (box φ)) φ

/-- The B schema unfolds to an implication from a diamond of a box. -/
example : axiomB (atom 0) = impl (diamond (box (atom 0))) (atom 0) := rfl

/-- The B schema is not the T schema. -/
example : axiomB (atom 0) ≠ axiomT (atom 0) := by decide

end Formula

/-- Forcing at one world. -/
def Forces {W : Type u} (R : W → W → Prop) (V : ℕ → W → Prop) (w : W) : Formula → Prop
  | .atom n => V n w
  | .neg φ => ¬ Forces R V w φ
  | .conj φ ψ => Forces R V w φ ∧ Forces R V w ψ
  | .box φ => ∀ w', R w w' → Forces R V w' φ

/-- A true atom is forced; a false atom is not. -/
example :
    Forces (fun (_ _ : Unit) => False) (fun _ _ => True) () (Formula.atom 0) ∧
      ¬ Forces (fun (_ _ : Unit) => False) (fun _ _ => False) () (Formula.atom 0) := by
  constructor
  · exact trivial
  · exact not_false

theorem forces_atom {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop} {w : W} {n : ℕ} :
    Forces R V w (.atom n) ↔ V n w := Iff.rfl

theorem forces_neg {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop} {w : W} {φ : Formula} :
    Forces R V w (.neg φ) ↔ ¬ Forces R V w φ := Iff.rfl

theorem forces_conj {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop} {w : W}
    {φ ψ : Formula} :
    Forces R V w (.conj φ ψ) ↔ Forces R V w φ ∧ Forces R V w ψ := Iff.rfl

theorem forces_box {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop} {w : W} {φ : Formula} :
    Forces R V w (.box φ) ↔ ∀ w', R w w' → Forces R V w' φ := Iff.rfl

theorem forces_diamond {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop} {w : W}
    {φ : Formula} :
    Forces R V w (Formula.diamond φ) ↔ ∃ w', R w w' ∧ Forces R V w' φ := by
  simp only [Formula.diamond, forces_neg, forces_box]
  constructor
  · intro h
    by_contra hnone
    apply h
    intro w' hw' hφ
    exact hnone ⟨w', hw', hφ⟩
  · intro ⟨w', hw', hφ⟩ h
    exact h w' hw' hφ

theorem forces_disj {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop} {w : W}
    {φ ψ : Formula} :
    Forces R V w (Formula.disj φ ψ) ↔ Forces R V w φ ∨ Forces R V w ψ := by
  simp only [Formula.disj, forces_neg, forces_conj]
  constructor
  · intro h
    by_cases hφ : Forces R V w φ
    · exact Or.inl hφ
    · exact Or.inr (by
        by_contra hψ
        exact h ⟨hφ, hψ⟩)
  · intro h hn
    rcases h with hφ | hψ
    · exact hn.1 hφ
    · exact hn.2 hψ

theorem forces_impl {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop} {w : W}
    {φ ψ : Formula} :
    Forces R V w (Formula.impl φ ψ) ↔ (Forces R V w φ → Forces R V w ψ) := by
  simp only [Formula.impl, forces_disj, forces_neg]
  constructor
  · intro h hφ
    rcases h with hneg | hψ
    · exact absurd hφ hneg
    · exact hψ
  · intro h
    by_cases hφ : Forces R V w φ
    · exact Or.inr (h hφ)
    · exact Or.inl hφ

/-- A formula valid on a frame holds at every world under every valuation. -/
def Valid {W : Type u} (R : W → W → Prop) (φ : Formula) : Prop :=
  ∀ (V : ℕ → W → Prop) (w : W), Forces R V w φ

/-- On the one-world reflexive frame, `p → p` is valid and `p` is not. -/
example :
    Valid (fun (_ _ : Unit) => True) (Formula.impl (Formula.atom 0) (Formula.atom 0)) ∧
      ¬ Valid (fun (_ _ : Unit) => True) (Formula.atom 0) := by
  constructor
  · intro V w
    rw [forces_impl]
    exact id
  · intro h
    have := h (fun _ _ => False) ()
    rw [forces_atom] at this
    exact this

/-! ## Axioms that hold on every frame, or on a reflexive, transitive, directed or linear one -/

theorem valid_K {W : Type u} (R : W → W → Prop) (φ ψ : Formula) :
    Valid R (Formula.axiomK φ ψ) := by
  intro V w
  rw [forces_impl, forces_box, forces_impl, forces_box, forces_box]
  intro himpl hφ w' hw'
  have step : Forces R V w' φ → Forces R V w' ψ := (forces_impl.mp (himpl w' hw'))
  exact step (hφ w' hw')

theorem valid_mp {W : Type u} {R : W → W → Prop} {φ ψ : Formula}
    (himpl : Valid R (Formula.impl φ ψ)) (hφ : Valid R φ) : Valid R ψ := by
  intro V w
  exact (forces_impl.mp (himpl V w)) (hφ V w)

theorem valid_necessitation {W : Type u} {R : W → W → Prop} {φ : Formula}
    (hφ : Valid R φ) : Valid R (Formula.box φ) := by
  intro V w
  rw [forces_box]
  intro w' _
  exact hφ V w'

theorem valid_T_of_refl {W : Type u} {R : W → W → Prop} (hrefl : ∀ w, R w w) (φ : Formula) :
    Valid R (Formula.axiomT φ) := by
  intro V w
  rw [forces_impl, forces_box]
  intro h
  exact h w (hrefl w)

theorem valid_four_of_trans {W : Type u} {R : W → W → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c) (φ : Formula) :
    Valid R (Formula.axiomFour φ) := by
  intro V w
  rw [forces_impl, forces_box]
  intro hbox
  rw [forces_box]
  intro w' hw'
  rw [forces_box]
  intro w'' hw''
  exact hbox w'' (htrans w w' w'' hw' hw'')

theorem valid_dot2_of_directed {W : Type u} {R : W → W → Prop}
    (hdir : ∀ a b, ∃ c, R a c ∧ R b c) (φ : Formula) :
    Valid R (Formula.axiomDot2 φ) := by
  intro V w
  rw [forces_impl, forces_diamond]
  intro ⟨a, hwa, hbox⟩
  rw [forces_box] at hbox
  rw [forces_box]
  intro b hwb
  rw [forces_diamond]
  obtain ⟨c, hac, hbc⟩ := hdir a b
  exact ⟨c, hbc, hbox c hac⟩

/-- **The two-disjunct linearity schema is valid on a total frame.** -/
theorem valid_dot3_of_total {W : Type u} {R : W → W → Prop}
    (htotal : ∀ a b, R a b ∨ R b a) (φ ψ : Formula) :
    Valid R (Formula.axiomDot3 φ ψ) := by
  intro V w
  rw [forces_impl, forces_conj, forces_diamond, forces_diamond]
  intro ⟨⟨a, hwa, hφ⟩, ⟨b, hwb, hψ⟩⟩
  rw [forces_diamond]
  rcases htotal a b with hab | hba
  · refine ⟨a, hwa, ?_⟩
    rw [forces_disj]
    refine Or.inl ?_
    rw [forces_conj, forces_diamond]
    exact ⟨hφ, b, hab, hψ⟩
  · refine ⟨b, hwb, ?_⟩
    rw [forces_disj]
    refine Or.inr ?_
    rw [forces_conj, forces_diamond]
    exact ⟨hψ, a, hba, hφ⟩

theorem forces_dot3Lowe_of_forces_dot3 {W : Type u} {R : W → W → Prop} {V : ℕ → W → Prop}
    {w : W} {φ ψ : Formula} (h : Forces R V w (Formula.axiomDot3 φ ψ)) :
    Forces R V w (Formula.axiomDot3Lowe φ ψ) := by
  rw [forces_impl] at h ⊢
  intro hand
  have hdiam : Forces R V w (Formula.diamond
      (Formula.disj (Formula.conj φ (Formula.diamond ψ))
        (Formula.conj ψ (Formula.diamond φ)))) := h hand
  rw [forces_diamond] at hdiam
  obtain ⟨t, ht, hor⟩ := hdiam
  rw [forces_disj] at hor
  rw [forces_disj, forces_disj]
  rcases hor with hL | hR
  · exact Or.inl (forces_diamond.mpr ⟨t, ht, hL⟩)
  · exact Or.inr (Or.inr (forces_diamond.mpr ⟨t, ht, hR⟩))

/-- **The three-disjunct linearity schema is valid on a total frame.** -/
theorem valid_dot3Lowe_of_total {W : Type u} {R : W → W → Prop}
    (htotal : ∀ a b, R a b ∨ R b a) (φ ψ : Formula) :
    Valid R (Formula.axiomDot3Lowe φ ψ) := by
  intro V w
  exact forces_dot3Lowe_of_forces_dot3 (valid_dot3_of_total htotal φ ψ V w)

/-! ## The closed sets and a tower of stages -/

theorem valid_K_closed (φ ψ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) (Formula.axiomK φ ψ) :=
  valid_K _ φ ψ

theorem valid_T_closed (φ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) (Formula.axiomT φ) :=
  valid_T_of_refl (fun A => closedFrame_refl A) φ

theorem valid_four_closed (φ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) (Formula.axiomFour φ) :=
  valid_four_of_trans (R := fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1)
    (fun _ _ _ hAB hBC => closedFrame_trans hAB hBC) φ

theorem valid_dot2_closed (φ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) (Formula.axiomDot2 φ) :=
  valid_dot2_of_directed (fun A B => by
    obtain ⟨C, hA, hB⟩ := closedFrame_directed A B
    exact ⟨C, hA, hB⟩) φ

/-- **The linearity schema holds on the closed sets, for every valuation.** -/
theorem valid_dot3_closed (φ ψ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) (Formula.axiomDot3 φ ψ) :=
  valid_dot3_of_total (fun A B => closedFrame_linear A B) φ ψ

theorem valid_dot3Lowe_closed (φ ψ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1)
      (Formula.axiomDot3Lowe φ ψ) :=
  valid_dot3Lowe_of_total (fun A B => closedFrame_linear A B) φ ψ

theorem valid_K_stageChain (s : ℕ → ZFSet.{u}) (φ ψ : Formula) :
    Valid (fun m n => s m ⊆ s n) (Formula.axiomK φ ψ) :=
  valid_K _ φ ψ

theorem valid_T_stageChain {s : ℕ → ZFSet.{u}} (chain : StageChain s) (φ : Formula) :
    Valid (fun m n => s m ⊆ s n) (Formula.axiomT φ) :=
  valid_T_of_refl (fun n => stageChain_frame_refl chain n) φ

theorem valid_four_stageChain {s : ℕ → ZFSet.{u}} (chain : StageChain s) (φ : Formula) :
    Valid (fun m n => s m ⊆ s n) (Formula.axiomFour φ) :=
  valid_four_of_trans (R := fun m n => s m ⊆ s n)
    (fun _ _ _ hmn hnk => stageChain_frame_trans chain hmn hnk) φ

theorem valid_dot2_stageChain {s : ℕ → ZFSet.{u}} (chain : StageChain s) (φ : Formula) :
    Valid (fun m n => s m ⊆ s n) (Formula.axiomDot2 φ) :=
  valid_dot2_of_directed (fun m n => by
    obtain ⟨k, hm, hn⟩ := stageChain_frame_directed chain m n
    exact ⟨k, hm, hn⟩) φ

/-- **The linearity schema holds on every tower of stages, for every valuation.** -/
theorem valid_dot3_stageChain {s : ℕ → ZFSet.{u}} (chain : StageChain s) (φ ψ : Formula) :
    Valid (fun m n => s m ⊆ s n) (Formula.axiomDot3 φ ψ) :=
  valid_dot3_of_total (fun m n => stageChain_frame_linear chain m n) φ ψ

theorem valid_dot3Lowe_stageChain {s : ℕ → ZFSet.{u}} (chain : StageChain s) (φ ψ : Formula) :
    Valid (fun m n => s m ⊆ s n) (Formula.axiomDot3Lowe φ ψ) :=
  valid_dot3Lowe_of_total (fun m n => stageChain_frame_linear chain m n) φ ψ

/-- **`◇□φ → φ` fails on the closed sets.** At the empty set, under the valuation
"the empty set is a member", the hereditarily finite sets are an extension at
which that statement is necessary, and the statement itself fails. -/
theorem not_valid_axiomB_closed :
    ¬ Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1)
        (Formula.axiomB (Formula.atom 0)) := by
  intro hval
  let V : ℕ → {U : ZFSet.{u} // Closed U} → Prop :=
    fun n A => n = 0 ∧ (∅ : ZFSet.{u}) ∈ A.1
  let w0 : {U : ZFSet.{u} // Closed U} := ⟨∅, closed_empty⟩
  let wΩ : {U : ZFSet.{u} // Closed U} := ⟨V_ Ordinal.omega0, vonNeumann_omega_closed⟩
  have hforces := hval V w0
  rw [forces_impl] at hforces
  have ant : Forces (fun A B : {U : ZFSet.{u} // Closed U} => A.1 ⊆ B.1) V w0
      (Formula.diamond (Formula.box (Formula.atom 0))) := by
    rw [forces_diamond]
    refine ⟨wΩ, ZFSet.empty_subset _, ?_⟩
    rw [forces_box]
    intro B hsub
    rw [forces_atom]
    exact ⟨rfl, hsub empty_mem_vonNeumann_omega⟩
  have hatom : Forces (fun A B : {U : ZFSet.{u} // Closed U} => A.1 ⊆ B.1) V w0
      (Formula.atom 0) := hforces ant
  rw [forces_atom] at hatom
  exact ZFSet.notMem_empty _ hatom.2

/-! ## Lower bounds and one refutation on the admitted theories -/

theorem valid_K_admitted (φ ψ : Formula) :
    Valid (fun (A B : {T : Set Principle // Admitted.{u + 1} T}) => A.1 ⊆ B.1)
      (Formula.axiomK φ ψ) :=
  valid_K _ φ ψ

theorem valid_T_admitted (φ : Formula) :
    Valid (fun (A B : {T : Set Principle // Admitted.{u + 1} T}) => A.1 ⊆ B.1)
      (Formula.axiomT φ) :=
  valid_T_of_refl (fun A => admitted_refl A) φ

theorem valid_four_admitted (φ : Formula) :
    Valid (fun (A B : {T : Set Principle // Admitted.{u + 1} T}) => A.1 ⊆ B.1)
      (Formula.axiomFour φ) :=
  valid_four_of_trans
    (R := fun (A B : {T : Set Principle // Admitted.{u + 1} T}) => A.1 ⊆ B.1)
    (fun _ _ _ hAB hBC => admitted_trans hAB hBC) φ

/-- **`◇□φ → □◇φ` fails on the admitted theories.** At the theory of
extensionality, the empty set, union, and power, let `φ` say that the theory
contains the well-founded theory. That world is admitted. The well-founded
theory extends it, and every admitted extension of the well-founded theory
contains it, so `◇□φ`. The anti-founded theory also extends it, and along
that extension `φ` never becomes true, by `no_common_admitted_extension`, so
`¬□◇φ`. -/
theorem not_valid_dot2_admitted :
    ¬ Valid (fun (A B : {T : Set Principle // Admitted.{u + 1} T}) => A.1 ⊆ B.1)
        (Formula.axiomDot2 (Formula.atom 0)) := by
  intro hval
  let core : Set Principle := {.extensional, .empty, .union, .power}
  have hcore : core ⊆ setForming := by
    simp only [core, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp [setForming]
  have hW : core ⊆ wellFounded := by
    intro p hp
    rw [wellFounded]
    exact Set.mem_insert_of_mem _ (hcore hp)
  have hA : core ⊆ antiFounded := by
    intro p hp
    rw [antiFounded]
    exact Set.mem_insert_of_mem _ (hcore hp)
  let V : ℕ → {T : Set Principle // Admitted.{u + 1} T} → Prop :=
    fun n A => n = 0 ∧ wellFounded ⊆ A.1
  let w0 : {T : Set Principle // Admitted.{u + 1} T} :=
    ⟨core, admitted_wellFounded.mono hW⟩
  let wW : {T : Set Principle // Admitted.{u + 1} T} := ⟨wellFounded, admitted_wellFounded⟩
  let wA : {T : Set Principle // Admitted.{u + 1} T} := ⟨antiFounded, admitted_antiFounded⟩
  let R : {T : Set Principle // Admitted.{u + 1} T} →
      {T : Set Principle // Admitted.{u + 1} T} → Prop := fun A B => A.1 ⊆ B.1
  have hforces := hval V w0
  rw [forces_impl] at hforces
  have ant : Forces R V w0 (Formula.diamond (Formula.box (Formula.atom 0))) := by
    rw [forces_diamond]
    refine ⟨wW, hW, ?_⟩
    rw [forces_box]
    intro B hWB
    rw [forces_atom]
    exact ⟨rfl, hWB⟩
  have hbox : Forces R V w0 (Formula.box (Formula.diamond (Formula.atom 0))) := hforces ant
  rw [forces_box] at hbox
  have hdiam : Forces R V wA (Formula.diamond (Formula.atom 0)) := hbox wA hA
  rw [forces_diamond] at hdiam
  obtain ⟨B, hAB, hφ⟩ := hdiam
  rw [forces_atom] at hφ
  exact no_common_admitted_extension hφ.2 hAB B.2

/-! ## Buttons and switches on the closed sets -/

/-- A pure button: once true, true at every accessible world. -/
def PureButton {W : Type u} (R : W → W → Prop) (P : W → Prop) : Prop :=
  ∀ w, P w → ∀ w', R w w' → P w'

/-- Necessity of a predicate. -/
def Necessary {W : Type u} (R : W → W → Prop) (P : W → Prop) (w : W) : Prop :=
  ∀ w', R w w' → P w'

/-- A switch: from every world the predicate is possibly true and possibly false. -/
def IsSwitch {W : Type u} (R : W → W → Prop) (P : W → Prop) : Prop :=
  ∀ w, (∃ w', R w w' ∧ P w') ∧ (∃ w', R w w' ∧ ¬ P w')

/-- Two pure buttons are independently necessary when a common world sees a world
at which the first is necessary and the second is not, and a world at which the
second is necessary and the first is not. -/
def IndependentButtons {W : Type u} (R : W → W → Prop) (P Q : W → Prop) : Prop :=
  PureButton R P ∧ PureButton R Q ∧
    ∃ root left right,
      R root left ∧ R root right ∧
        Necessary R P left ∧ ¬ Necessary R P right ∧
          Necessary R Q right ∧ ¬ Necessary R Q left

/-- A constantly true predicate is a pure button; equality with zero is not, along `≤`. -/
example :
    PureButton (fun m n : ℕ => m ≤ n) (fun _ => True) ∧
      ¬ PureButton (fun m n : ℕ => m ≤ n) (fun n => n = 0) := by
  constructor
  · intro _ _ _ _
    trivial
  · intro h
    have := h 0 rfl 1 (Nat.zero_le 1)
    exact Nat.one_ne_zero this

/-- Zero is necessary for `0 ≤ n` at `3`, and it is not necessary for `n = 0` at `0`. -/
example :
    Necessary (fun m n : ℕ => m ≤ n) (fun n => 0 ≤ n) 3 ∧
      ¬ Necessary (fun m n : ℕ => m ≤ n) (fun n => n = 0) 0 := by
  constructor
  · intro _ _
    exact Nat.zero_le _
  · intro h
    exact Nat.one_ne_zero (h 1 (Nat.zero_le 1))

/-- Parity is a switch along `≤`; a constantly true predicate is not. -/
example :
    IsSwitch (fun m n : ℕ => m ≤ n) (fun n => Even n) ∧
      ¬ IsSwitch (fun m n : ℕ => m ≤ n) (fun _ => True) := by
  constructor
  · intro w
    have hle : w ≤ 2 * w := by
      calc
        w = 1 * w := (Nat.one_mul w).symm
        _ ≤ 2 * w := Nat.mul_le_mul_right w (by decide)
    refine ⟨⟨2 * w, hle, even_two_mul w⟩, ⟨2 * w + 1, hle.trans (Nat.le_add_right _ 1), ?_⟩⟩
    intro hEven
    rw [Nat.even_add_one] at hEven
    exact hEven (even_two_mul w)
  · intro h
    obtain ⟨_, _, hnot⟩ := (h 0).2
    exact hnot trivial

/-- On a fork, the two branch predicates are independently necessary pure buttons. -/
example :
    IndependentButtons (fun a b : Fin 3 => a = 0 ∨ a = b) (fun w : Fin 3 => w = 1)
      (fun w : Fin 3 => w = 2) := by
  refine ⟨?_, ?_, 0, 1, 2, Or.inl rfl, Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · intro w hw w' hr
    rcases hr with h0 | heq
    · exact absurd (h0.symm.trans hw) (by decide : (0 : Fin 3) ≠ 1)
    · rw [← heq]
      exact hw
  · intro w hw w' hr
    rcases hr with h0 | heq
    · exact absurd (h0.symm.trans hw) (by decide : (0 : Fin 3) ≠ 2)
    · rw [← heq]
      exact hw
  · intro w' hr
    rcases hr with h | h
    · exact absurd h (by decide : (1 : Fin 3) ≠ 0)
    · exact h.symm
  · intro h
    exact absurd (h 2 (Or.inr rfl)) (by decide : (2 : Fin 3) ≠ 1)
  · intro w' hr
    rcases hr with h | h
    · exact absurd h (by decide : (2 : Fin 3) ≠ 0)
    · exact h.symm
  · intro h
    exact absurd (h 1 (Or.inr rfl)) (by decide : (1 : Fin 3) ≠ 2)

/-- **A transitive total frame has no independently necessary pure buttons.** -/
theorem no_independent_pure_buttons_of_total {W : Type u} (R : W → W → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c) (htotal : ∀ a b, R a b ∨ R b a)
    (P Q : W → Prop) : ¬ IndependentButtons R P Q := by
  intro h
  obtain ⟨_, _, _, left, right, _, _, necP, notNecP, necQ, notNecQ⟩ := h
  rcases htotal left right with hab | hba
  · apply notNecP
    intro z hz
    exact necP z (htrans left right z hab hz)
  · apply notNecQ
    intro z hz
    exact necQ z (htrans right left z hba hz)

theorem closedFrame_no_independent_pure_buttons :
    ∀ P Q : {U : ZFSet.{u} // Closed U} → Prop,
      ¬ IndependentButtons (fun A B => A.1 ⊆ B.1) P Q :=
  no_independent_pure_buttons_of_total _
    (fun _ _ _ hAB hBC => closedFrame_trans hAB hBC)
    (fun A B => closedFrame_linear A B)

/-- Along `≤`, equality with zero and equality with one are not independently necessary. -/
example :
    ¬ IndependentButtons (fun m n : ℕ => m ≤ n) (fun n => n = 0) (fun n => n = 1) :=
  no_independent_pure_buttons_of_total (fun m n : ℕ => m ≤ n)
    (fun _ _ _ hmn hnk => hmn.trans hnk) le_total _ _

/-- Membership of the empty set, once true of a closed set, stays true of every
closed extension. -/
theorem emptyMem_pure_button :
    PureButton (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1)
      (fun A => (∅ : ZFSet.{u}) ∈ A.1) := by
  intro A hA B hAB
  exact hAB hA

/-- **Membership of the empty set is not a switch on the closed sets.** At the
hereditarily finite sets it holds, and it holds at every closed extension. -/
theorem emptyMem_not_switch :
    ¬ IsSwitch (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1)
        (fun A => (∅ : ZFSet.{u}) ∈ A.1) := by
  intro h
  let wΩ : {U : ZFSet.{u} // Closed U} := ⟨V_ Ordinal.omega0, vonNeumann_omega_closed⟩
  obtain ⟨B, hsub, hnot⟩ := (h wΩ).2
  exact hnot (hsub empty_mem_vonNeumann_omega)

end Mettapedia.SetTheory.OpenTower.Potentialism
