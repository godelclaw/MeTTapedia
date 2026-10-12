import Mettapedia.SetTheory.OpenTower.Potentialism.Modal
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

/-!
# A transitive filtration that keeps a total preorder total

The subformulas of one modal formula are finite. Worlds that force the same
subformulas are identified, and the Lemmon relation on those truth sets is
reflexive, transitive and total whenever the original relation is. A formula
that fails on the original frame fails on this finite frame.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Potentialism

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.OpenTower.InternalTower
open Classical

universe u

/-- The subformulas of a modal formula, including the formula itself. -/
def subformulas : Formula → Finset Formula
  | .atom n => {.atom n}
  | .neg φ => insert (.neg φ) (subformulas φ)
  | .conj φ ψ => insert (.conj φ ψ) (subformulas φ ∪ subformulas ψ)
  | .box φ => insert (.box φ) (subformulas φ)

theorem subformulas_atom (n : ℕ) : subformulas (Formula.atom n) = {Formula.atom n} := rfl

theorem subformulas_neg (φ : Formula) :
    subformulas (Formula.neg φ) = insert (Formula.neg φ) (subformulas φ) := rfl

theorem subformulas_conj (φ ψ : Formula) :
    subformulas (Formula.conj φ ψ) =
      insert (Formula.conj φ ψ) (subformulas φ ∪ subformulas ψ) := rfl

theorem subformulas_box (φ : Formula) :
    subformulas (Formula.box φ) = insert (Formula.box φ) (subformulas φ) := rfl

/-- A boxed atom has that atom as a subformula. -/
example : Formula.atom 0 ∈ subformulas (Formula.box (Formula.atom 0)) := by
  rw [subformulas_box, subformulas_atom]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The atom `1` is not a subformula of the atom `0`. -/
example : Formula.atom 1 ∉ subformulas (Formula.atom 0) := by
  rw [subformulas_atom, Finset.mem_singleton]
  intro h
  cases h

theorem mem_subformulas_self (φ : Formula) : φ ∈ subformulas φ := by
  cases φ with
  | atom n =>
    rw [subformulas_atom n]
    exact Finset.mem_singleton_self _
  | neg φ =>
    rw [subformulas_neg φ]
    exact Finset.mem_insert_self _ _
  | conj φ ψ =>
    rw [subformulas_conj φ ψ]
    exact Finset.mem_insert_self _ _
  | box φ =>
    rw [subformulas_box φ]
    exact Finset.mem_insert_self _ _

theorem subformulas_neg_child (φ : Formula) : φ ∈ subformulas (Formula.neg φ) := by
  rw [subformulas_neg]
  exact Finset.mem_insert_of_mem (mem_subformulas_self φ)

theorem subformulas_box_child (φ : Formula) : φ ∈ subformulas (Formula.box φ) := by
  rw [subformulas_box]
  exact Finset.mem_insert_of_mem (mem_subformulas_self φ)

theorem subformulas_conj_left (φ ψ : Formula) : φ ∈ subformulas (Formula.conj φ ψ) := by
  rw [subformulas_conj]
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (mem_subformulas_self φ))

theorem subformulas_conj_right (φ ψ : Formula) : ψ ∈ subformulas (Formula.conj φ ψ) := by
  rw [subformulas_conj]
  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (mem_subformulas_self ψ))

/-- Membership in the subformulas is transitive. -/
theorem mem_subformulas_trans {ρ ψ χ : Formula} (hψ : ψ ∈ subformulas ρ) (hχ : χ ∈ subformulas ψ) :
    χ ∈ subformulas ρ := by
  revert ψ χ
  induction ρ with
  | atom n =>
    intro ψ χ hψ hχ
    rw [subformulas_atom n, Finset.mem_singleton] at hψ
    subst hψ
    exact hχ
  | neg φ ih =>
    intro ψ χ hψ hχ
    rw [subformulas_neg, Finset.mem_insert] at hψ
    rcases hψ with rfl | hψ
    · rw [subformulas_neg, Finset.mem_insert] at hχ
      rcases hχ with rfl | hχ
      · rw [subformulas_neg]
        exact Finset.mem_insert_self _ _
      · rw [subformulas_neg]
        exact Finset.mem_insert_of_mem (ih (mem_subformulas_self φ) hχ)
    · rw [subformulas_neg]
      exact Finset.mem_insert_of_mem (ih hψ hχ)
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ χ hψ hχ
    rw [subformulas_conj, Finset.mem_insert, Finset.mem_union] at hψ
    rcases hψ with rfl | hψ | hψ
    · rw [subformulas_conj, Finset.mem_insert, Finset.mem_union] at hχ
      rcases hχ with rfl | hχ | hχ
      · rw [subformulas_conj]
        exact Finset.mem_insert_self _ _
      · rw [subformulas_conj]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (ih₁ (mem_subformulas_self φ₁) hχ))
      · rw [subformulas_conj]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (ih₂ (mem_subformulas_self φ₂) hχ))
    · rw [subformulas_conj]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ih₁ hψ hχ))
    · rw [subformulas_conj]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ih₂ hψ hχ))
  | box φ ih =>
    intro ψ χ hψ hχ
    rw [subformulas_box, Finset.mem_insert] at hψ
    rcases hψ with rfl | hψ
    · rw [subformulas_box, Finset.mem_insert] at hχ
      rcases hχ with rfl | hχ
      · rw [subformulas_box]
        exact Finset.mem_insert_self _ _
      · rw [subformulas_box]
        exact Finset.mem_insert_of_mem (ih (mem_subformulas_self φ) hχ)
    · rw [subformulas_box]
      exact Finset.mem_insert_of_mem (ih hψ hχ)

/-- The subformulas of `φ` that hold at one world. -/
noncomputable def truthSet {W : Type*} (R : W → W → Prop) (V : ℕ → W → Prop) (φ : Formula) (w : W) :
    Finset Formula :=
  (subformulas φ).filter (fun ψ => Forces R V w ψ)

theorem truthSet_mem_iff {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ ψ : Formula}
    (hsub : ψ ∈ subformulas φ) (w : W) : ψ ∈ truthSet R V φ w ↔ Forces R V w ψ := by
  unfold truthSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hsub, h⟩⟩

/-- A true atom belongs to its truth set. -/
example :
    Formula.atom 0 ∈ truthSet (fun (_ _ : Unit) => True) (fun _ _ => True) (Formula.atom 0) () := by
  rw [truthSet_mem_iff (mem_subformulas_self _) ()]
  trivial

/-- A false atom does not belong to its truth set. -/
example :
    Formula.atom 0 ∉ truthSet (fun (_ _ : Unit) => True) (fun _ _ => False) (Formula.atom 0) () := by
  intro h
  have hforces := (truthSet_mem_iff (mem_subformulas_self _) ()).mp h
  rw [forces_atom] at hforces
  exact hforces

/-- The truth sets of subformulas of `φ` that some world realizes. -/
noncomputable def filWorlds {W : Type*} (R : W → W → Prop) (V : ℕ → W → Prop) (φ : Formula) :
    Finset (Finset Formula) :=
  (subformulas φ).powerset.filter (fun s => ∃ w, truthSet R V φ w = s)

theorem mem_filWorlds {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ : Formula}
    {s : Finset Formula} :
    s ∈ filWorlds R V φ ↔ s ⊆ subformulas φ ∧ ∃ w, truthSet R V φ w = s := by
  unfold filWorlds
  rw [Finset.mem_filter, Finset.mem_powerset]

theorem truthSet_mem_filWorlds {W : Type*} (R : W → W → Prop) (V : ℕ → W → Prop) (φ : Formula)
    (w : W) : truthSet R V φ w ∈ filWorlds R V φ := by
  rw [mem_filWorlds]
  refine ⟨?_, w, rfl⟩
  intro ψ hψ
  rw [truthSet, Finset.mem_filter] at hψ
  exact hψ.1

theorem filWorld_witness {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ : Formula}
    (s : {s : Finset Formula // s ∈ filWorlds R V φ}) : ∃ w, truthSet R V φ w = s.1 :=
  ((mem_filWorlds).mp s.2).2

/-- The truth set of a true atom is a filtration world. -/
example :
    {Formula.atom 0} ∈ filWorlds (fun (_ _ : Unit) => True) (fun _ _ => True) (Formula.atom 0) := by
  have hEq :
      truthSet (fun (_ _ : Unit) => True) (fun _ _ => True) (Formula.atom 0) () = {Formula.atom 0} := by
    ext ψ
    constructor
    · intro hψ
      have hsub : ψ ∈ subformulas (Formula.atom 0) := by
        rw [truthSet, Finset.mem_filter] at hψ
        exact hψ.1
      rw [subformulas_atom, Finset.mem_singleton] at hsub
      exact Finset.mem_singleton.mpr hsub
    · intro hψ
      rw [Finset.mem_singleton] at hψ
      rw [hψ, truthSet_mem_iff (mem_subformulas_self _)]
      trivial
  rw [← hEq]
  exact truthSet_mem_filWorlds _ _ _ _

/-- A foreign atom is not a filtration world of the atom `0`. -/
example :
    {Formula.atom 1} ∉ filWorlds (fun (_ _ : Unit) => True) (fun _ _ => True) (Formula.atom 0) := by
  intro h
  obtain ⟨hsub, _⟩ := (mem_filWorlds).mp h
  have hmem : Formula.atom 1 ∈ subformulas (Formula.atom 0) :=
    hsub (Finset.mem_singleton_self _)
  rw [subformulas_atom, Finset.mem_singleton] at hmem
  cases hmem

/-- Lemmon's relation: a boxed subformula true at the source stays boxed, and holds, at the target. -/
def filtRel {W : Type*} (R : W → W → Prop) (V : ℕ → W → Prop) (φ : Formula)
    (s t : {s : Finset Formula // s ∈ filWorlds R V φ}) : Prop :=
  ∀ ψ, Formula.box ψ ∈ subformulas φ → Formula.box ψ ∈ s.1 → Formula.box ψ ∈ t.1 ∧ ψ ∈ t.1

/-- With no boxed subformula, the Lemmon relation holds. -/
example :
    filtRel (fun (_ _ : Unit) => True) (fun _ _ => True) (Formula.atom 0)
      ⟨truthSet (fun (_ _ : Unit) => True) (fun _ _ => True) (Formula.atom 0) (),
        truthSet_mem_filWorlds _ _ _ _⟩
      ⟨truthSet (fun (_ _ : Unit) => True) (fun _ _ => True) (Formula.atom 0) (),
        truthSet_mem_filWorlds _ _ _ _⟩ := by
  intro ψ hbox _hmem
  rw [subformulas_atom, Finset.mem_singleton] at hbox
  cases hbox

private def chainRel (a b : Fin 2) : Prop := a ≤ b

private def chainVal (_n : ℕ) (w : Fin 2) : Prop := w = 1

private theorem chain_box_at_one :
    Formula.box (Formula.atom 0) ∈
      truthSet chainRel chainVal (Formula.box (Formula.atom 0)) 1 := by
  rw [truthSet_mem_iff (mem_subformulas_self _), forces_box]
  intro w hw
  have hle : (1 : ℕ) ≤ w := (Fin.le_iff_val_le_val).mp hw
  have hlt : w.1 < 2 := w.isLt
  have hv : w.1 = 1 := by omega
  have hw1 : w = 1 := Fin.ext hv
  rw [hw1, forces_atom]
  rfl

private theorem chain_atom_not_at_zero :
    Formula.atom 0 ∉ truthSet chainRel chainVal (Formula.box (Formula.atom 0)) 0 := by
  intro h
  have hforces :=
    (truthSet_mem_iff (subformulas_box_child (Formula.atom 0)) 0).mp h
  rw [forces_atom] at hforces
  exact Nat.zero_ne_one (congrArg Fin.val hforces)

/-- On the two-point chain, the top's truth set does not see the bottom's. -/
example :
    ¬ filtRel chainRel chainVal (Formula.box (Formula.atom 0))
        ⟨truthSet chainRel chainVal (Formula.box (Formula.atom 0)) 1,
          truthSet_mem_filWorlds _ _ _ _⟩
        ⟨truthSet chainRel chainVal (Formula.box (Formula.atom 0)) 0,
          truthSet_mem_filWorlds _ _ _ _⟩ := by
  intro h
  have hmem := chain_box_at_one
  obtain ⟨_, hψ⟩ := h (Formula.atom 0) (mem_subformulas_self _) hmem
  exact chain_atom_not_at_zero hψ

theorem filtRel_of_rel {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ : Formula}
    (htrans : ∀ a b c, R a b → R b c → R a c) {w w' : W} (hR : R w w') :
    filtRel R V φ ⟨truthSet R V φ w, truthSet_mem_filWorlds R V φ w⟩
      ⟨truthSet R V φ w', truthSet_mem_filWorlds R V φ w'⟩ := by
  intro ψ hsub hmem
  have hbox : Forces R V w (Formula.box ψ) := (truthSet_mem_iff hsub w).mp hmem
  refine ⟨?_, ?_⟩
  · rw [truthSet_mem_iff hsub]
    rw [forces_box]
    intro u hu
    exact (forces_box.mp hbox) u (htrans w w' u hR hu)
  · rw [truthSet_mem_iff (mem_subformulas_trans hsub (subformulas_box_child ψ))]
    exact (forces_box.mp hbox) w' hR

theorem filtRel_refl {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ : Formula}
    (hrefl : ∀ w, R w w) (s : {s : Finset Formula // s ∈ filWorlds R V φ}) : filtRel R V φ s s := by
  obtain ⟨w, hw⟩ := filWorld_witness s
  intro ψ hsub hmem
  refine ⟨hmem, ?_⟩
  rw [← hw] at hmem ⊢
  have hbox : Forces R V w (Formula.box ψ) := (truthSet_mem_iff hsub w).mp hmem
  rw [truthSet_mem_iff (mem_subformulas_trans hsub (subformulas_box_child ψ))]
  exact (forces_box.mp hbox) w (hrefl w)

theorem filtRel_trans {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ : Formula}
    {a b c : {s : Finset Formula // s ∈ filWorlds R V φ}} (hab : filtRel R V φ a b)
    (hbc : filtRel R V φ b c) : filtRel R V φ a c := by
  intro ψ hsub hmem
  obtain ⟨hbox, _⟩ := hab ψ hsub hmem
  exact hbc ψ hsub hbox

/-- Totality of the original preorder passes to the Lemmon relation on realized truth sets. -/
theorem filtRel_total {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ : Formula}
    (htrans : ∀ a b c, R a b → R b c → R a c) (htotal : ∀ a b, R a b ∨ R b a)
    (s t : {s : Finset Formula // s ∈ filWorlds R V φ}) :
    filtRel R V φ s t ∨ filtRel R V φ t s := by
  by_cases hst : filtRel R V φ s t
  · exact Or.inl hst
  · right
    obtain ⟨w, hw⟩ := filWorld_witness s
    obtain ⟨v, hv⟩ := filWorld_witness t
    have hnot : ¬ R w v := by
      intro hR
      apply hst
      intro ψ hsub hmem
      have hmemw : Formula.box ψ ∈ truthSet R V φ w := by
        rw [hw]
        exact hmem
      have hpair := filtRel_of_rel (V := V) (φ := φ) htrans hR ψ hsub hmemw
      rw [← hv]
      exact hpair
    have hRv : R v w := by
      rcases htotal w v with h | h
      · exact absurd h hnot
      · exact h
    intro ψ hsub hmem
    have hmemv : Formula.box ψ ∈ truthSet R V φ v := by
      rw [hv]
      exact hmem
    have hpair := filtRel_of_rel (V := V) (φ := φ) htrans hRv ψ hsub hmemv
    rw [← hw]
    exact hpair

theorem realized_neg_iff {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ χ : Formula}
    (hχ : χ ∈ subformulas φ) (hneg : Formula.neg χ ∈ subformulas φ)
    (s : {s : Finset Formula // s ∈ filWorlds R V φ}) :
    Formula.neg χ ∈ s.1 ↔ χ ∉ s.1 := by
  obtain ⟨w, hw⟩ := filWorld_witness s
  rw [← hw, truthSet_mem_iff hneg, truthSet_mem_iff hχ]
  exact forces_neg

theorem realized_conj_iff {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop}
    {φ χ ξ : Formula} (hχ : χ ∈ subformulas φ) (hξ : ξ ∈ subformulas φ)
    (hconj : Formula.conj χ ξ ∈ subformulas φ) (s : {s : Finset Formula // s ∈ filWorlds R V φ}) :
    Formula.conj χ ξ ∈ s.1 ↔ χ ∈ s.1 ∧ ξ ∈ s.1 := by
  obtain ⟨w, hw⟩ := filWorld_witness s
  rw [← hw, truthSet_mem_iff hconj, truthSet_mem_iff hχ, truthSet_mem_iff hξ]
  exact forces_conj

/-- On a realized truth set, forcing in the filtration agrees with membership, for subformulas. -/
theorem filt_forces_iff_mem {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop} {φ : Formula}
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ ψ, ψ ∈ subformulas φ →
      ∀ s : {s : Finset Formula // s ∈ filWorlds R V φ},
        Forces (filtRel R V φ) (fun n t => Formula.atom n ∈ t.1) s ψ ↔ ψ ∈ s.1 := by
  intro ψ
  induction ψ with
  | atom _ =>
    intro _ s
    rfl
  | neg χ ih =>
    intro hsub s
    have hχ : χ ∈ subformulas φ := mem_subformulas_trans hsub (subformulas_neg_child χ)
    rw [forces_neg, realized_neg_iff hχ hsub s]
    exact not_congr (ih hχ s)
  | conj χ ξ ihχ ihξ =>
    intro hsub s
    have hχ : χ ∈ subformulas φ := mem_subformulas_trans hsub (subformulas_conj_left χ ξ)
    have hξ : ξ ∈ subformulas φ := mem_subformulas_trans hsub (subformulas_conj_right χ ξ)
    rw [forces_conj, realized_conj_iff hχ hξ hsub s]
    exact and_congr (ihχ hχ s) (ihξ hξ s)
  | box χ ih =>
    intro hsub s
    have hχ : χ ∈ subformulas φ := mem_subformulas_trans hsub (subformulas_box_child χ)
    rw [forces_box]
    constructor
    · intro hAll
      obtain ⟨w, hw⟩ := filWorld_witness s
      rw [← hw, truthSet_mem_iff hsub, forces_box]
      intro w' hR
      let t : {s : Finset Formula // s ∈ filWorlds R V φ} :=
        ⟨truthSet R V φ w', truthSet_mem_filWorlds R V φ w'⟩
      have hrel : filtRel R V φ s t := by
        intro ψ hψ hψs
        have hψw : Formula.box ψ ∈ truthSet R V φ w := by
          rw [hw]
          exact hψs
        exact filtRel_of_rel htrans hR ψ hψ hψw
      have hmemχ : χ ∈ t.1 := (ih hχ t).mp (hAll t hrel)
      exact (truthSet_mem_iff hχ w').mp (by
        have : t.1 = truthSet R V φ w' := rfl
        rw [this] at hmemχ
        exact hmemχ)
    · intro hmem t hrel
      exact (ih hχ t).mpr (hrel χ hsub hmem).2

theorem filWorlds_finite {W : Type*} (R : W → W → Prop) (V : ℕ → W → Prop) (φ : Formula) :
    Finite {s : Finset Formula // s ∈ filWorlds R V φ} :=
  Fintype.finite (Fintype.subtype (filWorlds R V φ) fun _ => Iff.rfl)

theorem filWorlds_nonempty {W : Type*} (R : W → W → Prop) (V : ℕ → W → Prop) (φ : Formula)
    (hinhab : Nonempty W) : Nonempty {s : Finset Formula // s ∈ filWorlds R V φ} := by
  obtain ⟨w⟩ := hinhab
  exact ⟨⟨truthSet R V φ w, truthSet_mem_filWorlds R V φ w⟩⟩

theorem not_forces_filt_of_not_forces {W : Type*} {R : W → W → Prop} {V : ℕ → W → Prop}
    {φ : Formula} (htrans : ∀ a b c, R a b → R b c → R a c) {w : W} (hw : ¬ Forces R V w φ) :
    ¬ Forces (filtRel R V φ) (fun n s => Formula.atom n ∈ s.1)
        ⟨truthSet R V φ w, truthSet_mem_filWorlds R V φ w⟩ φ := by
  intro h
  have hmem :=
    (filt_forces_iff_mem (R := R) (V := V) (φ := φ) htrans φ (mem_subformulas_self φ) _).mp h
  exact hw ((truthSet_mem_iff (mem_subformulas_self φ) w).mp hmem)

/-- A failure on a reflexive transitive total frame already fails on a finite one of that shape. -/
theorem finite_total_of_not_valid {W : Type*} {R : W → W → Prop} (hrefl : ∀ w, R w w)
    (htrans : ∀ a b c, R a b → R b c → R a c) (htotal : ∀ a b, R a b ∨ R b a) (hinhab : Nonempty W)
    {φ : Formula} (hfail : ¬ Valid R φ) :
    ∃ (W' : Type) (R' : W' → W' → Prop),
      Finite W' ∧ Nonempty W' ∧ (∀ w, R' w w) ∧
        (∀ a b c, R' a b → R' b c → R' a c) ∧ (∀ a b, R' a b ∨ R' b a) ∧ ¬ Valid R' φ := by
  unfold Valid at hfail
  rw [Classical.not_forall] at hfail
  obtain ⟨V, hfail⟩ := hfail
  rw [Classical.not_forall] at hfail
  obtain ⟨w, hw⟩ := hfail
  refine ⟨{s : Finset Formula // s ∈ filWorlds R V φ}, filtRel R V φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact filWorlds_finite R V φ
  · exact filWorlds_nonempty R V φ hinhab
  · exact filtRel_refl hrefl
  · intro _a _b _c hab hbc
    exact filtRel_trans hab hbc
  · intro a b
    exact filtRel_total htrans htotal a b
  · intro hval
    exact not_forces_filt_of_not_forces htrans hw
      (hval (fun n s => Formula.atom n ∈ s.1)
        ⟨truthSet R V φ w, truthSet_mem_filWorlds R V φ w⟩)

/-- A formula that fails on the closed sets fails on some nonempty finite total preorder. -/
theorem not_valid_finite_total_of_not_valid_closed {φ : Formula}
    (hfail : ¬ Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) φ) :
    ∃ (W : Type) (R : W → W → Prop),
      Finite W ∧ Nonempty W ∧ (∀ w, R w w) ∧
        (∀ a b c, R a b → R b c → R a c) ∧ (∀ a b, R a b ∨ R b a) ∧ ¬ Valid R φ :=
  finite_total_of_not_valid
    (W := {U : ZFSet.{u} // Closed U})
    (R := fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1)
    (fun A => closedFrame_refl A)
    (fun _ _ _ hab hbc => closedFrame_trans hab hbc)
    (fun a b => closedFrame_linear a b)
    ⟨⟨∅, closed_empty⟩⟩ hfail

end Mettapedia.SetTheory.OpenTower.Potentialism
