import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Forall2
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases

/-!
# Value equality of finite term graphs

A value such as a MeTTa atom or a Prolog term is a finite term graph: a node
is a leaf carrying a value, or a constructor with a name and ordered children,
and a child may point back to an ancestor, so the graph may be cyclic.  Two
nodes are equal as values when their unfoldings agree: both are leaves the leaf
comparison relates, or both are constructors with the same name whose children
are pairwise equal.

The leaf comparison is any Boolean relation.  It need not be reflexive: a NaN
equals nothing, not even itself.  Value equality is therefore the greatest
relation closed under one comparison step, not an equivalence in general.

## Main results

* `valueEq_iff_forall_upTo`: two nodes are equal as values exactly when their
  unfoldings agree to every finite depth.  Cycles change how a comparison ends,
  not what it decides.
* `run_decides`: the worklist procedure, which expands each pair of
  constructor nodes once and takes a pair met again as equal, answers `true`
  exactly for value-equal nodes, within an explicit number of steps.
* `valueEq_symm`, `valueEq_trans`, `valueEq_refl_of_reachable`: for a
  symmetric and transitive leaf comparison, value equality is a partial
  equivalence, reflexive on every node whose reachable leaves are
  self-equal (for numbers, those holding no NaN).

This models the algorithm; it does not verify a particular implementation.
-/

namespace Mettapedia.Algorithms.TermGraphValueEquality

/-- A node of a term graph on `n` nodes. -/
inductive Node (L : Type*) (n : ℕ) where
  | leaf (value : L)
  | cons (name : ℕ) (children : List (Fin n))

variable {L : Type*} {n : ℕ}

/-- One comparison step for the pair `(a, b)`, relative to a relation that
the child pairs must satisfy. -/
def Step (leafEq : L → L → Bool) (g : Fin n → Node L n)
    (R : Fin n → Fin n → Prop) (a b : Fin n) : Prop :=
  match g a, g b with
  | .leaf x, .leaf y => leafEq x y = true
  | .cons f cs, .cons h ds => f = h ∧ List.Forall₂ R cs ds
  | _, _ => False

theorem Step.mono {leafEq : L → L → Bool} {g : Fin n → Node L n}
    {R S : Fin n → Fin n → Prop} (hRS : ∀ a b, R a b → S a b)
    {a b : Fin n} (h : Step leafEq g R a b) : Step leafEq g S a b := by
  unfold Step at h ⊢
  cases hga : g a <;> cases hgb : g b <;> simp only [hga, hgb] at h ⊢
  · exact h
  · exact ⟨h.1, h.2.imp (fun x y hxy => hRS x y hxy)⟩

/-- A relation all of whose pairs pass one comparison step. -/
def IsValueBisim (leafEq : L → L → Bool) (g : Fin n → Node L n)
    (R : Fin n → Fin n → Prop) : Prop :=
  ∀ a b, R a b → Step leafEq g R a b

/-- Value equality: the greatest relation closed under the comparison step. -/
def ValueEq (leafEq : L → L → Bool) (g : Fin n → Node L n)
    (a b : Fin n) : Prop :=
  ∃ R, IsValueBisim leafEq g R ∧ R a b

section Greatest

variable {leafEq : L → L → Bool} {g : Fin n → Node L n}

theorem valueEq_isValueBisim : IsValueBisim leafEq g (ValueEq leafEq g) := by
  rintro a b ⟨R, hR, hab⟩
  exact (hR a b hab).mono fun x y hxy => ⟨R, hR, hxy⟩

theorem valueEq_step {a b : Fin n} (h : ValueEq leafEq g a b) :
    Step leafEq g (ValueEq leafEq g) a b :=
  valueEq_isValueBisim a b h

end Greatest

/-! ## Finite unfoldings -/

/-- Agreement of the unfoldings of two nodes to depth `k`. -/
def UpTo (leafEq : L → L → Bool) (g : Fin n → Node L n) : ℕ → Fin n → Fin n → Prop
  | 0 => fun _ _ => True
  | k + 1 => Step leafEq g (UpTo leafEq g k)

section Unfolding

variable {leafEq : L → L → Bool} {g : Fin n → Node L n}

theorem upTo_of_valueEq {a b : Fin n} (h : ValueEq leafEq g a b) :
    ∀ k, UpTo leafEq g k a b := by
  intro k
  induction k generalizing a b with
  | zero => trivial
  | succ k ih =>
    exact (valueEq_step h).mono fun x y hxy => ih hxy

/-- Agreement to every finite depth is closed under the comparison step: the
children of a constructor are a finite list, so each child pair agrees to
every depth. -/
theorem forall_upTo_isValueBisim :
    IsValueBisim leafEq g (fun a b => ∀ k, UpTo leafEq g k a b) := by
  intro a b h
  have hstep : ∀ k, Step leafEq g (UpTo leafEq g k) a b := fun k => h (k + 1)
  unfold Step at hstep ⊢
  cases hga : g a <;> cases hgb : g b <;> simp only [hga, hgb] at hstep ⊢
  · exact hstep 0
  · exact (hstep 0).elim
  · exact (hstep 0).elim
  · rename_i f cs h ds
    refine ⟨(hstep 0).1, ?_⟩
    have hlen : cs.length = ds.length := (hstep 0).2.length_eq
    rw [List.forall₂_iff_get]
    refine ⟨hlen, fun i h₁ h₂ k => ?_⟩
    exact (List.forall₂_iff_get.mp (hstep k).2).2 i h₁ h₂

/-- Cycles change how a comparison ends, not what it decides: two nodes are
equal as values exactly when their unfoldings agree to every finite depth. -/
theorem valueEq_iff_forall_upTo {a b : Fin n} :
    ValueEq leafEq g a b ↔ ∀ k, UpTo leafEq g k a b :=
  ⟨upTo_of_valueEq, fun h => ⟨_, forall_upTo_isValueBisim, h⟩⟩

end Unfolding

/-! ## The worklist procedure -/

/-- Compare the pending pairs.  A pair of constructor nodes is expanded once:
it joins `seen`, and meeting it again discharges only that obligation.  Every
pending pair is still compared, so a loop cannot hide a mismatch or a NaN.
`none` means the fuel ran out. -/
def run (leafEq : L → L → Bool) (g : Fin n → Node L n) :
    ℕ → List (Fin n × Fin n) → Finset (Fin n × Fin n) → Option Bool
  | 0, _, _ => none
  | _ + 1, [], _ => some true
  | fuel + 1, (a, b) :: rest, seen =>
    match g a, g b with
    | .leaf x, .leaf y =>
      if leafEq x y then run leafEq g fuel rest seen else some false
    | .cons f cs, .cons h ds =>
      if (a, b) ∈ seen then run leafEq g fuel rest seen
      else if f = h ∧ cs.length = ds.length then
        run leafEq g fuel (cs.zip ds ++ rest) (insert (a, b) seen)
      else some false
    | _, _ => some false

section Procedure

variable {leafEq : L → L → Bool} {g : Fin n → Node L n}

/-- The pairs a successful run vouches for: those expanded, and leaf pairs the
leaf comparison relates. -/
def Vouched (leafEq : L → L → Bool) (g : Fin n → Node L n)
    (S : Finset (Fin n × Fin n)) (a b : Fin n) : Prop :=
  (a, b) ∈ S ∨ ∃ x y, g a = .leaf x ∧ g b = .leaf y ∧ leafEq x y = true

theorem run_sound_aux :
    ∀ (fuel : ℕ) (pending : List (Fin n × Fin n)) (seen : Finset (Fin n × Fin n)),
      run leafEq g fuel pending seen = some true →
      ∃ S, seen ⊆ S ∧ (∀ p ∈ pending, Vouched leafEq g S p.1 p.2) ∧
        ∀ q ∈ S, q ∉ seen → Step leafEq g (Vouched leafEq g S) q.1 q.2
  | 0, _, _, h => by simp [run] at h
  | _ + 1, [], seen, _ => ⟨seen, subset_rfl, by simp, fun q hq hnot => (hnot hq).elim⟩
  | fuel + 1, (a, b) :: rest, seen, h => by
    simp only [run] at h
    cases hga : g a <;> cases hgb : g b <;> simp only [hga, hgb] at h
    · rename_i x y
      by_cases hxy : leafEq x y = true
      · simp only [hxy, if_true] at h
        obtain ⟨S, hsub, hpend, hstep⟩ := run_sound_aux fuel rest seen h
        refine ⟨S, hsub, ?_, hstep⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inr ⟨x, y, hga, hgb, hxy⟩
        · exact hpend p hp
      · simp [hxy] at h
    · simp at h
    · simp at h
    · rename_i f cs h' ds
      by_cases hseen : (a, b) ∈ seen
      · simp only [hseen, if_true] at h
        obtain ⟨S, hsub, hpend, hstep⟩ := run_sound_aux fuel rest seen h
        refine ⟨S, hsub, ?_, hstep⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inl (hsub hseen)
        · exact hpend p hp
      · simp only [hseen, if_false] at h
        by_cases hmatch : f = h' ∧ cs.length = ds.length
        · simp only [hmatch, and_self, if_true] at h
          obtain ⟨S, hsub, hpend, hstep⟩ :=
            run_sound_aux fuel (cs.zip ds ++ rest) (insert (a, b) seen) h
          have hab : (a, b) ∈ S := hsub (Finset.mem_insert_self _ _)
          refine ⟨S, fun q hq => hsub (Finset.mem_insert_of_mem hq), ?_, ?_⟩
          · intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact Or.inl hab
            · exact hpend p (List.mem_append_right _ hp)
          · intro q hq hnot
            by_cases hqab : q = (a, b)
            · subst hqab
              unfold Step
              simp only [hga, hgb]
              refine ⟨hmatch.1, ?_⟩
              rw [List.forall₂_iff_get]
              refine ⟨hmatch.2, fun i h₁ h₂ => ?_⟩
              have hmem : (cs.get ⟨i, h₁⟩, ds.get ⟨i, h₂⟩) ∈ cs.zip ds := by
                rw [List.mem_iff_get]
                refine ⟨⟨i, by simp [List.length_zip, h₁, h₂]⟩, ?_⟩
                simp [List.get_eq_getElem, List.getElem_zip]
              exact hpend _ (List.mem_append_left _ hmem)
            · exact hstep q hq (by simp [Finset.mem_insert, hqab, hnot])
        · simp [hmatch] at h

/-- A run that answers `true` is right: the compared nodes are value-equal. -/
theorem run_sound {fuel : ℕ} {a b : Fin n}
    (h : run leafEq g fuel [(a, b)] ∅ = some true) : ValueEq leafEq g a b := by
  obtain ⟨S, -, hpend, hstep⟩ := run_sound_aux fuel [(a, b)] ∅ h
  refine ⟨Vouched leafEq g S, ?_, hpend (a, b) (List.mem_singleton_self _)⟩
  intro x y hxy
  rcases hxy with hin | ⟨u, v, hgx, hgy, huv⟩
  · exact hstep (x, y) hin (Finset.notMem_empty _)
  · unfold Step
    simp only [hgx, hgy]
    exact huv

/-- A run over value-equal pending pairs never answers `false`. -/
theorem run_ne_false :
    ∀ (fuel : ℕ) (pending : List (Fin n × Fin n)) (seen : Finset (Fin n × Fin n)),
      (∀ p ∈ pending, ValueEq leafEq g p.1 p.2) →
      run leafEq g fuel pending seen ≠ some false
  | 0, _, _, _ => by simp [run]
  | _ + 1, [], _, _ => by simp [run]
  | fuel + 1, (a, b) :: rest, seen, hall => by
    have hab : ValueEq leafEq g a b := hall (a, b) List.mem_cons_self
    have hrest : ∀ p ∈ rest, ValueEq leafEq g p.1 p.2 :=
      fun p hp => hall p (List.mem_cons_of_mem _ hp)
    have hstep := valueEq_step hab
    simp only [run]
    unfold Step at hstep
    cases hga : g a <;> cases hgb : g b <;> simp only [hga, hgb] at hstep ⊢
    · simp only [hstep, if_true]
      exact run_ne_false fuel rest seen hrest
    · by_cases hseen : (a, b) ∈ seen
      · simp only [hseen, if_true]
        exact run_ne_false fuel rest seen hrest
      · rename_i f cs h' ds
        have hlen : cs.length = ds.length := hstep.2.length_eq
        simp only [hseen, if_false, hstep.1, hlen, and_self, if_true]
        refine run_ne_false fuel _ _ ?_
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · rw [List.mem_iff_get] at hp
          obtain ⟨i, rfl⟩ := hp
          have hi₁ : i.1 < cs.length := by
            have := i.2; simp [List.length_zip] at this; omega
          have hi₂ : i.1 < ds.length := by
            have := i.2; simp [List.length_zip] at this; omega
          have := (List.forall₂_iff_get.mp hstep.2).2 i.1 hi₁ hi₂
          simpa [List.get_eq_getElem, List.getElem_zip] using this
        · exact hrest p hp

/-- A bound on the arity of every node. -/
def ArityBound (g : Fin n → Node L n) (A : ℕ) : Prop :=
  ∀ i, match g i with
    | .leaf _ => True
    | .cons _ cs => cs.length ≤ A

/-- Each step either drops one pending pair, or expands a new constructor
pair, which adds at most `A` pending pairs and one of at most `n * n` seen
pairs.  So this measure falls at every step. -/
def measure (A : ℕ) (pending : List (Fin n × Fin n))
    (seen : Finset (Fin n × Fin n)) : ℕ :=
  pending.length + (n * n - seen.card) * (A + 1)

theorem run_ne_none {A : ℕ} (hA : ArityBound g A) :
    ∀ (fuel : ℕ) (pending : List (Fin n × Fin n)) (seen : Finset (Fin n × Fin n)),
      measure A pending seen < fuel →
      run leafEq g fuel pending seen ≠ none
  | 0, _, _, hfuel => (Nat.not_lt_zero _ hfuel).elim
  | _ + 1, [], _, _ => by simp [run]
  | fuel + 1, (a, b) :: rest, seen, hfuel => by
    simp only [run]
    have hdrop : measure A rest seen < fuel := by
      unfold measure at hfuel ⊢
      simp only [List.length_cons] at hfuel
      omega
    cases hga : g a <;> cases hgb : g b <;> simp only
    · split_ifs
      · exact run_ne_none hA fuel rest seen hdrop
      · simp
    · simp
    · simp
    · rename_i f cs h' ds
      split_ifs with hseen hmatch
      · exact run_ne_none hA fuel rest seen hdrop
      · refine run_ne_none hA fuel _ _ ?_
        have hcard : (insert (a, b) seen).card = seen.card + 1 :=
          Finset.card_insert_of_notMem hseen
        have hbound : (insert (a, b) seen).card ≤ n * n := by
          have := Finset.card_le_univ (insert (a, b) seen)
          simpa [Fintype.card_prod, Fintype.card_fin] using this
        have hcs : cs.length ≤ A := by
          have := hA a
          simp only [hga] at this
          exact this
        unfold measure at hfuel ⊢
        simp only [List.length_cons, List.length_append, List.length_zip,
          hmatch.2, min_self] at hfuel ⊢
        rw [hcard] at hbound ⊢
        have hlt : seen.card < n * n := by omega
        have hsplit : n * n - seen.card = (n * n - (seen.card + 1)) + 1 := by omega
        rw [hsplit, Nat.add_mul, one_mul] at hfuel
        have hds : ds.length ≤ A := hmatch.2 ▸ hcs
        generalize (n * n - (seen.card + 1)) * (A + 1) = P at hfuel ⊢
        omega
      · simp

/-- The number of steps that always suffices for one comparison. -/
def fuelFor (n A : ℕ) : ℕ := 1 + n * n * (A + 1) + 1

/-- The worklist procedure decides value equality: within `fuelFor n A`
steps it answers, and it answers `true` exactly for value-equal nodes. -/
theorem run_decides {A : ℕ} (hA : ArityBound g A) (a b : Fin n) :
    run leafEq g (fuelFor n A) [(a, b)] ∅ = some true ↔ ValueEq leafEq g a b := by
  refine ⟨run_sound, fun h => ?_⟩
  have hfuel : measure A [(a, b)] (∅ : Finset (Fin n × Fin n)) < fuelFor n A := by
    unfold measure fuelFor
    simp
  have hsome := run_ne_none (leafEq := leafEq) hA _ _ _ hfuel
  have hfalse := run_ne_false (leafEq := leafEq) (g := g) (fuelFor n A) [(a, b)] ∅
    (by simpa using h)
  cases hr : run leafEq g (fuelFor n A) [(a, b)] ∅ with
  | none => exact (hsome hr).elim
  | some r => cases r <;> simp_all

end Procedure

/-! ## A partial equivalence -/

section Equivalence

variable {leafEq : L → L → Bool} {g : Fin n → Node L n}

theorem forall₂_comp {α β γ : Type*} {R : α → β → Prop} {S : β → γ → Prop} :
    ∀ {xs : List α} {ys : List β} {zs : List γ},
      List.Forall₂ R xs ys → List.Forall₂ S ys zs →
      List.Forall₂ (fun x z => ∃ y, R x y ∧ S y z) xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons ⟨_, h₁, h₂⟩ (forall₂_comp t₁ t₂)

theorem valueEq_symm (hsymm : ∀ x y, leafEq x y = true → leafEq y x = true)
    {a b : Fin n} (h : ValueEq leafEq g a b) : ValueEq leafEq g b a := by
  refine ⟨fun x y => ValueEq leafEq g y x, ?_, h⟩
  intro x y hxy
  have hstep := valueEq_step hxy
  unfold Step at hstep ⊢
  cases hgx : g x <;> cases hgy : g y <;> simp only [hgx, hgy] at hstep ⊢
  · exact hsymm _ _ hstep
  · exact ⟨hstep.1.symm, hstep.2.flip⟩

theorem valueEq_trans (htrans : ∀ x y z, leafEq x y = true → leafEq y z = true →
      leafEq x z = true)
    {a b c : Fin n} (hab : ValueEq leafEq g a b) (hbc : ValueEq leafEq g b c) :
    ValueEq leafEq g a c := by
  refine ⟨fun x z => ∃ y, ValueEq leafEq g x y ∧ ValueEq leafEq g y z, ?_,
    ⟨b, hab, hbc⟩⟩
  rintro x z ⟨y, hxy, hyz⟩
  have h₁ := valueEq_step hxy
  have h₂ := valueEq_step hyz
  unfold Step at h₁ h₂ ⊢
  cases hgx : g x <;> cases hgy : g y <;> cases hgz : g z <;>
    simp only [hgx, hgy, hgz] at h₁ h₂ ⊢
  · exact htrans _ _ _ h₁ h₂
  · exact ⟨h₁.1.trans h₂.1, forall₂_comp h₁.2 h₂.2⟩

/-- The nodes reachable from `a` through children, `a` included. -/
inductive Reachable (g : Fin n → Node L n) (a : Fin n) : Fin n → Prop where
  | refl : Reachable g a a
  | child {i j : Fin n} {f : ℕ} {cs : List (Fin n)} :
      Reachable g a i → g i = .cons f cs → j ∈ cs → Reachable g a j

/-- Value equality is reflexive on a node whose reachable leaves are all
self-equal: for numbers, a node that holds no NaN. -/
theorem valueEq_refl_of_reachable {a : Fin n}
    (hleaves : ∀ i x, Reachable g a i → g i = .leaf x → leafEq x x = true) :
    ValueEq leafEq g a a := by
  refine ⟨fun x y => x = y ∧ Reachable g a x, ?_, rfl, Reachable.refl⟩
  rintro x y ⟨rfl, hx⟩
  unfold Step
  cases hgx : g x
  · exact hleaves x _ hx hgx
  · rename_i f cs
    refine ⟨rfl, ?_⟩
    rw [List.forall₂_same]
    intro c hc
    exact ⟨rfl, Reachable.child hx hgx hc⟩

end Equivalence

/-! ## Example: numbers, one of them a NaN -/

/-- Rational numbers, with `none` for a NaN: equal by value, and a NaN
equals nothing. -/
def numEq : Option ℚ → Option ℚ → Bool
  | some x, some y => decide (x = y)
  | _, _ => false

/-- `c = f(1, c)` at node 0, `d = f(1, f(1, d))` at node 2, a loop twice as
long, and `e = f(NaN, e)` at node 4. -/
def loops : Fin 6 → Node (Option ℚ) 6
  | 0 => .cons 0 [1, 0]
  | 1 => .leaf (some 1)
  | 2 => .cons 0 [1, 3]
  | 3 => .cons 0 [1, 2]
  | 4 => .cons 0 [5, 4]
  | 5 => .leaf none

theorem loops_arity : ArityBound loops 2 := by
  intro i; fin_cases i <;> simp [loops]

/-- Loops of different lengths with the same unfolding are equal. -/
example : run numEq loops (fuelFor 6 2) [(0, 2)] ∅ = some true := by decide

/-- A NaN inside a loop keeps the loop from equalling itself. -/
example : run numEq loops (fuelFor 6 2) [(4, 4)] ∅ = some false := by decide

example : ValueEq numEq loops 0 2 :=
  (run_decides loops_arity 0 2).mp (by decide)

example : ¬ ValueEq numEq loops 4 4 := fun h => by
  have := (run_decides (leafEq := numEq) loops_arity 4 4).mpr h
  exact absurd this (by decide)

end Mettapedia.Algorithms.TermGraphValueEquality
