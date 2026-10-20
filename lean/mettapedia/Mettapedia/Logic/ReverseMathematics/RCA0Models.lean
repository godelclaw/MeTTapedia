import Mettapedia.Logic.ReverseMathematics.Systems
import Mettapedia.Logic.ReverseMathematics.TuringIdeal

/-!
# Turing ideals are ω-models of RCA₀

**Theorem** (`IsTuringIdeal.models_RCA0`). For every signature whose extra
symbols are computable, every Turing ideal is an ω-model of `RCA₀`. In
particular the recursive sets are one (`recursiveSets_models_RCA0`), the
least (`IsTuringIdeal.recursiveSets_subset`).

This is one direction of the characterization "the ω-models of `RCA₀` are
exactly the Turing ideals" (Simpson, *Subsystems of Second Order
Arithmetic*, §VIII.1). The mechanism:

1. A bounded formula with set parameters `V 0, …, V (k-1)` is decided by a
   procedure computable in those sets (`bounded_computableIn`). Atoms query
   the oracles; bounded quantifiers are primitive recursion.
2. For a `Σ⁰₁` formula `∃m θ` equivalent to a `Π⁰₁` formula `∀m χ`, search
   for the first `m` with `θ` or `¬χ`; the search always stops, and `θ` at the
   found `m` decides membership. The defined set is therefore computable in
   the parameters.
3. The parameters have a common upper bound inside the ideal
   (`IsTuringIdeal.exists_upper`), so the defined set lies in the ideal.

For the converse direction this file proves the closure properties that
need no arithmetization of computations: every ω-model of `RCA₀` is
nonempty and closed under the join, under complements and under sets
`Σ⁰₀`-definable from its members (`Models.join_mem`, `Models.compl_mem`,
`Models.bounded_mem`). Closure under Turing reducibility needs a `Σ⁰₁`
definition of oracle computations inside `L₂` (Kleene's normal form,
relativized), which is not formalized here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Formula Term RelComp Encodable

variable {σ : Signature}

/-! ## Environments of bound values in front of parameters -/

/-- The number environment with the values `l` (innermost first) in front of
the parameters `v`. -/
def prepend (l : List ℕ) (v : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if h : i < l.length then l[i] else v (i - l.length)

theorem cons_prepend (n : ℕ) (l : List ℕ) (v : ℕ → ℕ) :
    Env.cons n (prepend l v) = prepend (n :: l) v := by
  funext i
  cases i with
  | zero => simp [prepend]
  | succ i =>
      simp only [Env.cons_succ, prepend, List.length_cons, Nat.add_lt_add_iff_right,
        List.getElem_cons_succ]
      split_ifs <;> simp [Nat.add_sub_add_right]

theorem prepend_nil (v : ℕ → ℕ) : prepend [] v = v := by
  funext i
  simp [prepend]

theorem cons_cons_eq_prepend (m n : ℕ) (v : ℕ → ℕ) :
    Env.cons m (Env.cons n v) = prepend [m, n] v := by
  rw [← prepend_nil v, cons_prepend, cons_prepend, prepend_nil]

/-- The parameters below `i + 1`, as a finite table. -/
def paramTable (v : ℕ → ℕ) (i : ℕ) : List ℕ :=
  List.ofFn fun j : Fin (i + 1) => v j

theorem prepend_eq_getD (l : List ℕ) (v : ℕ → ℕ) (i : ℕ) :
    prepend l v i = (l ++ paramTable v i).getD i 0 := by
  unfold prepend paramTable
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left h]
    simp [h]
  · rw [List.getElem?_append_right (by omega),
      List.getElem?_eq_getElem (by simp; omega), Option.getD_some, List.getElem_ofFn]

/-! ## Bounded formulas are decided relative to their parameters -/

/-- Terms of a computable signature are computable functions of the bound
values. -/
theorem term_computableIn (hσ : σ.IsComputable) {O : Set (ℕ →. ℕ)} (v : ℕ → ℕ) (t : Term σ) :
    ComputableIn O fun l : List ℕ => t.eval (prepend l v) := by
  induction t with
  | var i =>
      exact of_eq (ofPrimrec₂ (Primrec.list_getD 0)
          (ofPrimrec₂ Primrec.list_append id' (const (paramTable v i))) (const i))
        fun l => (prepend_eq_getD l v i).symm
  | zero => exact const 0
  | one => exact const 1
  | add t u ht hu =>
      exact ofPrimrec₂ (f := fun a b : ℕ => a + b) Primrec.nat_add ht hu
  | mul t u ht hu =>
      exact ofPrimrec₂ (f := fun a b : ℕ => a * b) Primrec.nat_mul ht hu
  | app f t u ht hu =>
      exact comp₂ (f := σ.interp f)
        (Computable.computableIn (hσ f) : ComputableIn₂ O (σ.interp f)) ht hu

/-- Primitive recursion for the bounded universal quantifier. -/
private theorem rec_and_eq (P : ℕ → Prop) [DecidablePred P] (H : ℕ → Bool)
    (hH : ∀ n, H n = decide (P n)) :
    ∀ m, Nat.rec (motive := fun _ => Bool) true (fun y acc => acc && H y) m =
      decide (∀ n < m, P n)
  | 0 => by simp
  | m + 1 => by
      have ih := rec_and_eq P H hH m
      show (Nat.rec (motive := fun _ => Bool) true (fun y acc => acc && H y) m && H m) = _
      rw [ih, hH, Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨below, at_m⟩ n lt
        rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
        · exact below n lt
        · exact at_m
      · intro all
        exact ⟨fun n lt => all n (Nat.lt_succ_of_lt lt), all m (Nat.lt_succ_self m)⟩

/-- Primitive recursion for the bounded existential quantifier. -/
private theorem rec_or_eq (P : ℕ → Prop) [DecidablePred P] (H : ℕ → Bool)
    (hH : ∀ n, H n = decide (P n)) :
    ∀ m, Nat.rec (motive := fun _ => Bool) false (fun y acc => acc || H y) m =
      decide (∃ n < m, P n)
  | 0 => by simp
  | m + 1 => by
      have ih := rec_or_eq P H hH m
      show (Nat.rec (motive := fun _ => Bool) false (fun y acc => acc || H y) m || H m) = _
      rw [ih, hH, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨n, lt, holds⟩ | at_m)
        · exact ⟨n, Nat.lt_succ_of_lt lt, holds⟩
        · exact ⟨m, Nat.lt_succ_self m, at_m⟩
      · rintro ⟨n, lt, holds⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
        · exact Or.inl ⟨n, lt, holds⟩
        · exact Or.inr holds

open Classical in
/-- **A bounded formula is decided by a procedure computable in its set
parameters.** -/
theorem bounded_computableIn (hσ : σ.IsComputable) (S : Set (Set ℕ)) (v : ℕ → ℕ)
    (V : ℕ → Set ℕ) {k : ℕ} {φ : Formula σ} (hφ : IsBounded φ) (hk : SetVarsBelow k φ) :
    ComputableIn (envOracles V k) fun l : List ℕ => decide (Holds S φ (prepend l v) V) := by
  revert hk
  induction hφ with
  | eq t u =>
      intro _
      exact of_eq (ofPrimrec₂ Primrec.eq.decide (term_computableIn hσ v t)
        (term_computableIn hσ v u)) fun l => by rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; simp [Holds]
  | lt t u =>
      intro _
      exact of_eq (ofPrimrec₂ Primrec.nat_lt.decide (term_computableIn hσ v t)
        (term_computableIn hσ v u)) fun l => by rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; simp [Holds]
  | mem t j =>
      intro hk
      cases hk with
      | mem _ hj =>
          exact of_eq (mem_comp (A := V j) (charFn_mem_envOracles V hj)
            (term_computableIn hσ v t)) fun l => by rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; simp [Holds]
  | falsum =>
      intro _
      exact of_eq (const false) fun l => by rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; simp [Holds]
  | imp _ _ ihφ ihψ =>
      intro hk
      cases hk with
      | imp hkφ hkψ =>
          exact of_eq (ofPrimrec₂ (f := fun a b : Bool => !a || b)
            (Primrec.or.comp (Primrec.not.comp Primrec.fst) Primrec.snd)
            (ihφ hkφ) (ihψ hkψ)) fun l => by
              rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; simp [Holds, imp_iff_not_or]
  | and _ _ ihφ ihψ =>
      intro hk
      cases hk with
      | and hkφ hkψ =>
          exact of_eq (ofPrimrec₂ (f := fun a b : Bool => a && b) Primrec.and (ihφ hkφ) (ihψ hkψ))
            fun l => by
            rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; simp [Holds]
  | or _ _ ihφ ihψ =>
      intro hk
      cases hk with
      | or hkφ hkψ =>
          exact of_eq (ofPrimrec₂ (f := fun a b : Bool => a || b) Primrec.or (ihφ hkφ) (ihψ hkψ))
            fun l => by
            rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; simp [Holds]
  | @ballLt t φ _ ihφ =>
      intro hk
      cases hk with
      | ballLt _ hkφ =>
          have body := ihφ hkφ
          have step : ComputableIn₂ (envOracles V k) fun (l : List ℕ) (p : ℕ × Bool) =>
              p.2 && decide (Holds S φ (prepend (p.1 :: l) v) V) :=
            ofPrimrec₂ (f := fun a b : Bool => a && b) Primrec.and (comp' snd snd)
              (comp' body (ofPrimrec₂ Primrec.list_cons (comp' fst snd) fst))
          refine of_eq (nat_rec (term_computableIn hσ v t) (const true) step) fun l => ?_
          have := rec_and_eq (fun n => Holds S φ (prepend (n :: l) v) V)
            (fun n => decide (Holds S φ (prepend (n :: l) v) V)) (fun _ => rfl)
            (t.eval (prepend l v))
          rw [this]
          simp only [Holds, cons_prepend]
  | @bexLt t φ _ ihφ =>
      intro hk
      cases hk with
      | bexLt _ hkφ =>
          have body := ihφ hkφ
          have step : ComputableIn₂ (envOracles V k) fun (l : List ℕ) (p : ℕ × Bool) =>
              p.2 || decide (Holds S φ (prepend (p.1 :: l) v) V) :=
            ofPrimrec₂ (f := fun a b : Bool => a || b) Primrec.or (comp' snd snd)
              (comp' body (ofPrimrec₂ Primrec.list_cons (comp' fst snd) fst))
          refine of_eq (nat_rec (term_computableIn hσ v t) (const false) step) fun l => ?_
          have := rec_or_eq (fun n => Holds S φ (prepend (n :: l) v) V)
            (fun n => decide (Holds S φ (prepend (n :: l) v) V)) (fun _ => rfl)
            (t.eval (prepend l v))
          rw [this]
          simp only [Holds, cons_prepend]

/-! ## Δ⁰₁ comprehension in a Turing ideal -/

open Classical in
/-- **Turing ideals are closed under `Δ⁰₁`-definability.** -/
theorem IsTuringIdeal.deltaOneClosed (hσ : σ.IsComputable) {S : Set (Set ℕ)}
    (hS : IsTuringIdeal S) : DeltaOneClosed σ S := by
  intro φ ψ hφ hψ v V inS equiv
  obtain ⟨θ, hθ, rfl⟩ := isSigma_one_iff.mp hφ
  obtain ⟨χ, hχ, rfl⟩ := isPi_one_iff.mp hψ
  have hθk : SetVarsBelow (max θ.setBound χ.setBound) θ :=
    (setVarsBelow_setBound θ).mono (le_max_left _ _)
  have hχk : SetVarsBelow (max θ.setBound χ.setBound) χ :=
    (setVarsBelow_setBound χ).mono (le_max_right _ _)
  set k := max θ.setBound χ.setBound
  have cθ := bounded_computableIn hσ S v V hθ hθk
  have cχ := bounded_computableIn hσ S v V hχ hχk
  set X : Set ℕ := {n | Holds S (ex θ) (Env.cons n v) V} with hX
  refine ⟨X, ?_, fun n => Iff.rfl⟩
  have pairList : ComputableIn (envOracles V k) fun q : ℕ × ℕ => [q.2, q.1] :=
    ofPrimrec₂ Primrec.list_cons snd (ofPrimrec₂ Primrec.list_cons fst (const []))
  -- θ at the candidate witness, and the search for a witness of θ or of ¬χ
  set value : ℕ → ℕ → Bool := fun n m => decide (Holds S θ (prepend [m, n] v) V) with hvalue
  set p : ℕ → ℕ → Bool := fun n m =>
    decide (Holds S θ (prepend [m, n] v) V) || !decide (Holds S χ (prepend [m, n] v) V) with hp
  have cvalue : ComputableIn₂ (envOracles V k) value :=
    of_eq (comp' cθ pairList) fun q => by simp [hvalue]
  have cp : ComputableIn₂ (envOracles V k) p :=
    of_eq (ofPrimrec₂ (f := fun a b : Bool => a || b) Primrec.or (comp' cθ pairList)
      (ofPrimrec (f := fun b : Bool => !b) Primrec.not (comp' cχ pairList))) fun q => by simp [hp]
  have decider := RelComp.map (rfind' cp) cvalue
  have key : ∀ n, (Nat.rfind fun m => Part.some (p n m)).map (value n) =
      Part.some (decide (n ∈ X)) := by
    intro n
    have witness : ∃ m, p n m = true := by
      by_cases h : Holds S (ex θ) (Env.cons n v) V
      · obtain ⟨m, hm⟩ := h
        refine ⟨m, ?_⟩
        rw [cons_cons_eq_prepend] at hm
        simp [hp, hm]
      · have notAll : ¬ Holds S (all χ) (Env.cons n v) V := fun hall => h ((equiv n).mpr hall)
        simp only [Holds, not_forall] at notAll
        obtain ⟨m, hm⟩ := notAll
        refine ⟨m, ?_⟩
        rw [cons_cons_eq_prepend] at hm
        simp [hp, hm]
    obtain ⟨m, hm⟩ := witness
    obtain ⟨m₀, found, _⟩ := Nat.rfind_min' (p := p n) hm
    have found' : m₀ ∈ Nat.rfind fun m => Part.some (p n m) := found
    have spec : p n m₀ = true := by
      have := Nat.rfind_spec found
      simpa using this
    rw [Part.eq_some_iff.mpr (Part.mem_map (value n) found')]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [hvalue, decide_eq_true_eq, hX, Set.mem_ofPred_eq]
    constructor
    · intro holds
      exact ⟨m₀, by rw [cons_cons_eq_prepend]; exact holds⟩
    · intro holds
      by_contra notθ
      have notχ : ¬ Holds S χ (prepend [m₀, n] v) V := by
        simpa [hp, notθ] using spec
      have : Holds S (all χ) (Env.cons n v) V := (equiv n).mp holds
      exact notχ (by rw [← cons_cons_eq_prepend]; exact this m₀)
  have total : ComputableIn (envOracles V k) fun n : ℕ => decide (n ∈ X) :=
    RecursiveIn.of_eq decider key
  obtain ⟨B, hB, below⟩ := hS.exists_upper V inS k
  exact hS.down hB (setTuringLE_iff_nat.mpr (recursiveIn_of_envOracles below (charFn_of_decide total)))

/-- **Every Turing ideal is an ω-model of RCA₀.** -/
theorem IsTuringIdeal.models_RCA0 (hσ : σ.IsComputable) {S : Set (Set ℕ)} (hS : IsTuringIdeal S) :
    Models S (RCA0 : Set (Formula σ)) :=
  (models_RCA0_iff S).mpr ⟨hS.nonempty, hS.deltaOneClosed hσ⟩

/-- **The recursive sets form an ω-model of RCA₀.** -/
theorem recursiveSets_models_RCA0 (hσ : σ.IsComputable) :
    Models recursiveSets (RCA0 : Set (Formula σ)) :=
  recursiveSets_isTuringIdeal.models_RCA0 hσ

/-- In particular for Simpson's language `L₂`. -/
theorem recursiveSets_models_RCA0_arith :
    Models recursiveSets (RCA0 : Set (Formula Signature.arith)) :=
  recursiveSets_models_RCA0 Signature.arith_isComputable

/-- The sets computable from one set form an ω-model of RCA₀. -/
theorem principal_models_RCA0 (hσ : σ.IsComputable) (B : Set ℕ) :
    Models (principal B) (RCA0 : Set (Formula σ)) :=
  (principal_isTuringIdeal B).models_RCA0 hσ

/-! ## Closure properties of every ω-model of RCA₀ -/

/-- **Bounded comprehension.** Every ω-model of RCA₀ contains each set
`Σ⁰₀`-definable from its members. -/
theorem Models.bounded_mem {S : Set (Set ℕ)} (h : Models S (RCA0 : Set (Formula σ)))
    {θ : Formula σ} (hθ : IsBounded θ) (v : ℕ → ℕ) (V : ℕ → Set ℕ) (inS : ∀ j, V j ∈ S) :
    ∃ X ∈ S, ∀ n, n ∈ X ↔ Holds S θ (Env.cons n v) V := by
  obtain ⟨_, closed⟩ := (models_RCA0_iff S).mp h
  have shifted : IsBounded (θ.renameNum Nat.succ) := hθ.renameNum _
  have dummy : ∀ n, Holds S (ex (θ.renameNum Nat.succ)) (Env.cons n v) V ↔
      Holds S θ (Env.cons n v) V := by
    intro n
    simp only [Holds, holds_renameNum, Env.cons_comp_succ, exists_const]
  obtain ⟨X, member, spec⟩ := closed (ex (θ.renameNum Nat.succ)) (all (θ.renameNum Nat.succ))
    (isSigma_one_iff.mpr ⟨_, shifted, rfl⟩) (isPi_one_iff.mpr ⟨_, shifted, rfl⟩) v V inS
    (fun n => by
      rw [dummy]
      simp only [Holds, holds_renameNum, Env.cons_comp_succ, forall_const])
  exact ⟨X, member, fun n => (spec n).trans (dummy n)⟩

/-- The `Σ⁰₀` definition of the join from set variables `0` and `1`. -/
def joinFormula : Formula σ :=
  bexLt (add (var 0) one)
    (or (and (eq (var 1) (add (var 0) (var 0))) (mem (var 0) 0))
      (and (eq (var 1) (add (add (var 0) (var 0)) one)) (mem (var 0) 1)))

theorem joinFormula_isBounded : IsBounded (joinFormula : Formula σ) :=
  .bexLt _ (.or (.and (.eq _ _) (.mem _ _)) (.and (.eq _ _) (.mem _ _)))

theorem holds_joinFormula (S : Set (Set ℕ)) (A B : Set ℕ) (V : ℕ → Set ℕ) (n : ℕ) (v : ℕ → ℕ) :
    Holds S (joinFormula : Formula σ) (Env.cons n v) (Env.cons A (Env.cons B V)) ↔
      n ∈ join A B := by
  simp only [joinFormula, Holds, Term.eval, Env.cons_zero, Env.cons_succ, join,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, _, (⟨rfl, hk⟩ | ⟨rfl, hk⟩)⟩
    · left
      refine ⟨by omega, ?_⟩
      have : (k + k) / 2 = k := by omega
      rwa [this]
    · right
      refine ⟨by omega, ?_⟩
      have : (k + k + 1) / 2 = k := by omega
      rwa [this]
  · rintro (⟨even, hA⟩ | ⟨odd, hB⟩)
    · exact ⟨n / 2, by omega, Or.inl ⟨by omega, hA⟩⟩
    · exact ⟨n / 2, by omega, Or.inr ⟨by omega, hB⟩⟩

/-- **Every ω-model of RCA₀ is closed under the join.** -/
theorem Models.join_mem {S : Set (Set ℕ)} (h : Models S (RCA0 : Set (Formula σ))) {A B : Set ℕ}
    (hA : A ∈ S) (hB : B ∈ S) : join A B ∈ S := by
  obtain ⟨X, member, spec⟩ := h.bounded_mem (joinFormula_isBounded (σ := σ)) (fun _ => 0)
    (Env.cons A (Env.cons B (fun _ => A))) (fun j => by
      rcases j with _ | _ | _ <;> assumption)
  have same : X = join A B := by
    ext n
    rw [spec n, holds_joinFormula]
  exact same ▸ member

/-- **Every ω-model of RCA₀ is closed under complements.** -/
theorem Models.compl_mem {S : Set (Set ℕ)} (h : Models S (RCA0 : Set (Formula σ))) {A : Set ℕ}
    (hA : A ∈ S) : Aᶜ ∈ S := by
  obtain ⟨X, member, spec⟩ := h.bounded_mem (θ := not (mem (var 0) 0)) (.imp (.mem _ _) .falsum)
    (fun _ => 0) (fun _ => A) (fun _ => hA)
  have same : X = Aᶜ := by
    ext n
    rw [spec n]
    simp [Formula.not, Holds, Term.eval]
  exact same ▸ member

/-- Every ω-model of RCA₀ contains the recursive sets definable without
parameters by a bounded formula; for instance the even numbers. -/
example {S : Set (Set ℕ)} (h : Models S (RCA0 : Set (Formula Signature.arith))) :
    {n : ℕ | ∃ k < n + 1, n = k + k} ∈ S := by
  obtain ⟨X, member, spec⟩ := h.bounded_mem
    (θ := bexLt (add (var 0) one) (eq (var 1) (add (var 0) (var 0)))) (.bexLt _ (.eq _ _))
    (fun _ => 0) (fun _ => h.1.some) (fun _ => h.1.some_mem)
  have same : X = {n : ℕ | ∃ k < n + 1, n = k + k} := by
    ext n
    rw [spec n]
    simp [Holds, Term.eval]
  exact same ▸ member

#print axioms bounded_computableIn
#print axioms IsTuringIdeal.deltaOneClosed
#print axioms IsTuringIdeal.models_RCA0
#print axioms recursiveSets_models_RCA0
#print axioms Models.join_mem
#print axioms Models.compl_mem

end Mettapedia.Logic.ReverseMathematics
