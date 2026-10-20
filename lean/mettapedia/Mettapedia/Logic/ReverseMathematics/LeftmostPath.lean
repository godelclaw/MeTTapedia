import Mettapedia.Logic.ReverseMathematics.WeakKoenig

/-!
# Arithmetical comprehension proves weak König's lemma in Turing ideals

**Theorem** (`IsTuringIdeal.WKL_of_models_ACA0`). A Turing ideal that is an
ω-model of ACA₀ (over primitive recursive symbols) satisfies weak König's
lemma.

The mechanism is the classical proof that ACA₀ proves König's lemma
(Simpson, *Subsystems of Second Order Arithmetic*, §III.7), split into a
comprehension step and a computation step.

1. The nodes of a tree `T` that have extensions in `T` at every greater
   length (`extendible T`) form a `Π⁰₂` set in the code of `T`
   (`holds_extendibleFormula`), so arithmetical comprehension puts its code
   in the model.
2. If `T` has nodes at every level, the empty string is extendible, and every
   extendible node has an extendible child (`extendible_child`, the
   pigeonhole step of König's lemma).
3. The leftmost path through the extendible nodes (`leftmost`) is computable
   from their code by primitive recursion with oracle queries
   (`leftmost_computableIn`), so it lies in the Turing ideal.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Encodable Formula Term RelComp

/-! ## Extendible nodes -/

/-- The nodes with extensions in `T` at every greater length. -/
def extendible (T : Set (List Bool)) : Set (List Bool) :=
  {σ | ∀ k, ∃ τ ∈ T, τ.length = σ.length + k ∧ σ <+: τ}

theorem extendible_subset (T : Set (List Bool)) : extendible T ⊆ T := by
  intro σ h
  obtain ⟨τ, hτ, hl, hp⟩ := h 0
  have same : σ = τ := hp.eq_of_length (by simpa using hl.symm)
  exact same ▸ hτ

theorem nil_mem_extendible {T : Set (List Bool)} (levels : HasAllLevels T) :
    [] ∈ extendible T := fun k =>
  let ⟨τ, hτ, hl⟩ := levels k
  ⟨τ, hτ, by simpa using hl, List.nil_prefix⟩

/-- A prefix of `τ` with a further entry extends by that entry. -/
theorem append_getD_prefix {σ τ : List Bool} (hp : σ <+: τ) (long : σ.length < τ.length) :
    σ ++ [τ.getD σ.length false] <+: τ := by
  obtain ⟨ρ, rfl⟩ := hp
  cases ρ with
  | nil => simp at long
  | cons c ρ' =>
      have bit : (σ ++ c :: ρ').getD σ.length false = c := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
        simp
      rw [bit]
      exact ⟨ρ', by simp⟩

/-- **The pigeonhole step of König's lemma.** -/
theorem extendible_child {T : Set (List Bool)} (hT : IsTree T) {σ : List Bool}
    (hσ : σ ∈ extendible T) : σ ++ [false] ∈ extendible T ∨ σ ++ [true] ∈ extendible T := by
  by_contra none
  push Not at none
  obtain ⟨h0, h1⟩ := none
  simp only [extendible, Set.mem_ofPred_eq, not_forall, not_exists, not_and] at h0 h1
  obtain ⟨k₀, hk₀⟩ := h0
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨τ, hτ, hl, hp⟩ := hσ (max k₀ k₁ + 1)
  have long : σ.length < τ.length := by omega
  have child := append_getD_prefix hp long
  cases hb : τ.getD σ.length false with
  | false =>
      rw [hb] at child
      refine hk₀ (τ.take (σ.length + 1 + k₀)) (hT τ hτ _) (by simp; omega) ?_
      exact List.prefix_take_iff.mpr ⟨child, by simp⟩
  | true =>
      rw [hb] at child
      refine hk₁ (τ.take (σ.length + 1 + k₁)) (hT τ hτ _) (by simp; omega) ?_
      exact List.prefix_take_iff.mpr ⟨child, by simp⟩

/-! ## The leftmost path -/

open Classical in
/-- The prefixes of the leftmost path through `E`: take the left child when
it lies in `E`, otherwise the right one. -/
noncomputable def leftmost (E : Set (List Bool)) : ℕ → List Bool
  | 0 => []
  | n + 1 => if leftmost E n ++ [false] ∈ E then leftmost E n ++ [false] else leftmost E n ++ [true]

theorem leftmost_succ (E : Set (List Bool)) (n : ℕ) :
    ∃ b, leftmost E (n + 1) = leftmost E n ++ [b] := by
  classical
  by_cases h : leftmost E n ++ [false] ∈ E
  · exact ⟨false, by simp [leftmost, h]⟩
  · exact ⟨true, by simp [leftmost, h]⟩

theorem length_leftmost (E : Set (List Bool)) : ∀ n, (leftmost E n).length = n
  | 0 => rfl
  | n + 1 => by
      obtain ⟨b, hb⟩ := leftmost_succ E n
      rw [hb, List.length_append, length_leftmost E n]
      rfl

theorem leftmost_prefix (E : Set (List Bool)) {m n : ℕ} (h : m ≤ n) :
    leftmost E m <+: leftmost E n := by
  induction n with
  | zero =>
      rw [Nat.le_zero.mp h]
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with lt | rfl
      · obtain ⟨b, hb⟩ := leftmost_succ E n
        rw [hb]
        exact (ih (Nat.lt_succ_iff.mp lt)).trans (List.prefix_append _ _)
      · exact List.prefix_refl _

/-- **The leftmost path stays among the extendible nodes.** -/
theorem leftmost_mem_extendible {T : Set (List Bool)} (hT : IsTree T) (levels : HasAllLevels T) :
    ∀ n, leftmost (extendible T) n ∈ extendible T
  | 0 => nil_mem_extendible levels
  | n + 1 => by
      classical
      have ih := leftmost_mem_extendible hT levels n
      by_cases h : leftmost (extendible T) n ++ [false] ∈ extendible T
      · rw [leftmost, if_pos h]
        exact h
      · rw [leftmost, if_neg h]
        exact (extendible_child hT ih).resolve_left h

/-- The set of positions where the leftmost path takes the right child. -/
def leftmostSet (E : Set (List Bool)) : Set ℕ :=
  {n | (leftmost E (n + 1)).getD n false = true}

theorem prefixOf_leftmostSet (E : Set (List Bool)) (n : ℕ) :
    prefixOf (leftmostSet E) n = leftmost E n := by
  apply List.ext_getElem (by rw [length_prefixOf, length_leftmost])
  intro i hi1 hi2
  rw [length_leftmost] at hi2
  have bit : (leftmost E n)[i] = (leftmost E (i + 1)).getD i false := by
    have long : i < (leftmost E (i + 1)).length := by rw [length_leftmost]; omega
    rw [getD_eq_getElem' long]
    obtain ⟨rest, hrest⟩ := leftmost_prefix E (show i + 1 ≤ n by omega)
    simp only [← hrest]
    rw [List.getElem_append_left long]
  rw [bit, Bool.eq_iff_iff, getElem_prefixOf]
  rfl

/-- **The leftmost path is a path through the tree.** -/
theorem isPath_leftmostSet {T : Set (List Bool)} (hT : IsTree T) (levels : HasAllLevels T) :
    IsPath (leftmostSet (extendible T)) T := fun n => by
  rw [prefixOf_leftmostSet]
  exact extendible_subset T (leftmost_mem_extendible hT levels n)

theorem mem_codeOf_encode (E : Set (List Bool)) (σ : List Bool) :
    encode σ ∈ codeOf E ↔ σ ∈ E :=
  ⟨fun ⟨_, hτ, h⟩ => encode_injective h ▸ hτ, fun h => ⟨σ, h, rfl⟩⟩

/-- **The leftmost path is computable from the code of its set.** -/
theorem leftmost_computableIn (E : Set (List Bool)) :
    ComputableIn {charFn (codeOf E)} (leftmost E) := by
  classical
  have query : ComputableIn₂ {charFn (codeOf E)} fun (_ : ℕ) (p : ℕ × List Bool) =>
      decide (encode (p.2 ++ [false]) ∈ codeOf E) :=
    mem_comp (A := codeOf E) (Set.mem_singleton _)
      (ofPrimrec Primrec.encode (ofPrimrec₂ (f := fun (l : List Bool) (a : Bool) => l ++ [a])
        Primrec.list_concat (comp' snd snd) (const false)))
  have step : ComputableIn₂ {charFn (codeOf E)} fun (_ : ℕ) (p : ℕ × List Bool) =>
      bif decide (encode (p.2 ++ [false]) ∈ codeOf E) then p.2 ++ [false] else p.2 ++ [true] :=
    ofPrimrec₂ (f := fun (b : Bool) (l : List Bool) => bif b then l ++ [false] else l ++ [true])
      (Primrec.cond Primrec.fst
        (Primrec.list_concat.comp Primrec.snd (Primrec.const false))
        (Primrec.list_concat.comp Primrec.snd (Primrec.const true)))
      query (comp' snd snd)
  have agree : ∀ m, Nat.rec (motive := fun _ => List Bool) []
      (fun y IH => bif decide (encode (IH ++ [false]) ∈ codeOf E) then IH ++ [false]
        else IH ++ [true]) m = leftmost E m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        show (bif decide (encode (Nat.rec (motive := fun _ => List Bool) [] _ m ++ [false]) ∈
            codeOf E) then _ else _) = _
        rw [ih, mem_codeOf_encode]
        by_cases h : leftmost E m ++ [false] ∈ E <;> simp [leftmost, h]
  exact of_eq (nat_rec (f := fun n => n) id' (const []) step) agree

/-- **The leftmost path is reducible to the code of its set.** -/
theorem leftmostSet_le (E : Set (List Bool)) : SetTuringLE (leftmostSet E) (codeOf E) := by
  classical
  refine setTuringLE_of_decide ?_
  refine of_eq (ofPrimrec₂ (Primrec.list_getD false)
    (comp' (leftmost_computableIn E) (ofPrimrec Primrec.succ id')) id') fun n => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  rfl

/-! ## The extendible nodes are arithmetical in the tree -/

/-- One when `n` codes a string. -/
def isCodeTest (n _ : ℕ) : ℕ :=
  bif (decode₂ (List Bool) n).isSome then 1 else 0

theorem isCodeTest_primrec : Primrec₂ isCodeTest :=
  Primrec.cond (Primrec.option_isSome.comp (Primrec.decode₂.comp Primrec.fst))
    (Primrec.const 1) (Primrec.const 0)

/-- One when `n` codes `σ`, `(Nat.unpair p).1` codes `τ`, `τ` extends `σ`, and
`|τ| = |σ| + (Nat.unpair p).2`. -/
def extendsTest (n p : ℕ) : ℕ :=
  bif ((decode₂ (List Bool) n).bind fun σ => (decode₂ (List Bool) (Nat.unpair p).1).map fun τ =>
      decide (τ.length = σ.length + (Nat.unpair p).2) && decide (τ.take σ.length = σ)).getD false
    then 1 else 0

theorem extendsTest_primrec : Primrec₂ extendsTest := by
  have inner : Primrec₂ fun (a : (ℕ × ℕ) × List Bool) (τ : List Bool) =>
      decide (τ.length = a.2.length + (Nat.unpair a.1.2).2) && decide (τ.take a.2.length = a.2) :=
    Primrec.and.comp
      (Primrec.eq.decide.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))))
      (Primrec.eq.decide.comp
        (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  have middle : Primrec₂ fun (q : ℕ × ℕ) (σ : List Bool) =>
      (decode₂ (List Bool) (Nat.unpair q.2).1).map fun τ =>
        decide (τ.length = σ.length + (Nat.unpair q.2).2) && decide (τ.take σ.length = σ) :=
    Primrec.option_map
      (Primrec.decode₂.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
      inner
  have outer : Primrec fun q : ℕ × ℕ =>
      ((decode₂ (List Bool) q.1).bind fun σ => (decode₂ (List Bool) (Nat.unpair q.2).1).map fun τ =>
        decide (τ.length = σ.length + (Nat.unpair q.2).2) && decide (τ.take σ.length = σ)).getD
        false :=
    Primrec.option_getD.comp (Primrec.option_bind (Primrec.decode₂.comp Primrec.fst) middle)
      (Primrec.const false)
  exact Primrec.cond outer (Primrec.const 1) (Primrec.const 0)

theorem extendsTest_eq_one (n m k : ℕ) :
    extendsTest n (Nat.pair m k) = 1 ↔ ∃ σ τ, decode₂ (List Bool) n = some σ ∧
      decode₂ (List Bool) m = some τ ∧ τ.length = σ.length + k ∧ σ <+: τ := by
  unfold extendsTest
  rw [Nat.unpair_pair]
  cases hn : decode₂ (List Bool) n with
  | none => simp
  | some σ =>
      cases hm : decode₂ (List Bool) m with
      | none => simp
      | some τ =>
          simp only [Option.bind_some, Option.map_some, Option.getD_some]
          constructor
          · intro h
            refine ⟨σ, τ, rfl, rfl, ?_⟩
            revert h
            cases hA : decide (τ.length = σ.length + k) <;>
              cases hB : decide (τ.take σ.length = σ) <;> intro h
            · exact absurd h (by decide)
            · exact absurd h (by decide)
            · exact absurd h (by decide)
            · exact ⟨of_decide_eq_true hA, List.prefix_iff_eq_take.mpr (of_decide_eq_true hB).symm⟩
          · rintro ⟨σ', τ', h1, h2, hl, hp⟩
            cases h1
            cases h2
            have hB := (List.prefix_iff_eq_take.mp hp).symm
            simp [hl, hB]

def isCodeSymbol : Signature.primrec.Fn := ⟨isCodeTest, isCodeTest_primrec⟩

def extendsSymbol : Signature.primrec.Fn := ⟨extendsTest, extendsTest_primrec⟩

def pairSymbol : Signature.primrec.Fn := ⟨Nat.pair, Primrec₂.natPair⟩

/-- `n` codes an extendible node of the tree coded by set variable `0`:
`n` codes a string, and `∀k ∃m (m ∈ X₀ ∧ m codes an extension of length
|n| + k)`. -/
def extendibleFormula : Formula Signature.primrec :=
  and (eq (app isCodeSymbol (var 0) zero) one)
    (all (ex (and (mem (var 0) 0)
      (eq (app extendsSymbol (var 2) (app pairSymbol (var 0) (var 1))) one))))

theorem extendibleFormula_isArithmetical : IsArithmetical extendibleFormula :=
  .and (.eq _ _) (.all (.ex (.and (.mem _ _) (.eq _ _))))

theorem holds_extendibleFormula (S : Set (Set ℕ)) (C : Set ℕ) (V : ℕ → Set ℕ) (n : ℕ)
    (v : ℕ → ℕ) :
    Holds S extendibleFormula (Env.cons n v) (Env.cons C V) ↔
      n ∈ codeOf (extendible (treeOf C)) := by
  change (isCodeTest n 0 = 1 ∧ ∀ k, ∃ m, m ∈ C ∧ extendsTest n (Nat.pair m k) = 1) ↔ _
  simp only [extendsTest_eq_one, mem_codeOf_iff]
  constructor
  · rintro ⟨isCode, ext⟩
    have some : (decode₂ (List Bool) n).isSome = true := by
      unfold isCodeTest at isCode
      cases h : (decode₂ (List Bool) n).isSome <;> simp_all
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp some
    refine ⟨σ, hσ, fun k => ?_⟩
    obtain ⟨m, hmC, σ', τ, hσ', hτ, hl, hp⟩ := ext k
    rw [hσ] at hσ'
    cases hσ'
    refine ⟨τ, ?_, hl, hp⟩
    show encode τ ∈ C
    rw [mem_decode₂.mp hτ]
    exact hmC
  · rintro ⟨σ, hσ, ext⟩
    refine ⟨by simp [isCodeTest, hσ], fun k => ?_⟩
    obtain ⟨τ, hτ, hl, hp⟩ := ext k
    exact ⟨encode τ, hτ, σ, τ, hσ, decode₂_encode τ, hl, hp⟩

/-! ## The theorem -/

/-- **A Turing ideal that is an ω-model of ACA₀ satisfies weak König's
lemma.** -/
theorem IsTuringIdeal.WKL_of_models_ACA0 {S : Set (Set ℕ)} (hS : IsTuringIdeal S)
    (h : Models S (ACA0 : Set (Formula Signature.primrec))) : WKL S := by
  intro C hC hT levels
  obtain ⟨_, closed⟩ := (models_ACA0_iff S).mp h
  obtain ⟨E, hE, spec⟩ := closed extendibleFormula extendibleFormula_isArithmetical
    (fun _ => 0) (fun _ => C) (fun _ => hC)
  have same : E = codeOf (extendible (treeOf C)) := by
    ext n
    rw [spec n]
    exact holds_extendibleFormula S C (fun _ => C) n (fun _ => 0)
  rw [same] at hE
  exact ⟨leftmostSet (extendible (treeOf C)), hS.down hE (leftmostSet_le _),
    isPath_leftmostSet hT levels⟩

/-- In particular the full power set, once more. -/
example : WKL (Set.univ : Set (Set ℕ)) :=
  univ_isTuringIdeal.WKL_of_models_ACA0 univ_models_ACA0

#print axioms extendible_child
#print axioms leftmost_computableIn
#print axioms holds_extendibleFormula
#print axioms IsTuringIdeal.WKL_of_models_ACA0

end Mettapedia.Logic.ReverseMathematics
