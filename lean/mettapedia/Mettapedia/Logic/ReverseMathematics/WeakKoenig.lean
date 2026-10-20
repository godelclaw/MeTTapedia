import Mettapedia.Logic.ReverseMathematics.Halting
import Mathlib.Order.KonigLemma
import Mathlib.Data.Set.Finite.List

/-!
# Weak König's lemma, the Kleene tree, and diagonally noncomputable functions

A binary string is a `List Bool`; a set of naturals `C` codes the set of
strings `treeOf C = {s | encode s ∈ C}` through Mathlib's coding of lists. In
an ω-model `S`, weak König's lemma (`WKL S`) says that every binary tree
coded in `S` with nodes at every level has a path in `S` (Simpson Chapter IV
and §VIII.2; for prefix-closed trees, having nodes at every level is being
infinite, `hasAllLevels_iff_infinite`).

* `exists_path`: König's lemma for binary trees, from Mathlib's
  `exists_seq_forall_proj_of_forall_finite`; hence `univ_WKL`.
* `kleeneTree`: the strings `s` such that `s_e ≠ φ_e(e) mod 2` whenever
  `φ_e(e)` converges within `|s|` steps. It is a recursive tree
  (`codeOf_kleeneTree_recursive`) with nodes at every level
  (`kleeneTree_hasAllLevels`), after S. C. Kleene, *Recursive functions and
  intuitionistic mathematics*, Proc. ICM 1950. The same construction, with
  step bounds from `Nat.Partrec.Code.evaln`, is in Cameron Freer's
  `reverse-mathlib` (`ReverseMathlib/Omega/KleeneTree.lean`); this version is
  written over `List Bool` and Mathlib's list coding.
* `isDNR_of_isPath_kleeneTree`: every path through the Kleene tree is a
  diagonally noncomputable function, and `not_computable_of_isDNR`: no
  diagonally noncomputable function is computable.
* `recursiveSets_not_WKL`: **the recursive sets are an ω-model of RCA₀ in
  which weak König's lemma fails.** This separates the ω-model classes of
  RCA₀ and WKL₀.
* `HasDNR S`: `S` contains the graph of a diagonally noncomputable function
  (the unrelativized instance of the principle DNR).
  `IsTuringIdeal.hasDNR_of_WKL`: WKL gives one through the Kleene tree.
  `Models.hasDNR`: arithmetical comprehension gives one through the
  `Δ⁰₂` definition of `e ↦ φ_e(e) + 1`. `not_hasDNR_recursiveSets`: the
  recursive sets have none.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Encodable Nat.Partrec Formula Term RelComp

/-! ## Binary trees coded by sets -/

/-- The binary strings coded by a set of naturals. -/
def treeOf (C : Set ℕ) : Set (List Bool) :=
  {s | encode s ∈ C}

/-- The code set of a set of binary strings. -/
def codeOf (T : Set (List Bool)) : Set ℕ :=
  {n | ∃ s ∈ T, encode s = n}

theorem treeOf_codeOf (T : Set (List Bool)) : treeOf (codeOf T) = T := by
  ext s
  simp only [treeOf, codeOf, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, same⟩
    exact encode_injective same ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

theorem mem_codeOf_iff (T : Set (List Bool)) (n : ℕ) :
    n ∈ codeOf T ↔ ∃ s, decode₂ (List Bool) n = some s ∧ s ∈ T :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, mem_decode₂.mpr h, hs⟩, fun ⟨s, h, hs⟩ => ⟨s, hs, mem_decode₂.mp h⟩⟩

/-- Closed under prefixes. -/
def IsTree (T : Set (List Bool)) : Prop :=
  ∀ s ∈ T, ∀ k, s.take k ∈ T

/-- A node at every length. -/
def HasAllLevels (T : Set (List Bool)) : Prop :=
  ∀ n, ∃ s ∈ T, s.length = n

/-- For trees, having a node at every level is being infinite. -/
theorem hasAllLevels_iff_infinite {T : Set (List Bool)} (hT : IsTree T) :
    HasAllLevels T ↔ T.Infinite := by
  constructor
  · intro levels finite
    obtain ⟨N, hN⟩ := (finite.image List.length).bddAbove
    obtain ⟨s, hs, hl⟩ := levels (N + 1)
    have := hN ⟨s, hs, rfl⟩
    omega
  · intro infinite n
    by_contra none
    push Not at none
    apply infinite
    refine (List.finite_length_lt Bool n).subset fun s hs => ?_
    by_contra long
    simp only [Set.mem_ofPred_eq, not_lt] at long
    exact none (s.take n) (hT s hs n) (by simp [long])

/-- The first `n` bits of the characteristic sequence of `X`. -/
noncomputable def prefixOf (X : Set ℕ) (n : ℕ) : List Bool := by
  classical
  exact (List.range n).map fun i => decide (i ∈ X)

theorem length_prefixOf (X : Set ℕ) (n : ℕ) : (prefixOf X n).length = n := by
  simp [prefixOf]

theorem getD_eq_getElem' {l : List Bool} {i : ℕ} (h : i < l.length) : l.getD i false = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getElem_prefixOf (X : Set ℕ) (n i : ℕ) (h : i < (prefixOf X n).length) :
    (prefixOf X n)[i] = true ↔ i ∈ X := by
  classical
  simp [prefixOf]

theorem getD_prefixOf (X : Set ℕ) {n i : ℕ} (h : i < n) :
    (prefixOf X n).getD i false = true ↔ i ∈ X := by
  rw [getD_eq_getElem' (by rw [length_prefixOf]; exact h), getElem_prefixOf]

/-- `X` is a path through `T`. -/
def IsPath (X : Set ℕ) (T : Set (List Bool)) : Prop :=
  ∀ n, prefixOf X n ∈ T

/-- **Weak König's lemma in the ω-model `S`.** -/
def WKL (S : Set (Set ℕ)) : Prop :=
  ∀ C ∈ S, IsTree (treeOf C) → HasAllLevels (treeOf C) → ∃ X ∈ S, IsPath X (treeOf C)

/-- `S` is an ω-model of `WKL₀ = RCA₀ + WKL`. -/
def ModelsWKL0 (σ : Signature) (S : Set (Set ℕ)) : Prop :=
  Models S (RCA0 : Set (Formula σ)) ∧ WKL S

/-! ## König's lemma -/

/-- **König's lemma for binary trees.** -/
theorem exists_path {T : Set (List Bool)} (hT : IsTree T) (levels : HasAllLevels T) :
    ∃ X, IsPath X T := by
  classical
  let α : ℕ → Type := fun i => {s : List Bool // s ∈ T ∧ s.length = i}
  have fin : ∀ i, Finite (α i) := fun i =>
    ((List.finite_length_eq Bool i).subset fun s hs => hs.2).to_subtype
  have : Finite (α 0) := fin 0
  have : ∀ i, Nonempty (α i) := fun i =>
    let ⟨s, hs, hl⟩ := levels i
    ⟨⟨s, hs, hl⟩⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite (α := α)
    (fun {i j} hij s => ⟨s.1.take i, hT s.1 s.2.1 i, by simp [s.2.2, hij]⟩)
    (fun i s => Subtype.ext (List.take_of_length_le (le_of_eq s.2.2)))
    (fun i j k hij hjk s => Subtype.ext (by simp [List.take_take, Nat.min_eq_left hij]))
    (fun i a => Set.toFinite _)
  have compatible : ∀ {i j : ℕ}, i ≤ j → (f j).1.take i = (f i).1 := fun hij =>
    congrArg Subtype.val (hf hij)
  refine ⟨{n | (f (n + 1)).1.getD n false = true}, fun n => ?_⟩
  have key : prefixOf {n | (f (n + 1)).1.getD n false = true} n = (f n).1 := by
    apply List.ext_getElem (by rw [length_prefixOf, (f n).2.2])
    intro i hi1 hi2
    have below : i + 1 ≤ n := by rw [length_prefixOf] at hi1; omega
    have bit : (f n).1[i] = (f (i + 1)).1.getD i false := by
      have long : i < (f (i + 1)).1.length := by rw [(f (i + 1)).2.2]; omega
      rw [getD_eq_getElem' long]
      have := compatible below
      simp only [← this, List.getElem_take]
    rw [bit, Bool.eq_iff_iff, getElem_prefixOf]
    rfl
  rw [key]
  exact (f n).2.1

/-- **The full power set satisfies weak König's lemma.** -/
theorem univ_WKL : WKL (Set.univ : Set (Set ℕ)) := fun _ _ hT levels =>
  let ⟨X, hX⟩ := exists_path hT levels
  ⟨X, trivial, hX⟩

theorem univ_modelsWKL0 (σ : Signature) : ModelsWKL0 σ Set.univ :=
  ⟨univ_models_RCA0, univ_WKL⟩

/-! ## Diagonally noncomputable functions -/

/-- `φ_e(e)` observed within `n` steps. -/
def diagObserved (n e : ℕ) : Option ℕ :=
  Code.evaln n (Denumerable.ofNat Code e) e

/-- `f` differs from `φ_e(e)` whenever the latter converges. -/
def IsDNR (f : ℕ → ℕ) : Prop :=
  ∀ e y, y ∈ Code.eval (Denumerable.ofNat Code e) e → f e ≠ y

/-- **No diagonally noncomputable function is computable.** -/
theorem not_computable_of_isDNR {f : ℕ → ℕ} (hf : IsDNR f) : ¬ Computable f := by
  intro computable
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp computable)
  refine hf (encode c) (f (encode c)) ?_ rfl
  rw [Denumerable.ofNat_encode, hc]
  exact Part.mem_some _

/-- The graph of a function, coded by pairing. -/
def graph (f : ℕ → ℕ) : Set ℕ :=
  {m | (Nat.unpair m).2 = f (Nat.unpair m).1}

/-- `S` contains the graph of a diagonally noncomputable function: the
unrelativized instance of the principle DNR. -/
def HasDNR (S : Set (Set ℕ)) : Prop :=
  ∃ f, IsDNR f ∧ graph f ∈ S

/-- A function with a recursive graph is computable. -/
theorem computable_of_graph_recursive {f : ℕ → ℕ} (h : IsRecursiveSet (graph f)) :
    Computable f := by
  classical
  have decideGraph := ComputablePred.decide h
  have search : Partrec fun n => Nat.rfind fun y => Part.some (decide (Nat.pair n y ∈ graph f)) :=
    Partrec.rfind ((decideGraph.comp Primrec₂.natPair.to_comp).partrec :
      Partrec₂ fun (n y : ℕ) => Part.some (decide (Nat.pair n y ∈ graph f)))
  refine search.of_eq_tot fun n => ?_
  refine Nat.mem_rfind.mpr ⟨by simp [graph], fun {m} lt => ?_⟩
  simp only [graph, Set.mem_ofPred_eq, Nat.unpair_pair, Part.mem_some_iff]
  simp only [Bool.false_eq, decide_eq_false_iff_not]
  omega

/-- **The recursive sets contain no diagonally noncomputable function.** -/
theorem not_hasDNR_recursiveSets : ¬ HasDNR recursiveSets := by
  rintro ⟨f, hf, recursive⟩
  exact not_computable_of_isDNR hf (computable_of_graph_recursive recursive)

/-! ## The Kleene tree -/

/-- The Kleene tree: `s` avoids `φ_e(e) mod 2` at every position `e` whose
diagonal computation converges within `|s|` steps. -/
def kleeneTree : Set (List Bool) :=
  {s | ∀ e < s.length, ∀ y, diagObserved s.length e = some y → s.getD e false ≠ decide (y % 2 = 1)}

theorem getD_take {s : List Bool} {k e : ℕ} (h : e < k) :
    (s.take k).getD e false = s.getD e false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
  simp [h]

theorem kleeneTree_isTree : IsTree kleeneTree := by
  intro s hs k e he y hy
  have short : (s.take k).length ≤ s.length := by simp
  simp only [List.length_take] at he
  have hek : e < k := by omega
  have hes : e < s.length := by omega
  have mono : diagObserved s.length e = some y := Code.evaln_mono short hy
  rw [getD_take hek]
  exact hs e hes y mono

/-- The node of length `n` that chooses, at each converged position, the bit
opposite to the diagonal value. -/
def kleeneWitness (n : ℕ) : List Bool :=
  (List.range n).map fun e => (diagObserved n e).elim false fun y => !decide (y % 2 = 1)

theorem length_kleeneWitness (n : ℕ) : (kleeneWitness n).length = n := by
  simp [kleeneWitness]

theorem kleeneWitness_mem (n : ℕ) : kleeneWitness n ∈ kleeneTree := by
  intro e he y hy
  rw [length_kleeneWitness] at he hy
  rw [getD_eq_getElem' (by rw [length_kleeneWitness]; exact he)]
  simp [kleeneWitness, hy]

theorem kleeneTree_hasAllLevels : HasAllLevels kleeneTree :=
  fun n => ⟨kleeneWitness n, kleeneWitness_mem n, length_kleeneWitness n⟩

/-- The local test at position `e`. -/
def kleeneLocal (e : ℕ) (s : List Bool) : Bool :=
  (diagObserved s.length e).elim true fun y => s.getD e false != decide (y % 2 = 1)

theorem mem_kleeneTree_iff (s : List Bool) :
    s ∈ kleeneTree ↔ ∀ e < s.length, kleeneLocal e s = true := by
  simp only [kleeneTree, Set.mem_ofPred_eq, kleeneLocal]
  refine forall_congr' fun e => imp_congr_right fun _ => ?_
  cases diagObserved s.length e with
  | none => simp
  | some y => simp

theorem kleeneLocal_primrec : Primrec₂ kleeneLocal := by
  have observed : Primrec fun p : ℕ × List Bool => diagObserved p.2.length p.1 :=
    Code.primrec_evaln.comp (Primrec.pair
      (Primrec.pair (Primrec.list_length.comp Primrec.snd) ((Primrec.ofNat Code).comp Primrec.fst))
      Primrec.fst)
  have bit : Primrec₂ fun (p : ℕ × List Bool) (y : ℕ) =>
      p.2.getD p.1 false != decide (y % 2 = 1) :=
    (Primrec.not.comp (Primrec.beq.comp
      ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
      (Primrec.eq.decide.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
        (Primrec.const 1)))).of_eq fun _ => rfl
  exact (Primrec.option_casesOn observed (Primrec.const true) bit).of_eq fun p => by
    simp only [kleeneLocal]
    cases diagObserved p.2.length p.1 <;> rfl

/-- **The Kleene tree is a recursive tree.** -/
theorem codeOf_kleeneTree_recursive : IsRecursiveSet (codeOf kleeneTree) := by
  classical
  have local' : PrimrecRel fun e s => kleeneLocal e s = true :=
    primrecRel_iff_primrec_decide.mpr (kleeneLocal_primrec.of_eq fun e s => by simp)
  have check : PrimrecPred fun s : List Bool => ∀ e < s.length, kleeneLocal e s = true :=
    (local'.forall_mem_list.comp (Primrec.list_range.comp Primrec.list_length) Primrec.id).of_eq
      (by simp)
  have decider : Primrec fun n : ℕ =>
      (decode₂ (List Bool) n).elim false fun s =>
        decide (∀ e < s.length, kleeneLocal e s = true) :=
    (Primrec.option_casesOn Primrec.decode₂ (Primrec.const false)
      (check.decide.comp Primrec.snd).to₂).of_eq fun n => by
        cases decode₂ (List Bool) n <;> rfl
  refine ⟨inferInstance, decider.to_comp.of_eq fun n => ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  show _ ↔ n ∈ codeOf kleeneTree
  rw [mem_codeOf_iff]
  cases h : decode₂ (List Bool) n with
  | none => simp
  | some s => simp [mem_kleeneTree_iff]

/-- The indicator of a set as a function. -/
noncomputable def indicator (X : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if n ∈ X then 1 else 0

/-- **Every path through the Kleene tree is diagonally noncomputable.** -/
theorem isDNR_of_isPath_kleeneTree {X : Set ℕ} (hX : IsPath X kleeneTree) :
    IsDNR (indicator X) := by
  classical
  intro e y hy
  obtain ⟨k, hk⟩ := Code.evaln_complete.mp hy
  set n := max k (e + 1)
  have en : e < n := lt_of_lt_of_le (Nat.lt_succ_self e) (le_max_right _ _)
  have node := hX n
  have he : e < (prefixOf X n).length := by rw [length_prefixOf]; exact en
  have observed : diagObserved (prefixOf X n).length e = some y := by
    rw [length_prefixOf]
    exact Code.evaln_mono (le_max_left _ _) hk
  have differs := node e he y observed
  have bit := getD_prefixOf X en (i := e)
  unfold indicator
  by_cases member : e ∈ X
  · have one : (prefixOf X n).getD e false = true := bit.mpr member
    rw [one] at differs
    simp only [member, if_true]
    intro same
    subst same
    simp at differs
  · have zero : (prefixOf X n).getD e false = false := by
      cases h : (prefixOf X n).getD e false
      · rfl
      · exact absurd (bit.mp h) member
    rw [zero] at differs
    simp only [member, if_false]
    intro same
    subst same
    simp at differs

/-- **In a Turing ideal, weak König's lemma gives a diagonally noncomputable
function.** -/
theorem IsTuringIdeal.hasDNR_of_WKL {S : Set (Set ℕ)} (hS : IsTuringIdeal S) (hW : WKL S) :
    HasDNR S := by
  classical
  have codeMem := hS.recursive_mem codeOf_kleeneTree_recursive
  obtain ⟨X, hXS, path⟩ := hW _ codeMem
    (by rw [treeOf_codeOf]; exact kleeneTree_isTree)
    (by rw [treeOf_codeOf]; exact kleeneTree_hasAllLevels)
  rw [treeOf_codeOf] at path
  refine ⟨indicator X, isDNR_of_isPath_kleeneTree path, hS.down hXS ?_⟩
  refine setTuringLE_of_decide ?_
  have query := mem_comp (A := X) (Set.mem_singleton _)
    (ofPrimrec (f := fun m : ℕ => (Nat.unpair m).1) (Primrec.fst.comp Primrec.unpair) id')
  have compare := ofPrimrec₂ (f := fun (m : ℕ) (b : Bool) => decide ((Nat.unpair m).2 = bif b then 1 else 0))
    (Primrec.eq.decide.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0))) id' query
  refine of_eq compare fun m => ?_
  rw [Bool.eq_iff_iff]
  simp only [graph, Set.mem_ofPred_eq, indicator, decide_eq_true_iff]
  by_cases member : (Nat.unpair m).1 ∈ X <;> simp [member]

/-- **The recursive sets do not satisfy weak König's lemma.** -/
theorem recursiveSets_not_WKL : ¬ WKL recursiveSets :=
  fun hW => not_hasDNR_recursiveSets (recursiveSets_isTuringIdeal.hasDNR_of_WKL hW)

/-- **RCA₀ does not ω-entail WKL**: the recursive sets are an ω-model of RCA₀
and not of WKL₀. -/
theorem recursiveSets_separates_RCA0_WKL0 {σ : Signature} (hσ : σ.IsComputable) :
    Models recursiveSets (RCA0 : Set (Formula σ)) ∧ ¬ ModelsWKL0 σ recursiveSets :=
  ⟨recursiveSets_models_RCA0 hσ, fun h => recursiveSets_not_WKL h.2⟩

/-! ## Arithmetical comprehension gives a diagonally noncomputable function -/

/-- `φ_e(e) + 1` if it converges within `s` steps, else `0`. -/
def diagValue (e s : ℕ) : ℕ :=
  (diagObserved s e).elim 0 (· + 1)

theorem diagValue_primrec : Primrec₂ diagValue := by
  have observed : Primrec fun p : ℕ × ℕ => diagObserved p.2 p.1 :=
    Code.primrec_evaln.comp (Primrec.pair
      (Primrec.pair Primrec.snd ((Primrec.ofNat Code).comp Primrec.fst)) Primrec.fst)
  exact (Primrec.option_casesOn observed (Primrec.const 0)
    (Primrec.succ.comp Primrec.snd).to₂).of_eq fun p => by
      simp only [diagValue]
      cases diagObserved p.2 p.1 <;> rfl

/-- `e ↦ φ_e(e) + 1`, and `0` where `φ_e(e)` diverges. -/
noncomputable def dnrWitness (e : ℕ) : ℕ := by
  classical
  exact if h : (Code.eval (Denumerable.ofNat Code e) e).Dom then
    (Code.eval (Denumerable.ofNat Code e) e).get h + 1 else 0

theorem dnrWitness_isDNR : IsDNR dnrWitness := by
  intro e y hy
  have dom : (Code.eval (Denumerable.ofNat Code e) e).Dom := Part.dom_iff_mem.mpr ⟨y, hy⟩
  simp only [dnrWitness, dom, dite_true, Part.get_eq_of_mem hy dom]
  omega

theorem diagValue_cases (e s : ℕ) :
    diagValue e s = 0 ∨ ∃ x, diagObserved s e = some x ∧ diagValue e s = x + 1 := by
  unfold diagValue
  cases diagObserved s e with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl, rfl⟩

theorem dnrWitness_eq_iff (e y : ℕ) :
    dnrWitness e = y ↔ (∃ s, diagValue e s = y ∧ 0 < y) ∨ (y = 0 ∧ ∀ s, diagValue e s = 0) := by
  classical
  by_cases dom : (Code.eval (Denumerable.ofNat Code e) e).Dom
  · set x := (Code.eval (Denumerable.ofNat Code e) e).get dom
    have value : dnrWitness e = x + 1 := by simp [dnrWitness, dom, x]
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp (Part.get_mem dom)
    have atK : diagValue e k = x + 1 := by
      simp only [diagValue, diagObserved]
      rw [Option.mem_def] at hk
      simp [hk, x]
    rw [value]
    constructor
    · rintro rfl
      exact Or.inl ⟨k, atK, by omega⟩
    · rintro (⟨s, hs, pos⟩ | ⟨zero, all⟩)
      · rcases diagValue_cases e s with z | ⟨x', hx', hv⟩
        · omega
        · have mem : x' ∈ Code.eval (Denumerable.ofNat Code e) e := Code.evaln_sound hx'
          have same : x' = x := Part.mem_unique mem (Part.get_mem dom)
          omega
      · have := all k
        omega
  · have value : dnrWitness e = 0 := by simp [dnrWitness, dom]
    have allZero : ∀ s, diagValue e s = 0 := by
      intro s
      rcases diagValue_cases e s with z | ⟨x', hx', _⟩
      · exact z
      · exact absurd (Part.dom_iff_mem.mpr ⟨x', Code.evaln_sound hx'⟩) dom
    rw [value]
    constructor
    · rintro rfl
      exact Or.inr ⟨rfl, allZero⟩
    · rintro (⟨s, hs, pos⟩ | ⟨zero, _⟩)
      · rw [allZero s] at hs
        omega
      · exact zero.symm

/-- The pairing projections and the diagonal values as primitive recursive
symbols. -/
def unpairFstSymbol : Signature.primrec.Fn :=
  ⟨fun m _ => (Nat.unpair m).1, (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).to₂⟩

def unpairSndSymbol : Signature.primrec.Fn :=
  ⟨fun m _ => (Nat.unpair m).2, (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to₂⟩

def diagValueSymbol : Signature.primrec.Fn := ⟨diagValue, diagValue_primrec⟩

/-- The arithmetical definition of the graph of `dnrWitness`, with the coded
pair `⟨e, y⟩` as number variable `0`:
`(∃s val(e, s) = y ∧ 0 < y) ∨ (y = 0 ∧ ∀s val(e, s) = 0)`. -/
def dnrGraphFormula : Formula Signature.primrec :=
  or (ex (and (eq (app diagValueSymbol (app unpairFstSymbol (var 1) zero) (var 0))
          (app unpairSndSymbol (var 1) zero))
        (lt zero (app unpairSndSymbol (var 1) zero))))
    (and (eq (app unpairSndSymbol (var 0) zero) zero)
      (all (eq (app diagValueSymbol (app unpairFstSymbol (var 1) zero) (var 0)) zero)))

theorem dnrGraphFormula_isArithmetical : IsArithmetical dnrGraphFormula :=
  .or (.ex (.and (.eq _ _) (.lt _ _))) (.and (.eq _ _) (.all (.eq _ _)))

theorem holds_dnrGraphFormula (S : Set (Set ℕ)) (m : ℕ) (v : ℕ → ℕ) (V : ℕ → Set ℕ) :
    Holds S dnrGraphFormula (Env.cons m v) V ↔ m ∈ graph dnrWitness := by
  rw [show m ∈ graph dnrWitness ↔ dnrWitness (Nat.unpair m).1 = (Nat.unpair m).2 from eq_comm,
    dnrWitness_eq_iff]
  simp [dnrGraphFormula, Holds, Term.eval, diagValueSymbol, unpairFstSymbol, unpairSndSymbol,
    Signature.primrec]

/-- **Every ω-model of ACA₀ contains a diagonally noncomputable function.** -/
theorem Models.hasDNR {S : Set (Set ℕ)} (h : Models S (ACA0 : Set (Formula Signature.primrec))) :
    HasDNR S := by
  obtain ⟨⟨A, hA⟩, closed⟩ := (models_ACA0_iff S).mp h
  obtain ⟨X, member, spec⟩ := closed dnrGraphFormula dnrGraphFormula_isArithmetical
    (fun _ => 0) (fun _ => A) (fun _ => hA)
  have same : X = graph dnrWitness := by
    ext m
    rw [spec m, holds_dnrGraphFormula]
  exact ⟨dnrWitness, dnrWitness_isDNR, same ▸ member⟩

/-! ## Examples -/

/-- Positive example of `IsTree` and `HasAllLevels`: the full binary tree. -/
example : IsTree Set.univ ∧ HasAllLevels Set.univ :=
  ⟨fun _ _ _ => trivial, fun n => ⟨List.replicate n false, trivial, by simp⟩⟩

/-- Negative example: `{[true]}` is not a tree (it misses the empty prefix),
and the tree `{[]}` has no node of length one. -/
example : ¬ IsTree {[true]} := by
  intro h
  have := h [true] rfl 0
  simp at this

example : ¬ HasAllLevels {[]} := by
  intro h
  obtain ⟨s, hs, hl⟩ := h 1
  rw [Set.mem_singleton_iff] at hs
  subst hs
  simp at hl

#print axioms exists_path
#print axioms codeOf_kleeneTree_recursive
#print axioms isDNR_of_isPath_kleeneTree
#print axioms IsTuringIdeal.hasDNR_of_WKL
#print axioms recursiveSets_not_WKL
#print axioms recursiveSets_separates_RCA0_WKL0
#print axioms Models.hasDNR
#print axioms not_hasDNR_recursiveSets

end Mettapedia.Logic.ReverseMathematics
