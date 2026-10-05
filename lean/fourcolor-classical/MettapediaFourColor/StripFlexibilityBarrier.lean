import MettapediaFourColor.StripChainRepair

/-! # Repairable inputs without greedy growth of joint-relation sizes

Both forced-chain inputs have a compatible repair. Nevertheless, for each
of the three Kempe palettes there is an admissible noncrossing matching
whose every batch switch weakly decreases all six evaluated relation sizes.
Thus no coordinatewise increasing score of those sizes can guarantee strict
one-round progress in the universal matching model.

The matchings are mathematical boundary contracts. Simultaneous realization
by one physical exterior is not asserted. The result excludes this greedy
criterion, not repair with neutral steps, temporary regression or more state.
-/

namespace FourColor.StripFlexibilityBarrier

open Color StripResponseSummary StripCriticalChain KempeMatchingChromogram

set_option maxRecDepth 10000

def fixed : Fin 3 → Color := ![c1,c2,c3]
def palette : Fin 3 → EdgePerm := ![.e123,.e213,.e321]

theorem fixed_complete : ∀ c : Color, c ≠ 0 → ∃ p, fixed p = c := by decide +kernel

def chord : Bool → Fin 3 → Fin 5 → Fin 11 × Fin 11
  | false => ![![(1,10),(2,6),(0,0),(0,0),(0,0)],
    ![(0,10),(3,4),(5,9),(7,8),(0,0)], ![(0,1),(2,5),(3,4),(6,9),(7,8)]]
  | true => ![![(1,2),(3,4),(5,9),(7,8),(0,0)],
    ![(0,2),(3,4),(5,8),(6,7),(9,10)], ![(0,1),(6,10),(0,0),(0,0),(0,0)]]

def mate : Bool → Fin 3 → Fin 11 → Fin 11
  | false => ![![0,10,6,3,4,5,2,7,8,9,1],![10,1,2,4,3,9,6,8,7,5,0],![1,0,5,4,3,2,9,8,7,6,10]]
  | true => ![![0,2,1,4,3,9,6,8,7,5,10],![2,1,0,4,3,8,7,6,5,10,9],![1,0,2,3,4,5,10,7,8,9,6]]

def normalized (s : Bool) (p : Fin 3) (i : Fin 11) : Color :=
  palette p (StripCriticalChain.boundary s i +
    StripCriticalChain.boundary s ⟨(i.val + 1) % 11, Nat.mod_lt _ (by decide)⟩)

def interval (b : Boundary) (c : Color) (a d : Fin 11) (i : Fin 11) : Color :=
  if a.val < i.val ∧ i.val ≤ d.val then c + b i else b i

def batch (s : Bool) (p : Fin 3) (bits : Fin 5 → Bool) : Boundary :=
  (List.finRange 5).foldl (fun b k => if bits k then
    interval b (fixed p) (chord s p k).1 (chord s p k).2 else b)
    (StripCriticalChain.boundary s)

def sizes (b : Boundary) (j : Fin 6) : ℕ :=
  (Finset.univ.filter (fun ac : Color × Color => relation b j ac.1 ac.2)).card

theorem matching_valid : ∀ s p, Function.Involutive (mate s p) ∧
    Noncrossing (mate s p) ∧ (∀ i, normalized s p i ≠ 0) ∧
    (∀ i, mate s p i = i ↔ normalized s p i = c1) := by
  unfold Function.Involutive
  decide +kernel

/-- The five slots enumerate all nontrivial chords; padding has empty support. -/
theorem chord_cover : ∀ s p,
    (∀ k, (chord s p k).1 ≤ (chord s p k).2 ∧
      ((chord s p k).1 = (chord s p k).2 ∨
        mate s p (chord s p k).1 = (chord s p k).2)) ∧
    (∀ i, mate s p i ≠ i → ∃ k,
      chord s p k = (min i (mate s p i), max i (mate s p i))) := by decide +kernel

theorem source_trace : ∀ s p,
    (trace (List.ofFn (StripCriticalChain.boundary s))).map (palette p) =
      List.ofFn (normalized s p) := by decide +kernel

theorem initial_matches (s p) : matchg [] (List.ofFn (normalized s p))
    (gram (mate s p) (normalized s p)) :=
  (reconstruct _ _ (matching_valid s p).1 (matching_valid s p).2.1
    (matching_valid s p).2.2.1 (matching_valid s p).2.2.2).1

/-- Every subset of whole chords stays in the original matching chromogram. -/
theorem batches_match : ∀ s p bits,
    matchg [] ((trace (List.ofFn (batch s p bits))).map (palette p))
      (gram (mate s p) (normalized s p)) := by decide +kernel

theorem initial_sizes : ∀ s, sizes (StripCriticalChain.boundary s) = ![3,2,2,2,1,0] := by
  decide +kernel

theorem sizes_nonincrease : ∀ s p bits,
    sizes (batch s p bits) ≤ sizes (StripCriticalChain.boundary s) := by
  change ∀ s p bits j, sizes (batch s p bits) j ≤ sizes (StripCriticalChain.boundary s) j
  decide +kernel

theorem batch_empty (s p bits) : ¬ ∃ a c, r5 (batch s p bits) a c := by
  have hle : sizes (batch s p bits) 5 ≤ 0 := calc
    _ ≤ sizes (StripCriticalChain.boundary s) 5 := sizes_nonincrease s p bits 5
    _ = 0 := congrFun (initial_sizes s) 5
  have hempty := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
  rintro ⟨a,c,h⟩
  have hm : (a,c) ∈ Finset.univ.filter
      (fun ac : Color × Color => relation (batch s p bits) 5 ac.1 ac.2) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, relation] using h
  rw [hempty] at hm
  exact Finset.notMem_empty _ hm

theorem batch_nonextension (s p bits) :
    ¬ StripSymbolicRepair.Terminal (trace (List.ofFn (batch s p bits))) :=
  no_trace _ (batch_empty s p bits)

/-- The obstruction applies to every increasing score, including positive
weighted sums and increasing lexicographic combinations. -/
theorem no_greedy_score {A : Type*} [Preorder A] (score : (Fin 6 → ℕ) → A)
    (increasing : Monotone score) (s p bits) :
    ¬ score (sizes (StripCriticalChain.boundary s)) < score (sizes (batch s p bits)) :=
  not_lt_of_ge (increasing (sizes_nonincrease s p bits))

/-- Successful compositional repair coexists with the greedy obstruction. -/
theorem repair_despite_barrier {A : Type*} [Preorder A]
    (score : (Fin 6 → ℕ) → A) (increasing : Monotone score) (s : Bool) :
    KempeCoclosure StripSymbolicRepair.Terminal
      (trace (List.ofFn (StripCriticalChain.boundary s))) ∧
    ∀ p bits, (¬ StripSymbolicRepair.Terminal (trace (List.ofFn (batch s p bits)))) ∧
      ¬ score (sizes (StripCriticalChain.boundary s)) < score (sizes (batch s p bits)) :=
  ⟨StripChainRepair.repair s, fun p bits =>
    ⟨batch_nonextension s p bits, no_greedy_score score increasing s p bits⟩⟩

end FourColor.StripFlexibilityBarrier
