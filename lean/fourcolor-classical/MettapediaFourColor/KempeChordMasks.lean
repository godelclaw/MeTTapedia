import MettapediaFourColor.KempeChordExchange

/-!
# Coupled exchanges through the active boundary

A Boolean mask selects the endpoints whose two non-fixed colours are exchanged.
Its bits must agree at the two ends of every exterior chord. Fixed-colour ports
can be eliminated from this relation and reinserted without losing the original
chromogram or the reconstructed trace.

This is the classical Kempe exchange action, expressed separately from a graph's
profile or reducibility certificate. The finite six-active-port two-ear fact
below has consumers in each of the three diamond cores.
-/

namespace FourColor.KempeChordMasks

open Color

/-- Forget fixed ports and chord parity; retain the ordered opening/closing pattern. -/
def skeleton : Chromogram → List Bool
  | [] => []
  | .skip :: w => skeleton w
  | .push :: w => true :: skeleton w
  | .pop0 :: w | .pop1 :: w => false :: skeleton w

/-- A mask has the same bit at both ends of every chord. -/
def paired : List Bool → List Bool → List Bool → Bool
  | stack, [], [] => stack.isEmpty
  | stack, b :: bs, true :: ds => paired (b :: stack) bs ds
  | a :: stack, b :: bs, false :: ds => (a == b) && paired stack bs ds
  | _, _, _ => false

/-- Reinsert all fixed ports while exchanging exactly the selected active ports. -/
def recolor : List Bool → List Color → List Color
  | _, [] => []
  | mask, c :: cs =>
    if c.hi then
      (if mask.headD false then EdgePerm.e132 c else c) :: recolor mask.tail cs
    else c :: recolor mask cs

/-- A compatible active mask reconstructs a trace for the very same exterior. -/
theorem recolor_matches : ∀ (w : Chromogram) (et : List Color) (mask : List Bool)
    (stack bits : List Bool), matchg stack et w → paired bits mask (skeleton w) →
    matchg (List.zipWith xor stack bits) (recolor mask et) w := by
  intro w
  induction w with
  | nil =>
    intro et mask stack bits hm hp
    cases et <;> cases mask <;> cases stack <;> cases bits <;>
      simp_all [matchg, skeleton, paired, recolor]
  | cons s w ih =>
    intro et mask stack bits hm hp
    cases et with
    | nil => simp at hm
    | cons c et =>
      cases s with
      | skip =>
        cases c <;> simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at hm
        simpa [recolor, matchg, matchStep] using ih et mask stack bits hm hp
      | push =>
        cases mask with
        | nil => simp [skeleton, paired] at hp
        | cons b mask =>
          cases c <;> cases b <;>
            simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at hm
          all_goals
            simpa [recolor, matchg, matchStep, EdgePerm.apply] using
              ih et mask _ _ hm hp
      | pop0 =>
        cases stack with
        | nil => cases c <;> simp [matchg, matchStep] at hm
        | cons a stack =>
          cases bits with
          | nil => cases mask <;> simp [skeleton, paired] at hp
          | cons b bits =>
            cases mask with
            | nil => simp [skeleton, paired] at hp
            | cons d mask =>
              simp only [skeleton, paired, Bool.and_eq_true, beq_iff_eq] at hp
              rcases hp with ⟨rfl, hp⟩
              cases c <;> cases a <;> cases b <;>
                simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at hm
              all_goals
                simpa [recolor, matchg, matchStep, EdgePerm.apply] using
                  ih et mask stack bits hm hp
      | pop1 =>
        cases stack with
        | nil => cases c <;> simp [matchg, matchStep] at hm
        | cons a stack =>
          cases bits with
          | nil => cases mask <;> simp [skeleton, paired] at hp
          | cons b bits =>
            cases mask with
            | nil => simp [skeleton, paired] at hp
            | cons d mask =>
              simp only [skeleton, paired, Bool.and_eq_true, beq_iff_eq] at hp
              rcases hp with ⟨rfl, hp⟩
              cases c <;> cases a <;> cases b <;>
                simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at hm
              all_goals
                simpa [recolor, matchg, matchStep, EdgePerm.apply] using
                  ih et mask stack bits hm hp

/-- The active positions are the ones on which the two-colour action is nontrivial. -/
def active (et : List Color) : List Color := et.filter Color.hi

/-- Balanced unsigned chord brackets, with an explicit initial depth. -/
def balanced : ℕ → List Bool → Bool
  | d, [] => d == 0
  | d, true :: ds => balanced (d + 1) ds
  | 0, false :: _ => false
  | d + 1, false :: ds => balanced d ds

theorem matched_skeleton : ∀ (w : Chromogram) (et : List Color) (stack : List Bool),
    matchg stack et w → balanced stack.length (skeleton w) = true ∧
      (skeleton w).length = (active et).length := by
  intro w
  induction w with
  | nil =>
    intro et stack h
    cases et <;> cases stack <;> simp_all [matchg, skeleton, balanced, active]
  | cons s w ih =>
    intro et stack h
    cases et with
    | nil => simp at h
    | cons c et =>
      cases s with
      | skip =>
        cases c <;> simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h
        simpa [skeleton, active] using ih et stack h
      | push =>
        cases c <;> simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h
        all_goals
          obtain ⟨hb, hl⟩ := ih et _ h
          simpa [skeleton, active, balanced, List.filter_cons, Color.hi] using And.intro hb hl
      | pop0 =>
        cases stack with
        | nil => cases c <;> simp [matchg, matchStep] at h
        | cons a stack =>
          cases c <;> cases a <;>
            simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h
          all_goals
            obtain ⟨hb, hl⟩ := ih et stack h
            simpa [skeleton, active, balanced, List.filter_cons, Color.hi] using And.intro hb hl
      | pop1 =>
        cases stack with
        | nil => cases c <;> simp [matchg, matchStep] at h
        | cons a stack =>
          cases c <;> cases a <;>
            simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h
          all_goals
            obtain ⟨hb, hl⟩ := ih et stack h
            simpa [skeleton, active, balanced, List.filter_cons, Color.hi] using And.intro hb hl

/-- Endpoints of a cyclically adjacent pair of active ports. -/
def ear (n i : ℕ) : List Bool :=
  (List.range n).map fun j => decide (j = i ∨ j = (i + 1) % n)

/-- Unordered pairs of disjoint cyclic ears. -/
def earPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => ((List.range n).filter fun j =>
    decide (i < j) &&
      (List.zipWith (fun a b => !(a && b)) (ear n i) (ear n j)).all id).map (i, ·)

/-- Exchange either ear or both, retaining their common exterior. -/
def jointMasks (n : ℕ) (p : ℕ × ℕ) : List (List Bool) :=
  [ear n p.1, ear n p.2, List.zipWith xor (ear n p.1) (ear n p.2)]

/-- One finite planar fact, independent of colours, ranks and configurations. -/
theorem six_checked : ∀ d : Fin 6 → Bool,
    balanced 0 (List.ofFn d) = true →
      (earPairs 6).any (fun p =>
        (jointMasks 6 p).all fun m => paired [] m (List.ofFn d)) = true := by
  decide +kernel

theorem six_ears (ds : List Bool) (hlen : ds.length = 6)
    (hb : balanced 0 ds = true) :
    ∃ p ∈ earPairs 6, ∀ m ∈ jointMasks 6 p, paired [] m ds = true := by
  let d : Fin 6 → Bool := fun i => ds[i.val]'(by omega)
  have hd : List.ofFn d = ds := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i h₁ h₂
      simp only [List.getElem_ofFn]
      rfl
  have h := six_checked d (by simpa only [hd] using hb)
  rw [hd] at h
  obtain ⟨p, hp, hm⟩ := List.any_eq_true.mp h
  exact ⟨p, hp, List.all_eq_true.mp hm⟩

/-- Every disjoint-ear choice must offer an accepted joint exchange. -/
def coverCheck (et : List Color) (answers : List (List Color)) : Bool :=
  decide ((active et).length = 6) &&
    (earPairs 6).all fun p =>
      (jointMasks 6 p).any fun m => answers.contains (recolor m et)

/-- The same paired-mask theorem covers any number of intervening fixed ports. -/
theorem coverCheck_sound (et : List Color) (answers : List (List Color))
    (hc : coverCheck et answers = true) (w : Chromogram) (hm : matchg [] et w) :
    ∃ answer ∈ answers, matchg [] answer w := by
  rw [coverCheck, Bool.and_eq_true] at hc
  obtain ⟨hlen, hc⟩ := hc
  have hlen := of_decide_eq_true hlen
  obtain ⟨hb, hs⟩ := matched_skeleton w et [] hm
  obtain ⟨p, hp, hmask⟩ := six_ears (skeleton w) (hs.trans hlen) hb
  obtain ⟨mask, hmem, ha⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc p hp)
  refine ⟨recolor mask et, (by simpa using ha), ?_⟩
  exact recolor_matches w et mask [] [] hm (hmask mask hmem)

end FourColor.KempeChordMasks
