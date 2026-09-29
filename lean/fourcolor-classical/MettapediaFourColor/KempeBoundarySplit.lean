import FourColor.Kempe
import FourColor.CertBase
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Kempe repair under a boundary split

Replace one nonzero edge colour by two distinct nonzero colours whose sum is
the original colour. The corresponding chromogram operation preserves every
matching answer after collapse. Consequently splitting a Kempe-closed boundary
relation remains Kempe-closed, and a repair in the larger interface descends
whenever its terminal witnesses reconstruct on the smaller interface.

Chromograms and the parity-negation lemma are reused from the Gonthier/Emery
development. The transfer retains the relation between the two new ports.
-/

namespace FourColor.KempeBoundarySplit

open Color

private theorem add_def (a b : Color) : a + b = Color.add a b := rfl

/-- Expand the first edge into a trivalent boundary junction. -/
def splitGram (firstSkip : Bool) : Chromogram → Chromogram
  | .skip :: w => .push :: .pop1 :: w
  | .push :: w =>
    if firstSkip then .skip :: .push :: gramNeg w else .push :: .skip :: gramNeg w
  | _ => [.pop0]

/-- The split matches the original exactly when its two new colours are proper. -/
theorem match_split (a b : Color) (t : List Color) (w : Chromogram)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    matchg [] (a :: b :: t) (splitGram (a == c1) w) =
      matchg [] ((a + b) :: t) w := by
  cases w with
  | nil => cases a <;> rfl
  | cons s w =>
    cases s <;> cases a <;> cases b <;>
      simp_all [splitGram, matchg, matchStep, matchg_gramNeg] <;> rfl

private theorem split_pair (flag : Bool) (w : Chromogram) (a b : Color) (t : List Color) :
    matchg [] (a :: b :: t) (splitGram flag w) →
      a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ matchg [] ((a + b) :: t) w := by
  cases w with
  | nil => cases a <;> simp [splitGram, matchg, matchStep]
  | cons s w =>
    cases s <;> cases flag <;> cases a <;> cases b <;>
      simp [add_def, Color.add, splitGram, matchg, matchStep, matchg_gramNeg]

/-- Every answer has a genuine proper collapse, including its colouring data. -/
theorem collapse_match (flag : Bool) (w : Chromogram) (et : List Color)
    (h : matchg [] et (splitGram flag w)) :
    ∃ a b t, et = a :: b :: t ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      matchg [] ((a + b) :: t) w := by
  cases et with
  | nil => cases w with
    | nil => simp [splitGram] at h
    | cons s w => cases s <;> cases flag <;> simp [splitGram] at h
  | cons a et =>
    cases et with
    | nil =>
      cases w with
      | nil => cases a <;> simp [splitGram, matchg, matchStep] at h
      | cons s w =>
        cases s <;> cases flag <;> cases a <;> simp [splitGram, matchg, matchStep] at h
    | cons b t => exact ⟨a, b, t, rfl, split_pair flag w a b t h⟩

/-- Keep both new colours and the old relation on their sum. -/
def Split (P : List Color → Prop) (et : List Color) : Prop :=
  ∃ a b t, et = a :: b :: t ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ P ((a + b) :: t)

theorem closed {P : List Color → Prop} (hP : KempeClosed P) : KempeClosed (Split P) := by
  rintro _ ⟨a, b, t, rfl, ha, hb, hab, ht⟩
  obtain ⟨hperm, w, hw, hall⟩ := hP _ ht
  constructor
  · intro g
    refine ⟨g a, g b, t.map g, rfl, ?_, ?_, ?_, ?_⟩
    · intro h; exact ha (g.apply_injective (by simpa using h))
    · intro h; exact hb (g.apply_injective (by simpa using h))
    · exact fun h => hab (g.apply_injective h)
    · simpa only [List.map_cons, EdgePerm.apply_add] using hperm g
  · refine ⟨splitGram (a == c1) w, ?_, ?_⟩
    · rw [match_split a b t w ha hb hab]
      exact hw
    · intro et het
      obtain ⟨a', b', t', rfl, ha', hb', hab', hm⟩ := collapse_match _ _ _ het
      exact ⟨a', b', t', rfl, ha', hb', hab', hall _ hm⟩

/-- A repair descends when every successful split answer reconstructs below. -/
theorem coclosure_collapse {P Q : List Color → Prop}
    (reconstruct : ∀ a b t, a ≠ 0 → b ≠ 0 → a ≠ b → Q (a :: b :: t) → P ((a + b) :: t))
    (a b : Color) (t : List Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (repair : KempeCoclosure Q (a :: b :: t)) : KempeCoclosure P ((a + b) :: t) := by
  intro outside hout hold
  obtain ⟨et, hQ, a', b', t', rfl, ha', hb', hab', ht'⟩ :=
    repair (Split outside) (closed hout) ⟨a, b, t, rfl, ha, hb, hab, hold⟩
  exact ⟨_, reconstruct a' b' t' ha' hb' hab' hQ, ht'⟩

/-- D-repair for all proper zero-sum traces of the stated boundary length. -/
def Repairs (P : List Color → Prop) (n : ℕ) : Prop :=
  ∀ et, et.length = n → (0 : Color) ∉ et → et.sum = 0 → KempeCoclosure P et

/-- A split interface supplies repair for every proper trace below it. -/
theorem repairs_collapse {P Q : List Color → Prop} {n : ℕ}
    (reconstruct : ∀ a b t, a ≠ 0 → b ≠ 0 → a ≠ b → Q (a :: b :: t) → P ((a + b) :: t))
    (hn : 0 < n) (repair : Repairs Q (n + 1)) : Repairs P n := by
  intro et hlen hzero hsum
  cases et with
  | nil => simp at hlen; omega
  | cons c t =>
    have hc : c ≠ 0 := fun h => hzero (by simp [h])
    obtain ⟨a, b, ha, hb, hab, rfl⟩ :
        ∃ a b : Color, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ a + b = c := by
      revert hc
      cases c <;> decide
    apply coclosure_collapse reconstruct a b t ha hb hab
    apply repair
    · simpa using hlen
    · simpa only [List.mem_cons, not_or, ne_eq, eq_comm] using
        And.intro ha (And.intro hb (fun h => hzero (List.mem_cons_of_mem _ h)))
    · simpa only [List.sum_cons, add_assoc] using hsum

/-- Rotate the complete boundary relation, retaining all witnesses. -/
def Rotated (P : List Color → Prop) (et : List Color) : Prop :=
  ∃ es, es.rotate 1 = et ∧ P es

/-- The rotation proof follows the chromogram transport in the reference development. -/
theorem closed_rotated {P : List Color → Prop} (hP : KempeClosed P) : KempeClosed (Rotated P) := by
  rintro _ ⟨es, rfl, hes⟩
  obtain ⟨hperm, w, hw, hall⟩ := hP es hes
  refine ⟨fun g => ⟨es.map g, by rw [List.map_rotate], hperm g⟩, gramRot w, ?_, ?_⟩
  · rw [matchg_gramRot]; exact hw
  · intro et het
    obtain ⟨es, rfl⟩ := Hypermap.exists_rotate_one et
    rw [matchg_gramRot] at het
    exact ⟨es, rfl, hall _ het⟩

theorem coclosure_rotate_back {P Q : List Color → Prop}
    (reconstruct : ∀ es, Q (es.rotate 1) → P es) {et : List Color}
    (repair : KempeCoclosure Q (et.rotate 1)) : KempeCoclosure P et := by
  intro outside hout hold
  obtain ⟨_, hQ, es, rfl, hes⟩ :=
    repair (Rotated outside) (closed_rotated hout) ⟨et, rfl, hold⟩
  exact ⟨es, reconstruct es hQ, hes⟩

/-- The boundary trace of a graph colouring, with its ports ordered explicitly. -/
def GraphTrace {V : Type*} (G : SimpleGraph V) (ports : List V) (et : List Color) : Prop :=
  ∃ k : G.Coloring Color, et = trace (ports.map k)

theorem graph_rotate_back {V : Type*} {G : SimpleGraph V} {ports : List V}
    {et : List Color} (n : ℕ)
    (repair : KempeCoclosure (GraphTrace G (ports.rotate n)) (et.rotate n)) :
    KempeCoclosure (GraphTrace G ports) et := by
  induction n generalizing ports et with
  | zero => simpa using repair
  | succ n ih =>
    apply coclosure_rotate_back (Q := GraphTrace G (ports.rotate 1))
      (fun es ⟨k, hk⟩ => ⟨k, List.rotate_injective 1 (by
        simpa only [List.map_rotate, trace_rotate] using hk)⟩)
    apply ih
    simpa only [List.rotate_rotate, Nat.add_comm 1] using repair

theorem ring_rotate_back {D : Type*} {G : Hypermap D} {r : List D}
    {et : List Color}
    (repair : KempeCoclosure (G.RingTrace (r.rotate 1)) (et.rotate 1)) :
    KempeCoclosure (G.RingTrace r) et :=
  coclosure_rotate_back (fun es ⟨k, hk, ht⟩ => ⟨k, hk, List.rotate_injective 1 (by
    simpa only [List.map_rotate, trace_rotate] using ht)⟩) repair

end FourColor.KempeBoundarySplit
