import MettapediaFourColor.TriangleStripAnchors
import Mettapedia.GraphTheory.Kempe.ForestLists

/-!
# Joint anchor propagation and actual exterior reconstruction

Two jointly chosen colours break the cycles in each of the decoded cores
D0092, D0063 and D0099. After any valid propagation trace, supported nonempty
lists reconstruct a core colouring. The occurrence consumer glues it to the
same actual exterior, checking every crossing edge.

The general forest argument is independent of core size and palette. The
two-anchor bound is proved only for these sources. Support and nonemptiness
are explicit finite checks, not assumed existence of a colouring or repair.
No supply theorem, strict graph reduction or all-exterior repair is asserted.
Source attribution and decoding are inherited from TriangleStripAnchors.
-/

namespace FourColor.TriangleStripLists

open SimpleGraph ColoringListPropagation TriangleStripAnchors

def anchorAt : (s : Source) → Fin 2 → Fin (size s)
  | .d0092 => (![0,2] : Fin 2 → Fin 7)
  | .d0063 => (![1,3] : Fin 2 → Fin 7)
  | .d0099 => (![1,6] : Fin 2 → Fin 8)

theorem anchor_cover (s : Source) : ∀ v,
    structuralColour s v = anchorColour s ↔ ∃ i, anchorAt s i = v := by
  cases s <;> decide +kernel

variable {A : Type*} [DecidableEq A]

/-- The same two anchor values are retained by every constraint. -/
def pin (s : Source) (L : Fin (size s) → Finset A) (choice : Fin 2 → A)
    (v : Fin (size s)) : Finset A :=
  (L v).filter fun a => ∀ i, v = anchorAt s i → a = choice i

theorem pin_pinned (s : Source) (L : Fin (size s) → Finset A)
    (choice : Fin 2 → A) (v : Fin (size s))
    (hv : structuralColour s v = anchorColour s) :
    (pin s L choice v : Set A).Subsingleton := by
  obtain ⟨i,hi⟩ := (anchor_cover s v).mp hv
  intro a ha b hb
  exact ((Finset.mem_filter.mp ha).2 i hi.symm).trans
    ((Finset.mem_filter.mp hb).2 i hi.symm).symm

/-- Local support is a complete test once the shared anchor colours are
fixed. A single proof applies to arbitrary lists on all three actual cores. -/
theorem source_iff (s : Source) (L : Fin (size s) → Finset A)
    (choice : Fin 2 → A) (es : List (Fin (size s) × Fin (size s)))
    (edges : ∀ e ∈ es, (core s).Adj e.1 e.2)
    (supported : Supported (core s) (run (pin s L choice) es)) :
    (∃ C : (core s).Coloring A, (∀ v, C v ∈ L v) ∧
      ∀ i, C (anchorAt s i) = choice i) ↔
      ∀ v, (run (pin s L choice) es v).Nonempty := by
  have exactness := extension_iff_nonempty (core s) (pin s L choice)
    {v | structuralColour s v = anchorColour s} (source_forest s)
    (pin_pinned s L choice) es edges supported
  rw [← exactness]
  constructor
  · rintro ⟨C,fit,fixed⟩
    refine ⟨C,fun v => Finset.mem_filter.mpr ⟨fit v,?_⟩⟩
    intro i hi
    simpa only [hi] using fixed i
  · rintro ⟨C,fit⟩
    exact ⟨C,fun v => (Finset.mem_filter.mp (fit v)).1,
      fun i => (Finset.mem_filter.mp (fit (anchorAt s i))).2 i rfl⟩

/-- All directed core edges, in a fixed finite order. -/
def sweep (s : Source) : List (Fin (size s) × Fin (size s)) :=
  ((List.finRange (size s)).product (List.finRange (size s))).filter
    fun e => (core s).Adj e.1 e.2

theorem sweep_edges (s : Source) : ∀ e ∈ sweep s, (core s).Adj e.1 e.2 := by
  intro e he
  exact of_decide_eq_true (List.mem_filter.mp he).2

/-- The number of sweeps is an input; support is checked afterwards. -/
def sweeps (s : Source) (n : ℕ) := (List.replicate n (sweep s)).flatten

theorem sweeps_edges (s : Source) (n : ℕ) :
    ∀ e ∈ sweeps s n, (core s).Adj e.1 e.2 := by
  intro e he
  obtain ⟨xs,hxs,he⟩ := List.mem_flatten.mp he
  have same : xs = sweep s := (List.mem_replicate.mp hxs).2
  exact sweep_edges s e (same ▸ he)

/-- A finite guard containing only list propagation, edge support and
nonemptiness. It enumerates no complete interior colourings. -/
def Guard (s : Source) (L : Fin (size s) → Finset A)
    (choice : Fin 2 → A) (n : ℕ) : Prop :=
  Supported (core s) (run (pin s L choice) (sweeps s n)) ∧
    ∀ v, (run (pin s L choice) (sweeps s n) v).Nonempty

instance (s : Source) (L : Fin (size s) → Finset A)
    (choice : Fin 2 → A) (n : ℕ) : Decidable (Guard s L choice n) := by
  unfold Guard Supported
  infer_instance

theorem guard_colouring (s : Source) (L : Fin (size s) → Finset A)
    (choice : Fin 2 → A) (n : ℕ) (guard : Guard s L choice n) :
    ∃ C : (core s).Coloring A, (∀ v, C v ∈ L v) ∧
      ∀ i, C (anchorAt s i) = choice i :=
  (source_iff s L choice (sweeps s n) (sweeps_edges s n) guard.1).mpr guard.2

/-- The permitted colours retain every actual exterior neighbour. -/
noncomputable def exteriorLists {V : Type*} {G : SimpleGraph V} [Fintype A]
    (s : Source) (S : Set V) (read : G.induce S ≃g core s)
    (E : (G.induce Sᶜ).Coloring A) (v : Fin (size s)) : Finset A := by
  classical
  exact Finset.univ.filter fun a => ∀ y : ↥(Sᶜ), G.Adj (read.symm v) y → a ≠ E y

/-- Reconstruct a full colouring, preserving the entire exterior and the
joint anchor assignment. No full colouring is assumed as an input. -/
theorem occurrence_extension {V : Type*} {G : SimpleGraph V} [Fintype A]
    (s : Source) (S : Set V) (read : G.induce S ≃g core s)
    (E : (G.induce Sᶜ).Coloring A) (choice : Fin 2 → A) (n : ℕ)
    (guard : Guard s (exteriorLists s S read E) choice n) :
    ∃ C : G.Coloring A, C.restrictInduce Sᶜ = E ∧
      ∀ i, C (read.symm (anchorAt s i)) = choice i := by
  classical
  obtain ⟨C,fit,fixed⟩ := guard_colouring s _ choice n guard
  let h : (G.induce S).Coloring A := .mk (fun x => C (read x)) (by
    intro x y hxy
    exact C.valid (read.map_rel_iff.mpr hxy))
  have compatible : KempeGuardedLift.Fits S E h := by
    intro x y hxy
    have hh := (Finset.mem_filter.mp (fit (read x))).2 y
    exact hh (by simpa using hxy)
  refine ⟨KempeGuardedLift.glue S E h compatible,
    KempeGuardedLift.glue_restrict S E h compatible, fun i => ?_⟩
  rw [KempeGuardedLift.glue_hidden]
  change C (read (read.symm (anchorAt s i))) = choice i
  simpa using fixed i

end FourColor.TriangleStripLists
