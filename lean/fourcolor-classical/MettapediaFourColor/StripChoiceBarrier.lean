import MettapediaFourColor.StripPuncturedExtension
import MettapediaFourColor.KempeRetainedMatching

/-!
# A choice-preserving rule can stall in the matching game

One source boundary admits seven different positions for a single omitted
vertex, but no complete colouring. For each colour query there is a
noncrossing matching whose answers either lose some of these choices or
return to the same boundary up to a palette permutation. Consequently an
arbitrary-length policy which never decreases the number of available hole
positions cannot finish against these matching responses.

This is an obstruction in the abstract matching game. The three responses
are not asserted to arise together from one actual exterior graph.
-/

namespace FourColor.StripChoiceBarrier

open Color StripResponseSummary StripPartialColouring StripSourceExtension
open KempeMatchingChromogram KempeIntervalRepair

def Possible (b : Boundary) (h : Fin 8) : Prop :=
  ∃ a c, StripPuncturedExtension.r5 {h} b a c

instance (b h) : Decidable (Possible b h) := by unfold Possible; infer_instance

def available (b : Boundary) : Finset (Fin 8) :=
  Finset.univ.filter (Possible b)

def score (b : Boundary) : ℕ := (available b).card

theorem possible_iff (b : Boundary) (h : Fin 8) :
    Possible b h ↔ ∃ f, ValidExcept b {h} f :=
  StripPuncturedExtension.terminal_iff {h} b

/-- Available positions count genuine induced-source colourings with every
ordered boundary colour fixed. -/
theorem actual_iff (b : Boundary) (hb : ProperBoundary b) (h : Fin 8) :
    (∃ k : (TriangleStripAnchors.input0099.graph.induce {v | Live {h} v}).Coloring Color,
      ∀ i, k ⟨port i,live_port {h} i⟩ = b i) ↔ Possible b h := by
  rw [possible_iff]
  constructor
  · rintro ⟨k,hk⟩
    exact validExcept_of_source b {h} k hk
  · rintro ⟨f,hf⟩
    exact ⟨.mk (fun v => completeColour b f v.val)
      (fun {u v} e => partial_valid b {h} f hb hf u.val v.val u.property v.property e),
      fun i => colour_port b f i⟩

theorem partial_map (g : EdgePerm) {b : Boundary} {h : Finset (Fin 8)}
    {f : Fin 8 → Color} (hf : ValidExcept b h f) :
    ValidExcept (fun i => g (b i)) h (fun i => g (f i)) := by
  exact ⟨fun v hv i hi eq => hf.1 v hv i hi (g.apply_injective eq),
    fun e he hu hv eq => hf.2 e he hu hv (g.apply_injective eq)⟩

theorem possible_map (g : EdgePerm) (b : Boundary) (h : Fin 8) :
    Possible (fun i => g (b i)) h ↔ Possible b h := by
  rw [possible_iff, possible_iff]
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨fun i => g⁻¹ (f i), by simpa using partial_map g⁻¹ hf⟩
  · rintro ⟨f,hf⟩
    exact ⟨_, partial_map g hf⟩

theorem score_map (g : EdgePerm) (b : Boundary) :
    score (fun i => g (b i)) = score b := by
  have eq : available (fun i => g (b i)) = available b := by
    ext h
    simp only [available, Finset.mem_filter, Finset.mem_univ, true_and, possible_map]
  exact congrArg Finset.card eq

def word : Fin 11 → Color := ![c1,c1,c2,c1,c2,c3,c2,c1,c2,c2,c1]
def base : Boundary := StripSymbolicRepair.readBoundary (List.ofFn word)

theorem base_profile : ProperBoundary base ∧
    (∀ h, Possible base h ↔ h ≠ 2) ∧ score base = 7 ∧
      ¬ ∃ a c, StripResponseSummary.r5 base a c := by decide +kernel

theorem base_nonextension : ¬ ∃ f, ValidCore base f := by
  intro h
  exact base_profile.2.2.2 ((StripResponseSummary.terminal_iff base).mpr h)

def palette : Fin 3 → EdgePerm := ![.e123,.e213,.e321]
def colour (s : Fin 3) (i : Fin 11) : Color := palette s (word i)
def arity (s : Fin 3) : ℕ := if s = 2 then 5 else 3
def roots : Fin 3 → List (Fin 11) := ![[2,5,6],[0,3,7],[0,2,4,6,9]]
def root (s : Fin 3) (j : ℕ) : Fin 11 := (roots s)[j]?.getD 0
def mate : Fin 3 → Fin 11 → Fin 11 :=
  ![![0,1,4,3,2,9,8,7,6,5,10],
    ![1,0,2,5,4,3,6,10,8,9,7],
    ![1,0,3,2,8,5,7,6,4,10,9]]

theorem matchings_valid : ∀ s,
    Function.Involutive (mate s) ∧ Noncrossing (mate s) ∧
    (∀ i, colour s i ≠ 0) ∧ (∀ i, mate s i = i ↔ colour s i = c1) := by
  unfold Function.Involutive
  decide +kernel

/-- The roots list every active pair exactly once. -/
theorem roots_cover : ∀ s,
    (roots s).length = arity s ∧ arity s ≤ 5 ∧
    (∀ i, colour s i ≠ c1 → ∃ j : Fin (arity s),
      i = root s j.val ∨ i = mate s (root s j.val)) ∧
    (∀ j k : Fin (arity s), root s j.val = root s k.val ∨
      root s j.val = mate s (root s k.val) → j = k) := by decide +kernel

/-- All subsets, including the empty and full subsets, are available. -/
def batch (s : Fin 3) (mask : Fin 32) : Fin 11 → Color :=
  (List.range (arity s)).foldl (fun c j =>
    if mask.val.testBit j then switch c (root s j) (mate s (root s j)) else c) (colour s)

def answer (s : Fin 3) (mask : Fin 32) : List Color :=
  (List.ofFn (batch s mask)).map (palette s)

def boundary (s : Fin 3) (mask : Fin 32) : Boundary :=
  StripSymbolicRepair.readBoundary (answer s mask)

/-- Every batch preserves its selected original chromogram. -/
theorem batches_match : ∀ s mask,
    matchg [] (List.ofFn (colour s)) (gram (mate s) (colour s)) ∧
    matchg [] (List.ofFn (batch s mask)) (gram (mate s) (colour s)) ∧
    trace (List.ofFn (boundary s mask)) = answer s mask ∧
    ProperBoundary (boundary s mask) := by decide +kernel

def Orbit (b : Boundary) : Prop := ∃ g : EdgePerm, b = fun i => g (base i)

instance (b) : Decidable (Orbit b) := by unfold Orbit; infer_instance

/-- The small obstruction: preserving seven choices can only return to the
same normalized boundary. All other batch answers lose at least one choice. -/
theorem answer_barrier : ∀ s mask,
    Orbit (boundary s mask) ∨ score (boundary s mask) < 7 := by decide +kernel

theorem orbit_score {b : Boundary} (hb : Orbit b) : score b = 7 := by
  obtain ⟨g,rfl⟩ := hb
  rw [score_map]
  exact base_profile.2.2.1

theorem orbit_nonextension {b : Boundary} (hb : Orbit b) : ¬ ∃ f, ValidCore b f := by
  obtain ⟨g,rfl⟩ := hb
  rintro ⟨f,hf⟩
  apply base_nonextension
  refine ⟨fun i => g⁻¹ (f i), ?_, ?_⟩
  · intro v i hi he
    apply hf.1 v i hi
    have h := congrArg g he
    simpa using h
  · intro e he eq
    exact hf.2 e he (g⁻¹.apply_injective eq)

/-- Adversary responses on the invariant orbit. The query may choose any
of the three colour partitions and any subset of the returned matching. -/
def Step (b c : Boundary) : Prop := ∃ g : EdgePerm,
  b = (fun i => g (base i)) ∧ ∃ s mask, c = fun i => g (boundary s mask i)

def PreservesChoices (b c : Boundary) : Prop := Step b c ∧ score b ≤ score c

theorem step_stays {b c : Boundary} (h : PreservesChoices b c) : Orbit c := by
  obtain ⟨⟨g,rfl,s,mask,rfl⟩,hn⟩ := h
  rw [score_map, score_map, base_profile.2.2.1] at hn
  rcases answer_barrier s mask with ⟨k,hk⟩ | small
  · refine ⟨g*k, ?_⟩
    simp only [hk, EdgePerm.mul_apply]
  · omega

/-- No length bound is imposed on the choice-preserving history. -/
theorem history_stays {b : Boundary}
    (h : Relation.ReflTransGen PreservesChoices base b) : Orbit b := by
  induction h with
  | refl => exact ⟨1, by simp⟩
  | tail _ step _ => exact step_stays step

theorem history_nonextension {b : Boundary}
    (h : Relation.ReflTransGen PreservesChoices base b) : ¬ ∃ f, ValidCore b f :=
  orbit_nonextension (history_stays h)

theorem history_no_source_trace {b : Boundary}
    (h : Relation.ReflTransGen PreservesChoices base b) :
    ¬ KempeBoundarySplit.GraphTrace TriangleStripAnchors.input0099.graph
      TriangleStripAnchors.input0099.boundary (trace (List.ofFn b)) :=
  no_trace b (fun ht => history_nonextension h ((StripResponseSummary.terminal_iff b).mp ht))

end FourColor.StripChoiceBarrier
