import MettapediaFourColor.RuleTraversalData

/-!
# An exact rooted matcher for the pinned discharging rules

The checked construction traces produce a single candidate reading from
an actual oriented edge. Checking its degrees, edges and cyclic steps is
sound and complete for `NearLinearCharge.Applies`. No injectivity is assumed:
all shared ambient vertex identities are retained by the candidate.
-/

namespace FourColor.RuleMatcher

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge RuleTraversal

variable {V : Type*} {G : SimpleGraph V} (rotation : Data G)

def candidate (r : Fin 84) (d : G.Dart) (v : Vertex r) : V :=
  (execute rotation d (RuleTraversalData.trace r v)).fst

variable [G.LocallyFinite]

/-- The candidate is forced by the rooted occurrence. This is a uniqueness
statement for actual vertex readings, allowing non-injective readings. -/
theorem candidate_eq {r : Fin 84} (d : G.Dart) (x : Occurrence rotation r)
    (hs : x.vertex (sender r) = d.fst) (ht : x.vertex (receiver r) = d.snd) :
    candidate rotation r d = x.vertex := by
  funext v
  have hr : imageDart x (RuleTraversalData.root r) (endpoint_edge r) = d := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext hs ht
  obtain ⟨hend, he⟩ := trace_transport x (RuleTraversalData.root r) (endpoint_edge r)
    (RuleTraversalData.trace r v) (RuleTraversalData.valid r v).1
  rw [hr] at he
  have hf := congrArg (fun d : G.Dart => d.fst) he
  change candidate rotation r d v = x.vertex (lastState _ _).1 at hf
  simpa only [(RuleTraversalData.valid r v).2] using hf

theorem rooted_unique {r : Fin 84} (d : G.Dart) (x y : Occurrence rotation r)
    (xs : x.vertex (sender r) = d.fst) (xt : x.vertex (receiver r) = d.snd)
    (ys : y.vertex (sender r) = d.fst) (yt : y.vertex (receiver r) = d.snd) :
    x.vertex = y.vertex :=
  (candidate_eq rotation d x xs xt).symm.trans (candidate_eq rotation d y ys yt)

variable [DecidableEq V] [DecidableRel G.Adj]

def goodTurn (a b c : V) : Bool :=
  if hab : G.Adj a b then
    if hac : G.Adj a c then
      decide (rotation.vertexRotation ⟨(a, b), hab⟩ = (⟨(a, c), hac⟩ : G.Dart))
    else false
  else false

omit [G.LocallyFinite] in
theorem goodTurn_of {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (h : rotation.vertexRotation ⟨(a, b), hab⟩ = (⟨(a, c), hac⟩ : G.Dart)) :
    goodTurn rotation a b c = true := by
  simp [goodTurn, hab, hac, h]

omit [G.LocallyFinite] in
theorem goodTurn_sound {a b c : V} (h : goodTurn rotation a b c = true) :
    ∃ (hab : G.Adj a b) (hac : G.Adj a c),
      rotation.vertexRotation ⟨(a, b), hab⟩ = (⟨(a, c), hac⟩ : G.Dart) := by
  unfold goodTurn at h
  split_ifs at h with hab hac
  · exact ⟨hab, hac, of_decide_eq_true h⟩

def Fits (r : Fin 84) (f : Vertex r → V) : Prop :=
  (∀ i j, (graph r).Adj i j → G.Adj (f i) (f j)) ∧
  (∀ i, lower r i ≤ G.degree (f i) ∧ (upper r i = 0 ∨ G.degree (f i) ≤ upper r i)) ∧
  (∀ i j k, (graph r).Adj i j → (graph r).Adj i k → Turn r i j k →
    goodTurn rotation (f i) (f j) (f k) = true)

instance (r : Fin 84) (f : Vertex r → V) : Decidable (Fits rotation r f) := by
  unfold Fits
  infer_instance

def occurrenceOfFits {r : Fin 84} (f : Vertex r → V) (h : Fits rotation r f) :
    Occurrence rotation r where
  vertex := f
  edge := h.1
  degree := h.2.1
  turn := by
    intro i j k hij hik ht
    obtain ⟨_, _, he⟩ := goodTurn_sound rotation (h.2.2 i j k hij hik ht)
    exact he

theorem fits_of_occurrence {r : Fin 84} (x : Occurrence rotation r) :
    Fits rotation r x.vertex := by
  refine ⟨x.edge, x.degree, ?_⟩
  intro i j k hij hik ht
  exact goodTurn_of rotation (x.edge i j hij) (x.edge i k hik) (x.turn i j k hij hik ht)

/-- Check the one candidate, with no search over vertex assignments. -/
def check (r : Fin 84) (d : G.Dart) : Bool :=
  let f := candidate rotation r d
  decide (f (sender r) = d.fst ∧ f (receiver r) = d.snd ∧ Fits rotation r f)

theorem check_iff {r : Fin 84} (d : G.Dart) :
    check rotation r d = true ↔ Applies rotation r d.fst d.snd := by
  unfold check
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hs, ht, hf⟩
    exact ⟨occurrenceOfFits rotation _ hf, hs, ht⟩
  · rintro ⟨x, hs, ht⟩
    rw [candidate_eq rotation d x hs ht]
    exact ⟨hs, ht, fits_of_occurrence rotation x⟩

open scoped BigOperators

/-- Executable oriented-edge charge, using only the exact rooted matcher. -/
def sentAt (d : G.Dart) : ℤ :=
  ∑ r : Fin 84, if check rotation r d then (amount r : ℤ) else 0

/-- The executable computation agrees with the actual existential semantics. -/
theorem sentAt_eq (d : G.Dart) : sentAt rotation d = sent rotation d.fst d.snd := by
  classical
  apply Finset.sum_congr rfl
  intro r _
  simp only [check_iff]

/-- Extend the oriented-edge computation by zero on nonedges. -/
def sentBetween (u v : V) : ℤ :=
  if h : G.Adj u v then sentAt rotation ⟨(u, v), h⟩ else 0

theorem sentBetween_eq (u v : V) : sentBetween rotation u v = sent rotation u v := by
  unfold sentBetween
  split_ifs with h
  · exact sentAt_eq rotation _
  · exact (sent_eq_zero_of_not_adj rotation h).symm

variable [Fintype V]

/-- Final charge computed from the certified rooted matcher. -/
def chargeAt (v : V) : ℤ :=
  10 * (6 - (G.degree v : ℤ)) +
    ∑ u : V, (sentBetween rotation u v - sentBetween rotation v u)

theorem chargeAt_eq (v : V) : chargeAt rotation v = finalCharge rotation v := by
  simp only [chargeAt, finalCharge, sentBetween_eq, net]

/-- The computed flatness test supplies the exact joint boundary obligation. -/
theorem checked_pair_budget {u v : V} (hne : u ≠ v)
    (hu : G.degree u = 8) (hv : G.degree v = 8)
    (hzu : chargeAt rotation u = 0) (hzv : chargeAt rotation v = 0) :
    pairBoundary rotation u v = 40 := by
  rw [chargeAt_eq] at hzu hzv
  exact flat_eight_pair_budget rotation hne hu hv hzu hzv

end FourColor.RuleMatcher
