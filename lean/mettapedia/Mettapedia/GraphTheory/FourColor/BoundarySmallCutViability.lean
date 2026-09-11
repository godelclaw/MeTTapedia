import Mettapedia.GraphTheory.FourColor.BoundarySmallCutExecutable

/-!
# The small-cut profile detects irreversible loss of connectivity

Zero-cut records recover the exact connectivity relation on ports.
A realized nonempty zero-cut record with every port unselected detects
a component invisible at the boundary. Such a component prevents any
connected extension by a nonempty exterior. A closed finished object
is deliberately not rejected by this theorem.

If this obstruction is absent, every component meets a port, so the
number of components is bounded by the interface size. These facts
justify the physical evaluator's visible-component and viability tests;
no connected-prefix or planar-piece hypothesis is supplied.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundarySmallCutViability

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24BoundaryEssentialGluing.Multigraph
open BoundarySmallCutProfile BoundaryConnectivity SmallCutConnectedBridgeless

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E P : Type*} (G : Multigraph V E) (ports : P → V)

def componentBit (v : V) : V → Bool := fun w => decide (G.Reach v w)

theorem componentBit_edges (v : V) (e : E) :
    componentBit G v (G.fst e) = componentBit G v (G.snd e) := by
  have he : G.Reach v (G.fst e) ↔ G.Reach v (G.snd e) :=
    ⟨fun p => p.tail ⟨e, not_false, .inl ⟨rfl, rfl⟩⟩,
      fun p => p.tail ⟨e, not_false, .inr ⟨rfl, rfl⟩⟩⟩
  simp only [componentBit, propext he]

variable [Fintype E]

theorem cutSize_zero_iff (s : V → Bool) :
    cutSize G s = 0 ↔ ∀ e, s (G.fst e) = s (G.snd e) := by
  simp [cutSize, Finset.sum_eq_zero_iff]

theorem state_cost_zero (s : V → Bool) :
    (state G ports s).cost.val = 0 ↔ cutSize G s = 0 := by
  change min 2 (cutSize G s) = 0 ↔ cutSize G s = 0
  omega

theorem reach_iff_zero_cuts (u v : V) :
    G.Reach u v ↔ ∀ s : V → Bool, cutSize G s = 0 → s u = s v := by
  constructor
  · intro h s hs
    exact constant_on_path G s (fun _ => False)
      (fun e _ => (cutSize_zero_iff G s).mp hs e) h
  · intro h
    have hz := cutSize_zero G (componentBit G u) (componentBit_edges G u)
    have hh := h (componentBit G u) hz
    have hu : componentBit G u u = true := by
      simp only [componentBit, decide_eq_true_eq]
      exact .refl
    rw [hu] at hh
    exact of_decide_eq_true hh.symm

/-- Read the port component relation solely from zero-cut records. -/
def SameComponent (S : Set (State P)) (p q : P) : Prop :=
  ∀ a ∈ S, a.cost.val = 0 → a.boundary p = a.boundary q

theorem sameComponent_profile (p q : P) :
    SameComponent (profile G ports) p q ↔ G.Reach (ports p) (ports q) := by
  rw [reach_iff_zero_cuts]
  constructor
  · intro h s hs
    exact h (state G ports s) ⟨s, rfl⟩ ((state_cost_zero G ports s).mpr hs)
  · rintro h a ⟨s, rfl⟩ hs
    exact h s ((state_cost_zero G ports s).mp hs)

def HasHidden (S : Set (State P)) : Prop :=
  ∃ a ∈ S, a.selected = true ∧ a.cost.val = 0 ∧ ∀ p, a.boundary p = false

/-- Exact obstruction, including an empty boundary and isolated vertices. -/
theorem hidden_iff_not_visible : HasHidden (profile G ports) ↔ ¬ PortVisible G ports := by
  constructor
  · rintro ⟨a, ⟨s, rfl⟩, hs, hc, hp⟩ hv
    obtain ⟨v, hsv⟩ : ∃ v, s v = true := of_decide_eq_true hs
    obtain ⟨p, hpath⟩ := hv v
    have hh := (reach_iff_zero_cuts G v (ports p)).mp hpath s
      ((state_cost_zero G ports s).mp hc)
    have hsp : s (ports p) = false := hp p
    simp only [hsv, hsp, Bool.true_eq_false] at hh
  · intro hv
    obtain ⟨v, hv⟩ : ∃ v, ∀ p, ¬ G.Reach v (ports p) := by
      simpa only [PortVisible, not_forall, not_exists] using hv
    refine ⟨state G ports (componentBit G v), ⟨_, rfl⟩, ?_, ?_, ?_⟩
    · change decide (∃ w, componentBit G v w = true) = true
      apply decide_eq_true
      refine ⟨v, ?_⟩
      simp only [componentBit, decide_eq_true_eq]
      exact .refl
    · exact (state_cost_zero G ports _).mpr
        (cutSize_zero G _ (componentBit_edges G v))
    · intro p
      change decide (G.Reach v (ports p)) = false
      exact decide_eq_false (hv p)

variable {W F : Type*} (K : Multigraph W F) (otherPorts : P → W)

/-- A hidden component cannot attach to anything in a later nonempty
exterior: all possible seams meet its complement. -/
theorem hidden_no_connected_glue [Nonempty W] (h : HasHidden (profile G ports)) :
    ¬ (glue G K ports otherPorts).Connected := by
  rintro hc
  obtain ⟨a, ⟨s, rfl⟩, hs, hz, hp⟩ := h
  obtain ⟨v, hv⟩ : ∃ v, s v = true := of_decide_eq_true hs
  let t : V ⊕ W → Bool := Sum.elim s (fun _ => false)
  have hedge (e : E ⊕ F ⊕ P) :
      t ((glue G K ports otherPorts).fst e) = t ((glue G K ports otherPorts).snd e) := by
    rcases e with e | e | p
    · exact (cutSize_zero_iff G s).mp ((state_cost_zero G ports s).mp hz) e
    · rfl
    · exact hp p
  have hh := constant_on_path (glue G K ports otherPorts) t (fun _ => False)
    (fun e _ => hedge e) (hc (.inl v) (.inr (Classical.choice ‹Nonempty W›)))
  change s v = false at hh
  simp only [hv, Bool.true_eq_false] at hh

theorem visible_of_connected_glue [Nonempty W]
    (h : (glue G K ports otherPorts).Connected) : PortVisible G ports := by
  by_contra hv
  exact hidden_no_connected_glue G ports K otherPorts
    ((hidden_iff_not_visible G ports).mpr hv) h

omit [Fintype E] in
def componentSetoid : Setoid V :=
  ⟨G.Reach, ⟨fun _ => .refl, fun h => reach_symm h, fun h h' => h.trans h'⟩⟩

/-- In a prefix that can still acquire a connected nonempty exterior,
there cannot be more components than exposed ports. -/
theorem card_components_le [Fintype V] [Fintype P]
    (h : ¬ HasHidden (profile G ports)) :
    Nat.card (Quotient (componentSetoid G)) ≤ Fintype.card P := by
  letI : Fintype (Quotient (componentSetoid G)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hv : PortVisible G ports := not_not.mp ((not_congr (hidden_iff_not_visible G ports)).mp h)
  apply Fintype.card_le_of_surjective (fun p => Quotient.mk (componentSetoid G) (ports p))
  intro q
  obtain ⟨v, rfl⟩ := Quotient.exists_rep q
  obtain ⟨p, hp⟩ := hv v
  exact ⟨p, Quotient.sound (reach_symm hp)⟩

/-- Equality of all zero-cut observations is an equivalence even for a
formal profile. For a physical profile it is precisely port reachability. -/
def portSetoid (S : Set (State P)) : Setoid P where
  r := SameComponent S
  iseqv := ⟨fun _ _ _ _ => rfl,
    fun h a ha hz => (h a ha hz).symm,
    fun h h' a ha hz => (h a ha hz).trans (h' a ha hz)⟩

/-- For a viable piece the finite port quotient is the whole component
quotient, not an approximation that loses hidden components. -/
def componentEquiv (h : ¬ HasHidden (profile G ports)) :
    Quotient (portSetoid (profile G ports)) ≃ Quotient (componentSetoid G) := by
  let f : Quotient (portSetoid (profile G ports)) → Quotient (componentSetoid G) :=
    Quotient.map ports (fun p q h => (sameComponent_profile G ports p q).mp h)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b he
    obtain ⟨p, rfl⟩ := Quotient.exists_rep a
    obtain ⟨q, rfl⟩ := Quotient.exists_rep b
    apply Quotient.sound
    apply (sameComponent_profile G ports p q).mpr
    exact Quotient.exact (s := componentSetoid G) he
  · have hv : PortVisible G ports :=
      not_not.mp ((not_congr (hidden_iff_not_visible G ports)).mp h)
    intro q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨p, hp⟩ := hv v
    exact ⟨Quotient.mk (portSetoid (profile G ports)) p, Quotient.sound (reach_symm hp)⟩

theorem card_components_eq_profile (h : ¬ HasHidden (profile G ports)) :
    Nat.card (Quotient (componentSetoid G)) =
      Nat.card (Quotient (portSetoid (profile G ports))) :=
  Nat.card_congr (componentEquiv G ports h).symm

end

open BoundarySmallCutExecutable

variable {P : Type*} [Fintype P]

/-- This rejects continuation by additional vertices, not final acceptance. -/
def rejectsExtension (a : Finset (State P)) : Bool :=
  decide ((a.filter fun q =>
    q.selected = true ∧ q.cost.val = 0 ∧ ∀ p, q.boundary p = false).Nonempty)

def sameComponent (a : Finset (State P)) (p q : P) : Bool :=
  decide ((a.filter fun s => s.cost.val = 0 ∧ s.boundary p ≠ s.boundary q).card = 0)

theorem rejectsExtension_iff (a : Finset (State P)) :
    rejectsExtension a = true ↔ HasHidden (a : Set (State P)) := by
  simp [rejectsExtension, HasHidden, Finset.filter_nonempty_iff]

theorem sameComponent_iff (a : Finset (State P)) (p q : P) :
    sameComponent a p q = true ↔ SameComponent (a : Set (State P)) p q := by
  simp [sameComponent, SameComponent, Finset.filter_eq_empty_iff]

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem rejectsExtension_extract (G : Multigraph V E) (ports : P → V) :
    rejectsExtension (extract G ports) = true ↔ ¬ PortVisible G ports := by
  rw [rejectsExtension_iff, extract_correct, hidden_iff_not_visible]

theorem sameComponent_extract (G : Multigraph V E) (ports : P → V) (p q : P) :
    sameComponent (extract G ports) p q = true ↔ G.Reach (ports p) (ports q) := by
  rw [sameComponent_iff, extract_correct, sameComponent_profile]

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open SerialTangleSmallCutTransfer

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq E]

theorem rejectsExtension_extractTangle (T : TwoSidedOpenTangleData V E L R) :
    rejectsExtension (extractTangle T) = true ↔
      ¬ PortVisible (sideMultigraph (asOpen T)) (asOpen T).boundaryVert := by
  rw [rejectsExtension_iff, extractTangle_correct, hidden_iff_not_visible]

theorem sameComponent_extractTangle (T : TwoSidedOpenTangleData V E L R) (p q : L ⊕ R) :
    sameComponent (extractTangle T) p q = true ↔
      (sideMultigraph (asOpen T)).Reach ((asOpen T).boundaryVert p) ((asOpen T).boundaryVert q) := by
  rw [sameComponent_iff, extractTangle_correct, sameComponent_profile]

end Mettapedia.GraphTheory.FourColor.BoundarySmallCutViability
