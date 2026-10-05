import MettapediaFourColor.StripSourceExtension

/-!
# A hidden boundary update can free a previously forced cap choice

A four-neighbour fan with colours `(p,q,p,r)` forces the fourth colour.
Changing the second neighbour from `q` to `r` frees `q` as a second choice.
In the decoded D0099 source, this exchange permits full reconstruction
although the selected two-cap prefix still has the same diamond boundary
and does not extend. Thus full-source repair cannot in general be inferred
by freezing the previously chosen cap witnesses.

The exterior update below is certified against one abstract noncrossing
matching. Realization by a particular exterior graph is not asserted.
D0099 provenance is inherited from `TriangleStripAnchors`.
-/

namespace FourColor.CapRechoice

open Color TriangleStripAnchors StripResponseSummary

set_option maxRecDepth 4096

/-- The four palette values are distinct. -/
def Palette (p q r s : Color) : Prop :=
  p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s

instance (p q r s : Color) : Decidable (Palette p q r s) := by
  unfold Palette
  infer_instance

/-- A repeated end colour leaves one forced fan colour. -/
theorem forced_choice : ∀ p q r s x : Color, Palette p q r s →
    (x ≠ p ∧ x ≠ q ∧ x ≠ p ∧ x ≠ r ↔ x = s) := by decide +kernel

/-- After identifying the two neighbour colours, both missing colours work. -/
theorem freed_choices : ∀ p q r s x : Color, Palette p q r s →
    (x ≠ p ∧ x ≠ r ∧ x ≠ p ∧ x ≠ r ↔ x = q ∨ x = s) := by decide +kernel

def initial : Fin 19 → Color :=
  ![c0,c1,c0,c1,c0,c1,c0,c1,c3,c0,c2,c2,c0,c0,c3,c0,c2,c0,c3]

/-- Only original boundary vertex 5 changes; the four cap vertices are fixed. -/
def selected (changed : Bool) (v : Fin 19) : Color :=
  if changed && decide (v = 5) then c2 else initial v

def outer (changed : Bool) : Boundary := fun i => selected changed (port i)

def retained (v : Fin 19) : Prop := v ≠ 12 ∧ v ≠ 13 ∧ v ≠ 15 ∧ v ≠ 17

instance (v : Fin 19) : Decidable (retained v) := by
  unfold retained
  infer_instance

def diamondBoundary : List (Fin 19) := [18,16,3,4,14,11,8,9,10]

theorem prefix_valid : ∀ s : Bool, ∀ u v : Fin 19,
    retained u → retained v → input0099.graph.Adj u v → selected s u ≠ selected s v :=
  by decide +kernel

/-- These are actual colourings of the same retained source graph. -/
def prefixColouring (s : Bool) : (input0099.graph.induce {v | retained v}).Coloring Color :=
  .mk (fun v => selected s v.val) (by
    intro u v h
    exact prefix_valid s _ _ u.property v.property h)

theorem same_visible_boundary :
    diamondBoundary.map (selected false) = diamondBoundary.map (selected true) :=
  by decide +kernel

theorem only_hidden_vertex : ∀ v : Fin 19, v ≠ 5 → selected false v = selected true v :=
  by decide +kernel

theorem cap_choice_changes :
    (∀ x : Color,
      (x ≠ outer false 4 ∧ x ≠ outer false 5 ∧ x ≠ outer false 6 ∧ x ≠ initial 11 ↔
        x = c3)) ∧
    (∀ x : Color,
      (x ≠ outer true 4 ∧ x ≠ outer true 5 ∧ x ≠ outer true 6 ∧ x ≠ initial 11 ↔
        x = c1 ∨ x = c3)) := by
  constructor
  · intro x; exact forced_choice c0 c1 c2 c3 x (by decide)
  · intro x; exact freed_choices c0 c1 c2 c3 x (by decide)

/-- The selected caps forbid all four colours at source vertex 13. -/
theorem no_fixed_prefix_extension (s : Bool) :
    ¬ ∃ k : input0099.graph.Coloring Color, ∀ v, retained v → k v = selected s v := by
  rintro ⟨k,h⟩
  have e3 := k.valid (show input0099.graph.Adj (13 : Fin 19) 3 by decide)
  have e4 := k.valid (show input0099.graph.Adj (13 : Fin 19) 4 by decide)
  have e14 := k.valid (show input0099.graph.Adj (13 : Fin 19) 14 by decide)
  have e16 := k.valid (show input0099.graph.Adj (13 : Fin 19) 16 by decide)
  rw [h 3 (by decide)] at e3
  rw [h 4 (by decide)] at e4
  rw [h 14 (by decide)] at e14
  rw [h 16 (by decide)] at e16
  cases s <;> cases hk : k 13 <;> simp_all [selected,initial]

private theorem fourth (x : Color) (h0 : x ≠ c0) (h1 : x ≠ c1) (h2 : x ≠ c2) : x = c3 :=
  (forced_choice c0 c1 c2 c3 x (by decide)).mp ⟨h0,h1,h0,h2⟩

/-- Before the hidden update the original boundary has no full extension,
even if all cap choices are allowed. -/
theorem no_initial_extension :
    ¬ ∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = outer false i := by
  rintro ⟨k,h⟩
  have e (u : Fin 19) (i : Fin 11) (adj : input0099.graph.Adj u (port i)) :
      k u ≠ outer false i := by rw [← h i]; exact k.valid adj
  have k11 : k 11 = c2 := by
    have e6 := e 11 6 (by decide)
    have e7 := e 11 7 (by decide)
    have e8 := e 11 8 (by decide)
    cases hk : k 11 <;> simp_all [outer,selected,initial,port]
  have k14 : k 14 = c3 := by
    apply fourth
    · exact e 14 4 (by decide)
    · exact e 14 5 (by decide)
    · have adj := k.valid (show input0099.graph.Adj (14 : Fin 19) 11 by decide)
      simpa only [k11] using adj
  have k18 : k 18 = c3 := fourth _ (e 18 0 (by decide))
    (e 18 1 (by decide)) (e 18 10 (by decide))
  have k16 : k 16 = c2 := by
    have e1 := e 16 1 (by decide)
    have e2 := e 16 2 (by decide)
    have e18 := k.valid (show input0099.graph.Adj (16 : Fin 19) 18 by decide)
    rw [k18] at e18
    cases hk : k 16 <;> simp_all [outer,selected,initial,port]
  have e3 := e 13 3 (by decide)
  have e4 := e 13 4 (by decide)
  have e14 := k.valid (show input0099.graph.Adj (13 : Fin 19) 14 by decide)
  have e16 := k.valid (show input0099.graph.Adj (13 : Fin 19) 16 by decide)
  rw [k14] at e14
  rw [k16] at e16
  cases hk : k 13 <;> simp_all [outer,selected,initial,port]

def repairedCore : Fin 8 → Color := ![c2,c0,c3,c1,c2,c2,c1,c3]

/-- Full source reconstruction uses the newly available colour at vertex 14. -/
def repaired : input0099.graph.Coloring Color :=
  StripSourceExtension.colouring (outer true) repairedCore (by decide +kernel)
    (by unfold ValidCore; decide +kernel)

theorem repaired_outer : ∀ i, repaired (port i) = outer true i :=
  StripSourceExtension.colour_port _ _

theorem repaired_rechooses : repaired 14 = c1 ∧ selected true 14 = c3 := by decide +kernel

def mate : Fin 11 → Fin 11 := ![1,0,7,6,5,4,3,2,8,10,9]

def normalized (s : Bool) (i : Fin 11) : Color :=
  EdgePerm.e321 (outer s i + outer s ⟨(i.val + 1) % 11, Nat.mod_lt _ (by decide)⟩)

theorem matching_valid : Function.Involutive mate ∧
    KempeMatchingChromogram.Noncrossing mate ∧
    (∀ i, normalized false i ≠ 0) ∧
    (∀ i, mate i = i ↔ normalized false i = c1) := by
  unfold Function.Involutive
  decide +kernel

theorem trace_normalized : ∀ s : Bool,
    (trace (List.ofFn (outer s))).map EdgePerm.e321 = List.ofFn (normalized s) :=
  by decide +kernel

theorem normalized_update : normalized true =
    KempeIntervalRepair.switch (normalized false) 4 (mate 4) := by decide +kernel

/-- The update switches one chord of the same original exterior matching. -/
theorem same_matching_update :
    let gram := KempeMatchingChromogram.gram mate (normalized false)
    matchg [] ((trace (List.ofFn (outer false))).map EdgePerm.e321) gram ∧
    matchg [] ((trace (List.ofFn (outer true))).map EdgePerm.e321) gram := by
  dsimp only
  rw [trace_normalized,trace_normalized,normalized_update]
  exact ⟨(KempeMatchingChromogram.reconstruct mate _ matching_valid.1 matching_valid.2.1
    matching_valid.2.2.1 matching_valid.2.2.2).1,
    KempeIntervalRepair.switch_matches mate _ matching_valid.1 matching_valid.2.1
      matching_valid.2.2.1 matching_valid.2.2.2 4⟩

/-- Full extension is not determined by the visible selected diamond boundary. -/
theorem visible_boundary_insufficient :
    ¬ (∀ s t : Bool, diamondBoundary.map (selected s) = diamondBoundary.map (selected t) →
      ((∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = outer s i) ↔
       (∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = outer t i))) := by
  intro h
  exact no_initial_extension ((h false true same_visible_boundary).mpr ⟨repaired,repaired_outer⟩)

end FourColor.CapRechoice
