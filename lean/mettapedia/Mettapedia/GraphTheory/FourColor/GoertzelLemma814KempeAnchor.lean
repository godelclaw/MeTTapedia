import Mettapedia.GraphTheory.FourColor.GoertzelLemma814
import Mettapedia.GraphTheory.FourColor.KempeSwitch

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.14: Kempe-switch anchor

This module ties the finite `LColor` chain-move model used by the Goertzel
Lemma 8.14/8.18 certificates to the shared `Color`/`switch` Kempe API in
`ColorAlgebra`.
-/

namespace GoertzelLemma814KempeAnchor

open GoertzelLemma814

/-- Encode the three finite nonzero gadget colors into the shared `𝔽₂²` colors. -/
def encodeLColor : LColor → Color
  | LColor.r => red
  | LColor.b => blue
  | LColor.p => purple

@[simp] theorem encodeLColor_r : encodeLColor LColor.r = red := rfl
@[simp] theorem encodeLColor_b : encodeLColor LColor.b = blue := rfl
@[simp] theorem encodeLColor_p : encodeLColor LColor.p = purple := rfl

@[simp] theorem encodeLColor_ne_zero (x : LColor) : encodeLColor x ≠ 0 := by
  cases x <;> simp [encodeLColor]

theorem encodeLColor_injective : Function.Injective encodeLColor := by
  intro x y h
  cases x <;> cases y
  · rfl
  · exact (red_ne_blue h).elim
  · exact (red_ne_purple h).elim
  · exact (red_ne_blue h.symm).elim
  · rfl
  · exact (blue_ne_purple h).elim
  · exact (red_ne_purple h.symm).elim
  · exact (blue_ne_purple h.symm).elim
  · rfl

@[simp] theorem encodeLColor_eq_iff (x y : LColor) :
    encodeLColor x = encodeLColor y ↔ x = y := by
  exact encodeLColor_injective.eq_iff

/-- The finite color swap is exactly the shared `Color.swap` after encoding. -/
@[simp] theorem encodeLColor_swapColor (a c x : LColor) :
    encodeLColor (swapColor a c x) =
      Color.swap (encodeLColor a) (encodeLColor c) (encodeLColor x) := by
  cases a <;> cases c <;> cases x <;> rfl

/--
The encoded color of a chain edge, using the same canonical representative
edge convention as `chainSwitchedColor`.
-/
def encodedChainColor (orients : List TauOrient) (states : List TauState)
    (ge : ChainEdge) : Color :=
  encodeLColor (chainEdgeColor states (chainCanonicalEdge orients ge))

/-- The set of local chain edges selected by a component, modulo canonical representatives. -/
def chainComponentSwitchSet (orients : List TauOrient)
    (component : List ChainEdge) : Set ChainEdge :=
  {ge | component.contains (chainCanonicalEdge orients ge) = true}

/-- The shared Kempe switch corresponding to a finite Goertzel component switch. -/
noncomputable def encodedChainSwitch (orients : List TauOrient)
    (states : List TauState) (component : List ChainEdge) (a c : LColor) :
    ChainEdge → Color :=
  switch (encodeLColor a) (encodeLColor c)
    (chainComponentSwitchSet orients component)
    (encodedChainColor orients states)

/--
Pointwise anchor: the finite `chainSwitchedColor` operation used by a certificate
row is the shared Kempe `switch` on the encoded coloring.
-/
theorem encode_chainSwitchedColor_eq_encodedChainSwitch
    (orients : List TauOrient) (states : List TauState)
    (component : List ChainEdge) (a c : LColor) (ge : ChainEdge) :
    encodeLColor (chainSwitchedColor orients states component a c ge) =
      encodedChainSwitch orients states component a c ge := by
  unfold chainSwitchedColor encodedChainSwitch chainComponentSwitchSet encodedChainColor switch
  by_cases h : chainCanonicalEdge orients ge ∈ component
  · have hc : component.contains (chainCanonicalEdge orients ge) = true :=
      List.contains_iff_mem.mpr h
    simp [h]
  · have hc : component.contains (chainCanonicalEdge orients ge) = false :=
      bool_false_of_not_true fun hcontains => h (List.contains_iff_mem.mp hcontains)
    simp [h]

/-- The shared Kempe switch selected by a concrete `ChainMove`. -/
noncomputable def encodedChainMoveSwitch (orients : List TauOrient)
    (states : List TauState) (move : ChainMove) : ChainEdge → Color :=
  encodedChainSwitch orients states
    (chainComponent orients states move.a move.c move.seed) move.a move.c

/--
Specialized `ChainMove` form of the anchor, avoiding any certificate-table
reduction and referring only to the move's computed two-color component.
-/
theorem encode_chainMoveSwitchedColor_eq_encodedChainMoveSwitch
    (orients : List TauOrient) (states : List TauState)
    (move : ChainMove) (ge : ChainEdge) :
    encodeLColor
        (chainSwitchedColor orients states
          (chainComponent orients states move.a move.c move.seed)
          move.a move.c ge) =
      encodedChainMoveSwitch orients states move ge := by
  exact encode_chainSwitchedColor_eq_encodedChainSwitch
    orients states (chainComponent orients states move.a move.c move.seed)
    move.a move.c ge

/--
Any specified certificate move whose color pair and seed come from the real
enumeration is also a genuine `chainSingleKempeStep`.

The membership hypotheses are intentional: arbitrary `ChainMove` values can
name equal colors or non-representative seeds, while the certificate generators
are expected to supply listed two-color pairs and listed chain seeds.
-/
theorem chainSingleKempeStep_of_chainSpecifiedKempeStep_of_mem
    (orients : List TauOrient) (s t : List TauState) (move : ChainMove)
    (hpair : (move.a, move.c) ∈ colorPairs)
    (hseed : move.seed ∈ chainEdges orients)
    (hstep : chainSpecifiedKempeStep orients s t move = true) :
    chainSingleKempeStep orients s t = true := by
  unfold chainSingleKempeStep
  rw [List.any_eq_true]
  refine ⟨(move.a, move.c), hpair, ?_⟩
  rw [List.any_eq_true]
  refine ⟨move.seed, hseed, ?_⟩
  simpa [chainSpecifiedKempeStep] using hstep

end GoertzelLemma814KempeAnchor

end Mettapedia.GraphTheory.FourColor
