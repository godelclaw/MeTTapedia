import MettapediaFourColor.FiveTriangleCollapseObstruction

/-!
# A coordinated recolouring with the same fan exterior

The source and target carry the same ordered ten-port fan after deleting source
boundary vertex 7 (zero-based). A single whole bichromatic component switch in
the source together with this exterior supplies a colouring that agrees with a
genuine target colouring at every retained port. The exterior is present in
both properness checks. This is one concrete repair, not a uniform family law.
-/

namespace FourColor.FiveTriangleJointChoice

open Color FiveTriangleCollapseObstruction

set_option maxRecDepth 32768

/-- Add explicitly retained exterior edges to an actual simple graph. -/
def edgeGraph {V : Type*} (edges : List (V × V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {V : Type*} [DecidableEq V] (edges : List (V × V)) :
    DecidableRel (edgeGraph edges).Adj := by unfold edgeGraph; infer_instance

/-- Existing ring edges are already present; these are the additional fan edges. -/
def sourceExterior : List (Fin 18 × Fin 18) :=
  [(6, 8), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6)]

def targetExterior : List (Fin 17 × Fin 17) :=
  [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8)]

def sourceGraph := upper.graph ⊔ edgeGraph sourceExterior
def targetGraph := lower.graph ⊔ edgeGraph targetExterior

instance : DecidableRel sourceGraph.Adj := by unfold sourceGraph; infer_instance
instance : DecidableRel targetGraph.Adj := by unfold targetGraph; infer_instance

def ports : Fin 10 → Fin 18 := ![9, 10, 0, 1, 2, 3, 4, 5, 6, 8]

def fanAdj (i j : Fin 10) : Prop := i ≠ j ∧
  ((i.val + 1) % 10 = j.val ∨ (j.val + 1) % 10 = i.val ∨ i = 0 ∨ j = 0)

instance : DecidableRel fanAdj := by unfold fanAdj; infer_instance

/-- Both retained interfaces induce exactly the same fan, with distinct ports. -/
theorem fan_exact : Function.Injective ports ∧ ∀ i j : Fin 10,
    (sourceGraph.Adj (ports i) (ports j) ↔ fanAdj i j) ∧
    (targetGraph.Adj (i.castAdd 7) (j.castAdd 7) ↔ fanAdj i j) := by
  decide +kernel

def before : Fin 18 → Color :=
  ![c0, c1, c0, c1, c0, c1, c0, c1, c3, c2, c3, c1, c2, c3, c0, c3, c0, c2]

def component (v : Fin 18) : Prop := v = 2 ∨ v = 15
instance : DecidablePred component := by unfold component; infer_instance

def after (v : Fin 18) : Color := if component v then c3 + before v else before v

def target : Fin 17 → Color :=
  ![c2, c3, c0, c1, c3, c1, c0, c1, c0, c3, c2, c0, c2, c0, c3, c2, c1]

/-- The two switched vertices are adjacent, and no active-colour edge leaves them. -/
theorem whole_component :
    before 2 = c0 ∧ before 15 = c3 ∧ sourceGraph.Adj 2 15 ∧
      ∀ u v, component u → sourceGraph.Adj u v →
        (before v = c0 ∨ before v = c3) → component v := by decide +kernel

theorem before_proper : ∀ u v, sourceGraph.Adj u v → before u ≠ before v := by
  decide +kernel

theorem after_proper : ∀ u v, sourceGraph.Adj u v → after u ≠ after v := by
  decide +kernel

theorem target_proper : ∀ u v, targetGraph.Adj u v → target u ≠ target v := by
  decide +kernel

/-- Actual vertex colours agree, with no independent permutation on either piece. -/
theorem boundary_agreement : ∀ i : Fin 10, after (ports i) = target (i.castAdd 7) := by
  decide +kernel

def sourceColouring : sourceGraph.Coloring Color := .mk after (fun h => after_proper _ _ h)
def targetColouring : targetGraph.Coloring Color := .mk target (fun h => target_proper _ _ h)

/-- Both colourings include their exterior constraints and share the same choices. -/
theorem compatible_witnesses :
    ∃ ks : sourceGraph.Coloring Color, ∃ kt : targetGraph.Coloring Color,
      ∀ i : Fin 10, ks (ports i) = kt (i.castAdd 7) :=
  ⟨sourceColouring, targetColouring, boundary_agreement⟩

end FourColor.FiveTriangleJointChoice
