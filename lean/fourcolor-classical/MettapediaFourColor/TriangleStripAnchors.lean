import MettapediaFourColor.TwoPortCoreElimination
import Mettapedia.GraphTheory.Kempe.TriangleAnchors

/-!
# Two retained colours for three decoded triangle strips

D0092, D0063 and D0099 satisfy one elimination-order contract. Two structural
anchor vertices suffice in each. Retaining their physical colours and the
joint forest guard preserves exactly the fixed-exterior Kempe histories.
The consumer applies to any exact induced occurrence, not just a free
completion. The exterior may have arbitrary edges and Kempe connections.

D0099 is from near-linear-4ct/reducible-configurations, revision
c2ce7a96e35256201526e2abb51a39d04a588b53, copyright 2026 Yuta Inoue (MIT).
The source and licence are retained under tools/fourcolor/near-linear.
The other decoded sources are inherited from FiveTriangleCollapseObstruction.
No reducibility, existence of a useful guarded move, or coverage is asserted.
-/

namespace FourColor.TriangleStripAnchors

open SimpleGraph Relation NearLinearDiamondData KempeTriangleAnchors

inductive Source where
  | d0092 | d0063 | d0099
  deriving DecidableEq

def size : Source → ℕ
  | .d0092 | .d0063 => 7
  | .d0099 => 8

def input0099 : Input 19 11 where
  source := "19 11\n\
    12 5 8 9 13 15 7\n\
    13 5 9 16 14 15 12\n\
    14 7 5 15 13 16 18 17 4\n\
    15 6 6 7 12 13 14 5\n\
    16 5 10 18 14 13 9\n\
    17 6 3 4 14 18 19 2\n\
    18 6 11 19 17 14 16 10\n\
    19 5 2 17 18 11 1\n\
    "
  valid := by decide +kernel

def vertex0099 (x : Fin 8) : Fin 19 := ⟨11 + x.val, by omega⟩

/-- Complete internal adjacency from the decoded sources. -/
def core : (s : Source) → SimpleGraph (Fin (size s))
  | .d0092 => TwoPortCoreElimination.core false
  | .d0063 => TwoPortCoreElimination.core true
  | .d0099 => input0099.graph.comap vertex0099

instance (s : Source) : DecidableRel (core s).Adj := by
  cases s <;> intro x y <;>
    change Decidable (_ ≠ _ ∧ (_ ∨ _ ∨ _)) <;>
    unfold Input.ringEdge <;> infer_instance

def rank : (s : Source) → Fin (size s) → ℕ
  | .d0092 => ![6,2,0,1,3,5,4]
  | .d0063 => ![6,1,0,5,3,2,4]
  | .d0099 => ![7,6,4,5,3,1,2,0]

def colourData : (s : Source) → Fin (size s) → Fin 3
  | .d0092 => ![0,2,0,1,1,1,2]
  | .d0063 => ![0,1,0,1,2,0,2]
  | .d0099 => ![0,1,0,2,2,2,1,0]

theorem rank_injective (s : Source) : Function.Injective (rank s) := by
  cases s <;> decide +kernel

theorem colour_proper (s : Source) : ∀ x y,
    (core s).Adj x y → colourData s x ≠ colourData s y := by
  cases s <;> decide +kernel

theorem later_clique (s : Source) : ∀ v x y,
    (core s).Adj v x → (core s).Adj v y →
    rank s v < rank s x → rank s v < rank s y → x ≠ y → (core s).Adj x y := by
  cases s <;> decide +kernel

def structuralColour (s : Source) : (core s).Coloring (Fin 3) :=
  .mk (colourData s) (colour_proper s _ _)

def anchorColour : Source → Fin 3
  | .d0092 => 0
  | .d0063 | .d0099 => 1

/-- Source labels: D0092 retains 12 and 14; D0063 retains 12 and 14;
D0099 retains 13 and 18. These are physical colour observations, not a
restriction that a repair use the structural three-colouring. -/
theorem two_anchors (s : Source) :
    (Finset.univ.filter fun x => colourData s x = anchorColour s).card = 2 := by
  cases s <;> decide +kernel

theorem source_forest (s : Source) :
    ((core s).induce {v | structuralColour s v ≠ anchorColour s}).IsAcyclic :=
  delete_class_acyclic (rank s) (rank_injective s) (later_clique s)
    (structuralColour s) (anchorColour s)

/-- A single proof handles all three source cores in arbitrary finite
surrounding graphs, retaining shared anchor choices and actual exterior data. -/
theorem repair_contract {V α : Type*} [Fintype V] [DecidableEq α]
    {G : SimpleGraph V} (s : Source) (S : Set V) (read : G.induce S ≃g core s)
    (C D : G.Coloring α) :
    let K := anchors S read (structuralColour s) (anchorColour s)
    ReflTransGen (KempeGuardedLift.Step (S \ K) Sᶜ)
      (C.restrictInduce (S \ K)ᶜ) (D.restrictInduce (S \ K)ᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding Sᶜ) C D :=
  occurrence_history_iff S read (rank s) (rank_injective s) (later_clique s)
    (structuralColour s) (anchorColour s) C D

/-- Any two full colourings agreeing on the exterior and the two anchors
can be joined without changing either. Hidden internal choices are harmless
once these observations are retained. -/
theorem same_observations {V α : Type*} [Fintype V] [DecidableEq α]
    {G : SimpleGraph V} (s : Source) (S : Set V) (read : G.induce S ≃g core s)
    (C D : G.Coloring α) (outside : ∀ x, x ∉ S → C x = D x)
    (retained : ∀ x ∈ anchors S read (structuralColour s) (anchorColour s), C x = D x) :
    ReflTransGen (G.KempeStepAvoiding
      (S \ anchors S read (structuralColour s) (anchorColour s))ᶜ) C D :=
  KempeCycleAnchors.same_anchor_path S _
    (occurrence_forest S read (rank s) (rank_injective s) (later_clique s)
      (structuralColour s) (anchorColour s)) C D outside retained

end FourColor.TriangleStripAnchors
