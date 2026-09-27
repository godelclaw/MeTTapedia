import Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer
import Mathlib.Data.Finset.NAry

/-!
# Computable small-cut profile extraction and transfer

The extractor exhausts vertex subsets of an explicitly finite multigraph.
The transition itself only sees finite sets of boundary records. Its
correctness is equality with the complete physically realized profile,
including states whose cut size is saturated at two.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundarySmallCutExecutable

open GoertzelV24BoundaryEssentialGluing BoundarySmallCutProfile BoundarySmallCutTransfer

variable {P : Type*}

instance [Fintype P] : DecidableEq (State P) := fun a b =>
  decidable_of_iff
    (a.boundary = b.boundary ∧ a.selected = b.selected ∧
      a.omitted = b.omitted ∧ a.cost = b.cost) (by
    constructor
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      cases a; cases b
      congr
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl⟩)

variable {V E : Type*} [Fintype V] [Fintype E]

def ofAssignment (G : Multigraph V E) (ports : P → V) (s : V → Bool) : State P where
  boundary := s ∘ ports
  selected := decide (∃ v, s v = true)
  omitted := decide (∃ v, s v = false)
  cost := ⟨min 2 (∑ e, if s (G.fst e) = s (G.snd e) then 0 else 1), by omega⟩

theorem ofAssignment_eq (G : Multigraph V E) (ports : P → V) (s : V → Bool) :
    ofAssignment G ports s = state G ports s := by
  simp only [ofAssignment, state, cutSize]
  congr 1
  · exact congrArg (@decide _) (Subsingleton.elim _ _)
  · exact congrArg (@decide _) (Subsingleton.elim _ _)

def extract [DecidableEq V] [Fintype P] (G : Multigraph V E) (ports : P → V) : Finset (State P) :=
  Finset.univ.image (ofAssignment G ports)

theorem extract_correct [DecidableEq V] [Fintype P] (G : Multigraph V E) (ports : P → V) :
    (extract G ports : Set (State P)) = profile G ports := by
  ext a
  simp [extract, profile, ofAssignment_eq]

/-- No realized nontrivial cut has cost zero or one. For an open piece
this tests its interior graph; for a closed result it tests the whole graph. -/
def accepts (a : Finset (State P)) : Bool :=
  decide (∀ q ∈ a, ¬ (q.selected = true ∧ q.omitted = true ∧ q.cost.val ≤ 1))

theorem accepts_iff (a : Finset (State P)) :
    accepts a = true ↔ ∀ q ∈ a, ¬ (q.selected = true ∧ q.omitted = true ∧ q.cost.val ≤ 1) := by
  simp [accepts]

theorem accepts_extract [DecidableEq V] [Fintype P] (G : Multigraph V E) (ports : P → V) :
    accepts (extract G ports) = true ↔ G.Connected ∧ G.Bridgeless := by
  rw [← SmallCutConnectedBridgeless.no_small_cut_iff, accepts_iff]
  simp only [extract, Finset.mem_image, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, ofAssignment_eq]
  simp only [HasSmallCut, IsSmallCut, state, decide_eq_true_eq]
  simp only [not_exists]
  have hcap (n : Nat) : min 2 n ≤ 1 ↔ n ≤ 1 := by omega
  simp only [hcap]

variable {L R : Type*} [Fintype L] [Fintype P] [Fintype R]

/-- A computable deduplicating transition over boundary records alone. -/
def transfer (a : Finset (State (L ⊕ P))) (b : Finset (State (P ⊕ R))) :
    Finset (State (L ⊕ R)) := Finset.image₂ composeState a b

theorem transfer_correct (a : Finset (State (L ⊕ P))) (b : Finset (State (P ⊕ R))) :
    (transfer a b : Set (State (L ⊕ R))) =
      composeProfile (a : Set (State (L ⊕ P))) (b : Set (State (P ⊕ R))) :=
  Finset.coe_image₂ _ _ _

theorem transfer_assoc {Q : Type*} [Fintype Q]
    (a : Finset (State (L ⊕ P))) (b : Finset (State (P ⊕ Q))) (c : Finset (State (Q ⊕ R))) :
    transfer (transfer a b) c = transfer a (transfer b c) := by
  apply Finset.coe_injective
  simp only [transfer_correct]
  exact composeProfile_assoc _ _ _

variable {W F : Type*} [Fintype W] [Fintype F] [DecidableEq V] [DecidableEq W]

theorem extract_glue (A : Multigraph V E) (B : Multigraph W F)
    (lA : L → V) (pA : P → V) (pB : P → W) (rB : R → W) :
    extract (glue A B pA pB) (outsidePorts lA rB) =
      transfer (extract A (Sum.elim lA pA)) (extract B (Sum.elim pB rB)) := by
  apply Finset.coe_injective
  rw [extract_correct, transfer_correct, extract_correct, extract_correct]
  exact profile_glue A B lA pA pB rB

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open OpenTangleCutDartSum SerialTangleSmallCutTransfer

/-- Compute directly from the literal dart data, without choosing quotient
edge representatives. The symmetric cut sum counts each edge twice. -/
def ofTangleAssignment (T : TwoSidedOpenTangleData V E L P) (s : V → Bool) : State (L ⊕ P) where
  boundary := s ∘ Sum.elim T.leftVert T.rightVert
  selected := decide (∃ v, s v = true)
  omitted := decide (∃ v, s v = false)
  cost := ⟨min 2 ((∑ d, bit (s (T.interiorVert d))
    (s (T.interiorVert (T.interiorAlpha d)))) / 2), by omega⟩

omit [Fintype L] [Fintype P] [DecidableEq V] in
theorem ofTangleAssignment_eq [DecidableEq E]
    (T : TwoSidedOpenTangleData V E L P) (s : V → Bool) :
    ofTangleAssignment T s = state (sideMultigraph (asOpen T)) (asOpen T).boundaryVert s := by
  have h := twice_cutSize (asOpen T) s
  conv at h => rhs; dsimp [asOpen]
  unfold ofTangleAssignment state
  congr 1
  · exact congrArg (@decide _) (Subsingleton.elim _ _)
  · exact congrArg (@decide _) (Subsingleton.elim _ _)
  · apply Fin.ext
    change min 2 ((∑ d, bit (s (T.interiorVert d))
      (s (T.interiorVert (T.interiorAlpha d)))) / 2) =
      min 2 (cutSize (sideMultigraph (asOpen T)) s)
    rw [← h]
    omega

def extractTangle (T : TwoSidedOpenTangleData V E L P) : Finset (State (L ⊕ P)) :=
  Finset.univ.image (ofTangleAssignment T)

theorem extractTangle_correct [DecidableEq E] (T : TwoSidedOpenTangleData V E L P) :
    (extractTangle T : Set (State (L ⊕ P))) =
      profile (sideMultigraph (asOpen T)) (asOpen T).boundaryVert := by
  ext a
  simp [extractTangle, profile, ofTangleAssignment_eq]

/-- The executable dart-data extractor commutes with actual serial sewing. -/
theorem extractTangle_serial [DecidableEq E] [DecidableEq F] [DecidableEq P]
    (A : TwoSidedOpenTangleData V E L P) (B : TwoSidedOpenTangleData W F P R) :
    extractTangle (A.serialCompose B (Equiv.refl P)) =
      transfer (extractTangle A) (extractTangle B) := by
  apply Finset.coe_injective
  rw [extractTangle_correct, transfer_correct, extractTangle_correct, extractTangle_correct]
  exact profile_serial A B

/-- The executable transition computes the actual serial-tangle profile. -/
theorem extract_serial [DecidableEq E] [DecidableEq F] [DecidableEq P]
    (A : TwoSidedOpenTangleData V E L P) (B : TwoSidedOpenTangleData W F P R) :
    extract (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P))))
        (asOpen (A.serialCompose B (Equiv.refl P))).boundaryVert =
      transfer (extract (sideMultigraph (asOpen A)) (asOpen A).boundaryVert)
        (extract (sideMultigraph (asOpen B)) (asOpen B).boundaryVert) := by
  apply Finset.coe_injective
  rw [extract_correct, transfer_correct, extract_correct, extract_correct]
  exact profile_serial A B

end Mettapedia.GraphTheory.FourColor.BoundarySmallCutExecutable
