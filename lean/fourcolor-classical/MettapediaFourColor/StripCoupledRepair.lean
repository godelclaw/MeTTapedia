import MettapediaFourColor.KempeRetainedMatching
import MettapediaFourColor.StripSymbolicRepair
import MettapediaFourColor.StripPartialColouring

/-!
# Two D0099 repairs preserving the original component matching

If no single component gives a source extension, two specified anchor
components do so together. The interval theorem supplies this dichotomy;
matching layouts and full colouring witnesses are not stored. The terminal
consumer reconstructs the three omitted vertices using their joint contract.
-/

namespace FourColor.StripCoupledRepair

open Color StripSymbolicRepair StripPartialColouring StripResponseSummary
open KempeRetainedMatching KempeIntervalRepair

def source : Bool → Fin 11 → Color
  | false => ![c1,c1,c1,c1,c1,c1,c1,c2,c2,c2,c3]
  | true => ![c1,c1,c1,c1,c1,c1,c1,c2,c3,c2,c2]

def colour (s : Bool) (i : Fin 11) : Color := EdgePerm.e321 (source s i)
def anchor (s : Bool) : Fin 11 := if s then 2 else 1

def singlePairs : Bool → List (Fin 11 × Fin 11)
  | false => [(0,7),(2,3),(2,9),(7,8),(8,9)]
  | true => [(0,3),(2,10),(4,5),(5,6),(6,7),(6,10),(7,9)]

def doublePairs : Bool → List (Fin 11 × Fin 11)
  | false => [(3,2),(9,2),(9,8)]
  | true => [(7,5)]

def single (s : Bool) (i j : Fin 11) : Bool :=
  decide ((i,j) ∈ singlePairs s ∨ (j,i) ∈ singlePairs s)

def double (s : Bool) (p q : Fin 11) : Bool := decide ((p,q) ∈ doublePairs s)

theorem active_anchors : ∀ s,
    (∀ i, colour s i ≠ 0) ∧ colour s 0 ≠ c1 ∧ colour s (anchor s) ≠ c1 :=
  by decide +kernel

/-- Only pairs of possible anchor partners are checked. The interval
recurrence excludes the unsuccessful cases without listing full matchings. -/
theorem select : ∀ s p q, double s p q = false →
    KempeIntervalMatching.possible (active (colour s))
      (allowed (single s) 0 p (anchor s) q) 0 11 = false := by decide +kernel

theorem one_direct : ∀ s i j, single s i j = true →
    Direct ((List.ofFn (switch (colour s) i j)).map EdgePerm.e321) := by decide +kernel

theorem two_direct : ∀ s p q, double s p q = true →
    Direct ((List.ofFn (switch (switch (colour s) 0 p) (anchor s) q)).map EdgePerm.e321) :=
  by decide +kernel

private theorem fill_self (f : Fin 8 → Color) : fill f (f 0) (f 2) (f 5) = f := by
  funext i
  fin_cases i <;> rfl

/-- The terminal relation supplies common choices for all three holes;
restoration consumes their shared constraint, including the edge 2--5. -/
theorem direct_completion {et : List Color} (h : Direct et) : Terminal et := by
  obtain ⟨f,hf⟩ := (terminal_iff (readBoundary et)).mp h.2.2
  have parts := (fill_iff (readBoundary et) f (f 0) (f 2) (f 5)).mp
    (by simpa only [fill_self] using hf)
  exact h.1 ▸ reconstruct (readBoundary et) h.2.1 f parts.1 parts.2

theorem completion_coclosure {et : List Color} (h : Direct et) :
    KempeCoclosure Terminal et := by
  intro outside _ hold
  exact ⟨et, direct_completion h, hold⟩

/-- The two switches use one matching recovered from the original exterior.
No assumption supplies a new favourable exterior between those switches. -/
theorem source_repair (s : Bool) : KempeCoclosure Terminal (List.ofFn (source s)) := by
  apply kempeCoclosure_of_map EdgePerm.e321
  change KempeCoclosure Terminal (List.ofFn (colour s))
  apply two_anchor_coclosure (colour s) (active_anchors s).1 0 (anchor s)
    (active_anchors s).2.1 (active_anchors s).2.2 (single s) (double s)
  · intro i j h
    apply kempeCoclosure_of_map EdgePerm.e321
    exact completion_coclosure (one_direct s i j h)
  · intro p q h
    apply kempeCoclosure_of_map EdgePerm.e321
    exact completion_coclosure (two_direct s p q h)
  · exact select s

theorem input_trace : ∀ s,
    trace (List.ofFn (readBoundary (List.ofFn (source s)))) = List.ofFn (source s) :=
  by decide +kernel

theorem input_empty : ∀ s,
    ¬ ∃ a b, r5 (readBoundary (List.ofFn (source s))) a b := by decide +kernel

theorem input_nonextension (s : Bool) : ¬ Terminal (List.ofFn (source s)) := by
  rw [← input_trace s]
  exact no_trace _ (input_empty s)

end FourColor.StripCoupledRepair
