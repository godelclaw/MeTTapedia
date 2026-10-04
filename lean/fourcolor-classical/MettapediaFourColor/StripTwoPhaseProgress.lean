import MettapediaFourColor.StripPuncturedExtension
import MettapediaFourColor.KempeRetainedMatching

/-!
# Two adaptive batches restore seven vertices of the strip core

Four difficult boundary words first use a chord cover retaining a single
exterior matching. Only five intermediate forms require a fresh matching;
all use the same anchor-selection theorem and punctured-source elimination.
No full matching layouts or interior-colouring table are stored.
-/

namespace FourColor.StripTwoPhaseProgress

open Color StripPuncturedExtension KempeRetainedMatching KempeIntervalRepair

def source : Fin 9 → Fin 11 → Color
  | 0 => ![c1,c2,c3,c1,c2,c1,c2,c1,c1,c3,c3]
  | 1 => ![c1,c2,c1,c3,c3,c1,c1,c3,c1,c1,c1]
  | 2 => ![c1,c2,c3,c1,c1,c3,c3,c1,c3,c1,c3]
  | 3 => ![c1,c2,c3,c3,c1,c3,c1,c3,c3,c3,c3]
  | 4 => ![c1,c2,c2,c1,c2,c2,c2,c2,c1,c2,c3]
  | 5 => ![c1,c2,c3,c1,c1,c2,c2,c1,c1,c3,c3]
  | 6 => ![c1,c2,c3,c1,c1,c3,c3,c1,c1,c3,c3]
  | 7 => ![c1,c2,c3,c1,c2,c3,c3,c2,c1,c3,c3]
  | 8 => ![c1,c2,c3,c1,c3,c2,c2,c3,c1,c3,c3]

def palette : Fin 9 → EdgePerm := ![.e213,.e213,.e123,.e123,.e321,.e321,.e213,.e123,.e123]
def colour (s : Fin 9) (i : Fin 11) : Color := palette s (source s i)

def anchor0 : Fin 9 → Fin 11 := ![3,0,1,1,0,0,3,1,1]
def anchor1 : Fin 9 → Fin 11 := ![9,2,2,5,1,1,6,4,5]

def singles : Fin 9 → List (Fin 11 × Fin 11)
  | 0 => [(8,9),(5,7),(5,9),(2,3),(0,10)]
  | 1 => [(7,8),(6,7),(5,6),(4,5),(7,10)]
  | 2 => [(8,10),(1,10),(5,10)]
  | 3 => [(9,10),(7,8),(7,10),(3,10),(3,5)]
  | 4 => [(8,9),(6,7),(4,5),(2,3),(1,2),(0,1),(2,7),(2,5)]
  | 5 => [(5,6),(4,5),(3,4),(0,4)]
  | 6 => [(7,8),(8,9),(5,8),(5,6),(0,8)]
  | 7 => [(4,5),(2,4),(1,2)]
  | 8 => [(4,5),(2,4),(1,2)]

def doubles : Fin 9 → List (Fin 11 × Fin 11)
  | 0 => [(5,10)]
  | 1 => []
  | 2 => []
  | 3 => [(10,7)]
  | 4 => []
  | 5 => []
  | 6 => [(8,7)]
  | 7 => [(10,7)]
  | 8 => [(10,6)]

def single (s : Fin 9) (i j : Fin 11) : Bool :=
  decide ((i,j) ∈ singles s ∨ (j,i) ∈ singles s)
def double (s : Fin 9) (p q : Fin 11) : Bool := decide ((p,q) ∈ doubles s)

theorem active_anchors : ∀ s,
    (∀ i, colour s i ≠ 0) ∧ colour s (anchor0 s) ≠ c1 ∧ colour s (anchor1 s) ≠ c1 :=
  by decide +kernel

/-- Interval exclusion covers all noncrossing matchings without enumerating
those matchings in the proof. Both anchor partners belong to the same one. -/
theorem select : ∀ s p q, double s p q = false →
    KempeIntervalMatching.possible (active (colour s))
      (allowed (single s) (anchor0 s) p (anchor1 s) q) 0 11 = false := by
  decide +kernel

theorem middle_one : ∀ s : Fin 5, ∀ i j, single (s.castAdd 4) i j = true →
    Direct (List.ofFn (switch (colour (s.castAdd 4)) i j)) := by decide +kernel

theorem middle_two : ∀ s : Fin 5, ∀ p q, double (s.castAdd 4) p q = true →
    Direct (List.ofFn (switch (switch (colour (s.castAdd 4)) (anchor0 (s.castAdd 4)) p)
      (anchor1 (s.castAdd 4)) q)) := by decide +kernel

/-- Every possible terminal answer has an actual seven-vertex partial
source witness, recovered by the same symbolic elimination. -/
theorem middle (s : Fin 5) : KempeCoclosure Terminal (List.ofFn (source (s.castAdd 4))) := by
  apply kempeCoclosure_of_map (palette (s.castAdd 4))
  change KempeCoclosure Terminal (List.ofFn (colour (s.castAdd 4)))
  apply two_anchor_coclosure _ (active_anchors _).1 (anchor0 _) (anchor1 _)
    (active_anchors _).2.1 (active_anchors _).2.2 (single _) (double _)
  · exact fun i j h => direct_coclosure (middle_one s i j h)
  · exact fun p q h => direct_coclosure (middle_two s p q h)
  · exact select _

def Ready (et : List Color) : Prop :=
  (∃ s : Fin 5, ∃ g : EdgePerm, et.map g = List.ofFn (source (s.castAdd 4))) ∨ Direct et
instance (et) : Decidable (Ready et) := by unfold Ready; infer_instance

theorem ready_sound {et} (h : Ready et) : KempeCoclosure Terminal et := by
  rcases h with ⟨s,g,hg⟩ | h
  · apply kempeCoclosure_of_map g
    rw [hg]
    exact middle s
  · exact direct_coclosure h

theorem first_one : ∀ s : Fin 4, ∀ i j, single (s.natAdd 5) i j = true →
    Ready (List.ofFn (switch (colour (s.natAdd 5)) i j)) := by decide +kernel

theorem first_two : ∀ s : Fin 4, ∀ p q, double (s.natAdd 5) p q = true →
    Ready (List.ofFn (switch (switch (colour (s.natAdd 5)) (anchor0 (s.natAdd 5)) p)
      (anchor1 (s.natAdd 5)) q)) := by decide +kernel

/-- Each first answer retains the same Kempe-closed exterior. If needed,
the continuation queries its current matching; it does not reuse a stale
partition or replace the exterior by an independently favourable one. -/
theorem progress (s : Fin 4) : KempeCoclosure Terminal (List.ofFn (source (s.natAdd 5))) := by
  apply kempeCoclosure_of_map (palette (s.natAdd 5))
  change KempeCoclosure Terminal (List.ofFn (colour (s.natAdd 5)))
  apply two_anchor_coclosure _ (active_anchors _).1 (anchor0 _) (anchor1 _)
    (active_anchors _).2.1 (active_anchors _).2.2 (single _) (double _)
  · exact fun i j h => ready_sound (first_one s i j h)
  · exact fun p q h => ready_sound (first_two s p q h)
  · exact select _

end FourColor.StripTwoPhaseProgress
