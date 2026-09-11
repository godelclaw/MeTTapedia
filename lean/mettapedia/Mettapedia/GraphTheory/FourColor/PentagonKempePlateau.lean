import Mettapedia.GraphTheory.FourColor.InternalEdgeOpening
import Mettapedia.GraphTheory.FourColor.PentagonContextTensor

/-!
# A physical colouring with no immediate pentagon repair

The five displayed bichromatic paths are simultaneously realized by one
proper colouring of an explicit graph with five degree-one terminals.
No union of components of one colour pair makes its boundary extend across
the pentagon. Three explicit component-union switches do make it extend.

The accompanying program additionally checks the spherical embedding of
the ambient control, single-component status, and shortest distance three.
Those geometry and shortest-distance claims are not asserted here. This is
a proof-method obstruction, not a configuration-reducibility certificate.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonKempePlateau

open InternalEdgeOpening PentagonContextTensor

def low : Fin 3 → Fin 3 := ![0, 0, 1]
def high : Fin 3 → Fin 3 := ![1, 2, 2]

def Active {E : Type*} (c : E → Fin 3) (p : Fin 3) (e : E) : Prop :=
  c e = low p ∨ c e = high p

instance {E : Type*} (c : E → Fin 3) (p : Fin 3) (e : E) :
    Decidable (Active c p e) := inferInstanceAs (Decidable (_ ∨ _))

/-- A union of bichromatic components, expressed without a component census. -/
def Region {V E : Type*} (ends : E → V × V) (c : E → Fin 3)
    (p : Fin 3) (selected : E → Bool) : Prop :=
  (∀ e, selected e = true → Active c p e) ∧
  ∀ e f, Touch ends e f → Active c p e → Active c p f → selected e = selected f

instance {V E : Type*} [DecidableEq V] [Fintype E]
    (ends : E → V × V) (c : E → Fin 3) (p : Fin 3) (s : E → Bool) :
    Decidable (Region ends c p s) := by unfold Region; infer_instance

def switch {E : Type*} (c : E → Fin 3) (p : Fin 3) (s : E → Bool) : E → Fin 3 :=
  fun e => if s e then Equiv.swap (low p) (high p) (c e) else c e

def walkCheck {V E : Type*} [DecidableEq V] [DecidableEq E]
    (ends : E → V × V) (c : E → Fin 3) (p : Fin 3) (e : E) : List E → E → Bool
  | [], f => e == f
  | g :: gs, f => decide (Touch ends e g ∧ Active c p e ∧ Active c p g) &&
      walkCheck ends c p g gs f

/-- Region membership propagates along every checked bichromatic walk. -/
theorem region_eq_of_walk {V E : Type*} [DecidableEq V] [DecidableEq E]
    {ends : E → V × V} {c : E → Fin 3} {p : Fin 3} {s : E → Bool}
    (hr : Region ends c p s) (e f : E) (path : List E)
    (hw : walkCheck ends c p e path f = true) : s e = s f := by
  induction path generalizing e with
  | nil =>
    have hef : e = f := by simpa [walkCheck] using hw
    exact congrArg s hef
  | cons g gs ih =>
    have h : decide (Touch ends e g ∧ Active c p e ∧ Active c p g) = true ∧
        walkCheck ends c p g gs f = true := by simpa only [walkCheck, Bool.and_eq_true] using hw
    have he := of_decide_eq_true h.1
    exact (hr.2 e g he.1 he.2.1 he.2.2).trans (ih g h.2)

def ends : Fin 40 → Fin 30 × Fin 30 :=
  ![(0,3), (1,4), (2,7), (3,8), (3,9), (4,9), (4,10), (5,11), (6,12),
    (7,8), (7,13), (8,14), (9,15), (10,16), (10,17), (11,17), (11,18),
    (12,18), (12,19), (13,19), (13,20), (14,20), (14,21), (15,16),
    (15,21), (16,22), (17,23), (18,24), (19,25), (20,26), (21,27),
    (22,23), (22,28), (23,24), (24,29), (25,26), (25,29), (26,27),
    (27,28), (28,29)]

def ports : Fin 5 → Fin 40 := ![0, 1, 7, 8, 2]

def states : Fin 4 → Fin 40 → Fin 3
  | 0 => ![0,0,1,2,1,2,1,2,0,0,2,1,0,0,2,1,0,1,2,0,
           1,0,2,2,1,1,0,2,1,2,0,2,0,1,0,0,2,1,2,1]
  | 1 => ![0,2,1,2,1,0,1,0,0,0,2,1,2,2,0,1,2,1,2,0,
           1,2,0,0,1,1,2,0,1,0,2,0,2,1,2,2,0,1,0,1]
  | 2 => ![1,2,1,2,0,1,0,1,0,0,2,1,2,2,1,0,2,1,2,0,
           1,2,0,0,1,1,2,0,1,0,2,0,2,1,2,2,0,1,0,1]
  | 3 => ![1,1,1,2,0,2,0,2,0,0,2,1,1,2,1,0,1,2,1,0,
           1,2,0,0,2,1,2,0,2,0,1,0,2,1,2,1,0,2,0,1]

def boundary (c : Fin 40 → Fin 3) : Word := c ∘ ports

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem states_proper : ∀ j, Proper ends (states j) := by
  intro j
  fin_cases j <;> decide +kernel

/-- Matching constraints read from the actual paths, not chosen independently. -/
def Matches : Fin 3 → (Fin 5 → Bool) → Prop
  | 0, s => s 0 = s 4 ∧ s 1 = s 3
  | 1, s => s 0 = s 3 ∧ s 1 = s 2
  | 2, s => s 2 = s 4

instance : (p : Fin 3) → (s : Fin 5 → Bool) → Decidable (Matches p s)
  | 0, s => inferInstanceAs (Decidable (s 0 = s 4 ∧ s 1 = s 3))
  | 1, s => inferInstanceAs (Decidable (s 0 = s 3 ∧ s 1 = s 2))
  | 2, s => inferInstanceAs (Decidable (s 2 = s 4))

set_option maxRecDepth 100000 in
theorem matches_of_region (p : Fin 3) (s : Fin 40 → Bool)
    (hr : Region ends (states 0) p s) : Matches p (s ∘ ports) := by
  fin_cases p
  · constructor
    · exact region_eq_of_walk hr 0 2
        [4,12,24,30,37,35,28,19,20,21,11,9,2] (by decide +kernel)
    · exact region_eq_of_walk hr 1 8
        [6,13,25,32,39,34,33,26,15,16,17,8] (by decide +kernel)
  · constructor
    · exact region_eq_of_walk hr 0 8 [3,9,10,19,18,8] (by decide +kernel)
    · exact region_eq_of_walk hr 1 7
        [5,12,23,13,14,26,31,32,38,30,22,21,29,35,36,34,27,16,7]
        (by decide +kernel)
  · exact region_eq_of_walk hr 7 2
      [15,14,6,5,4,3,11,22,24,23,25,31,33,27,17,18,28,36,39,38,37,29,20,10,2]
      (by decide +kernel)

set_option maxRecDepth 100000 in
private theorem boundary_check : ∀ (p : Fin 3) (s : Fin 5 → Bool),
    Matches p s → (∀ i, s i = true → Active (boundary (states 0)) p i) →
    fastPentagonCount (switch (boundary (states 0)) p s) = 0 := by decide +kernel

/-- Even an arbitrary union of components of one colour pair cannot repair
this colouring. There is no enumeration over the forty-edge region carrier. -/
theorem no_immediate_repair (p : Fin 3) (s : Fin 40 → Bool)
    (hr : Region ends (states 0) p s) :
    PentagonPositiveResolution.pentagonCount (color ∘ boundary (switch (states 0) p s)) = 0 := by
  rw [pentagonCount_eq_fast]
  exact boundary_check p (s ∘ ports) (matches_of_region p s hr) (fun i => hr.1 (ports i))

def stepPair : Fin 3 → Fin 3 := ![1, 0, 2]

def stepEdges : Fin 3 → List (Fin 40)
  | 0 => [1,5,7,12,13,14,16,21,22,23,26,27,29,30,31,32,34,35,36,38]
  | 1 => [0,4,5,6,7,14,15]
  | 2 => [1,5,7,12,16,17,18,24,28,30,35,37]

def selected (j : Fin 3) (e : Fin 40) : Bool := (stepEdges j).contains e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem escape_regions : ∀ j : Fin 3,
    Region ends (states j.castSucc) (stepPair j) (selected j) := by
  intro j
  fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
theorem escape_switches : ∀ j : Fin 3,
    switch (states j.castSucc) (stepPair j) (selected j) = states j.succ := by
  decide +kernel

theorem intermediate_counts : ∀ j : Fin 3,
    PentagonPositiveResolution.pentagonCount (color ∘ boundary (states j.castSucc)) = 0 := by
  simp only [pentagonCount_eq_fast]
  decide +kernel

theorem final_count :
    PentagonPositiveResolution.pentagonCount (color ∘ boundary (states 3)) = 1 := by
  rw [pentagonCount_eq_fast]
  decide +kernel

end Mettapedia.GraphTheory.FourColor.PentagonKempePlateau
