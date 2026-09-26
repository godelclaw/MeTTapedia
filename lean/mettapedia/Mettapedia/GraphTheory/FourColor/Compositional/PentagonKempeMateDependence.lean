import Mettapedia.GraphTheory.FourColor.PentagonKempePlateau

/-!
# Boundary mates do not determine an update of a fixed physical component

On the existing forty-edge control, two proper colourings have the same
boundary word and the same three boundary connectedness relations. The same
seven edges form the component rooted at the first port in both colourings.
Switching that component gives different boundary connectedness relations.

Connectivity is certified by literal walks and component labels constant on
every physical local step. No search over colourings or assumed mate table
occurs in the proof. This is a finite endpoint-graph obstruction to a proposed
state compression; the spherical embedding of the control is not asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeMateDependence

open InternalEdgeOpening PentagonKempePlateau

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def first : Fin 40 → Fin 3 :=
  ![0,0,0,1,2,1,2,1,2,2,1,0,0,0,1,2,0,1,0,2,
    0,1,2,2,1,1,0,2,1,2,0,2,0,1,0,0,2,1,2,1]

private def second : Fin 40 → Fin 3 :=
  ![0,0,0,1,2,1,2,1,2,2,1,0,0,1,0,2,0,1,0,2,
    0,1,2,2,1,0,1,2,1,2,0,2,1,0,1,0,2,1,2,0]

def regionMask (e : Fin 40) : Bool := ([0, 2, 3, 10, 11, 20, 21] : List (Fin 40)).contains e

def coloring : Fin 4 → Fin 40 → Fin 3
  | 0 => first
  | 1 => second
  | 2 => PentagonKempePlateau.switch first 0 regionMask
  | 3 => PentagonKempePlateau.switch second 0 regionMask

theorem colorings_proper : ∀ s, Proper ends (coloring s) := by
  intro s
  fin_cases s <;> decide +kernel

def LocalStep (c : Fin 40 → Fin 3) (p : Fin 3) (e f : Fin 40) : Prop :=
  Touch ends e f ∧ Active c p e ∧ Active c p f

def Connected (c : Fin 40 → Fin 3) (p : Fin 3) : Fin 40 → Fin 40 → Prop :=
  Relation.EqvGen (LocalStep c p)

private theorem label_eq_of_connected {A : Type*} {c : Fin 40 → Fin 3} {p : Fin 3}
    (label : Fin 40 → A) (hlabel : ∀ e f, LocalStep c p e f → label e = label f)
    {e f : Fin 40} (h : Connected c p e f) : label e = label f := by
  induction h with
  | rel _ _ h => exact hlabel _ _ h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem connected_of_walk {c : Fin 40 → Fin 3} {p : Fin 3}
    (e f : Fin 40) (path : List (Fin 40))
    (h : walkCheck ends c p e path f = true) : Connected c p e f := by
  induction path generalizing e with
  | nil =>
    have hef : e = f := by simpa [walkCheck] using h
    subst f
    exact Relation.EqvGen.refl _
  | cons g gs ih =>
    have hh : decide (Touch ends e g ∧ Active c p e ∧ Active c p g) = true ∧
        walkCheck ends c p g gs f = true := by simpa only [walkCheck, Bool.and_eq_true] using h
    have hstep : Touch ends e g ∧ Active c p e ∧ Active c p g := of_decide_eq_true hh.1
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hstep) (ih g hh.2)

/-- A bounded walk generator. Soundness is checked independently by `walkCheck`. -/
private def findWalk (c : Fin 40 → Fin 3) (p : Fin 3)
    (previous : Option (Fin 40)) (current target : Fin 40) : Nat → List (Fin 40)
  | 0 => []
  | n + 1 =>
    if current = target then [] else
    match (List.finRange 40).find? (fun e => decide
      (e ≠ current ∧ some e ≠ previous ∧ Touch ends current e ∧ Active c p e)) with
    | none => []
    | some next => next :: findWalk c p (some current) next target n

/-- Flat component-label certificate; inactive edges get distinct labels below. -/
private def rawLabels : String :=
  "010091919900122911190099122919192221919200190909119100911911191099119111191119199990000000099900909090000090009090990000" ++
  "010091919900122911190099122919192221919200190909119109000911191090909110909119119990000000099090909090000900009009090009" ++
  "010091919900122911190099122919192221919290900909000900911900911099119111191119190919000011919900919229111191229191992222" ++
  "010091919900122911190099122919192221919290900909000909000900911090909110909119110909000110909091919119000911119119191119"

private def label (s : Fin 4) (p : Fin 3) (e : Fin 40) : Nat :=
  if Active (coloring s) p e then
    (rawLabels.toList.getD ((s.val * 3 + p.val) * 40 + e.val) '9').toNat
  else 256 + e.val

private def mates : Fin 4 → Fin 3 → Fin 5 → Fin 5 :=
  ![![![4,2,1,3,0], ![1,0,2,4,3], ![0,1,3,2,4]],
    ![![4,2,1,3,0], ![1,0,2,4,3], ![0,1,3,2,4]],
    ![![4,2,1,3,0], ![0,3,2,1,4], ![2,1,0,4,3]],
    ![![4,2,1,3,0], ![0,3,2,1,4], ![4,1,3,2,0]]]

private theorem labels_constant : ∀ s p e f,
    LocalStep (coloring s) p e f → label s p e = label s p f := by
  unfold LocalStep
  intro s
  fin_cases s <;> decide +kernel

private theorem boundary_labels : ∀ s p i j,
    label s p (ports i) = label s p (ports j) ↔ i = j ∨ mates s p i = j := by
  decide +kernel

private theorem walks_checked : ∀ s p i,
    walkCheck ends (coloring s) p (ports i)
      (findWalk (coloring s) p none (ports i) (ports (mates s p i)) 40)
      (ports (mates s p i)) = true := by
  intro s
  fin_cases s <;> decide +kernel

/-- The displayed tables are proved equal to actual boundary connectivity. -/
theorem boundary_connected_iff (s : Fin 4) (p : Fin 3) (i j : Fin 5) :
    Connected (coloring s) p (ports i) (ports j) ↔ i = j ∨ mates s p i = j := by
  constructor
  · intro h
    exact (boundary_labels s p i j).mp
      (label_eq_of_connected (label s p) (labels_constant s p) h)
  · rintro (rfl | h)
    · exact Relation.EqvGen.refl _
    · rw [← h]
      exact connected_of_walk _ _ _ (walks_checked s p i)

def SameBoundaryData (c d : Fin 40 → Fin 3) : Prop :=
  boundary c = boundary d ∧ ∀ p i j,
    Connected c p (ports i) (ports j) ↔ Connected d p (ports i) (ports j)

theorem same_before : SameBoundaryData (coloring 0) (coloring 1) := by
  refine ⟨by decide +kernel, ?_⟩
  intro p i j
  rw [boundary_connected_iff, boundary_connected_iff]
  rfl

theorem common_region : ∀ s : Fin 2,
    Region ends (coloring (s.castAdd 2)) 0 regionMask := by
  intro s
  fin_cases s <;> decide +kernel

private theorem root_walks_checked : ∀ s : Fin 2, ∀ e, regionMask e = true →
    walkCheck ends (coloring (s.castAdd 2)) 0 (ports 0)
      (findWalk (coloring (s.castAdd 2)) 0 none (ports 0) e 40) e = true := by
  intro s
  fin_cases s <;> decide +kernel

/-- In both colourings the selected seven edges are exactly one physical
component, with the same boundary root, not an arbitrary component union. -/
theorem common_root_component (s : Fin 2) (e : Fin 40) :
    regionMask e = true ↔ Connected (coloring (s.castAdd 2)) 0 (ports 0) e := by
  constructor
  · intro he
    exact connected_of_walk _ _ _ (root_walks_checked s e he)
  · intro h
    have hlabel := label_eq_of_connected regionMask
      (fun a b hstep => (common_region s).2 a b hstep.1 hstep.2.1 hstep.2.2) h
    rw [← hlabel]
    decide

theorem different_after : ¬SameBoundaryData (coloring 2) (coloring 3) := by
  intro h
  have hfirst : Connected (coloring 2) 2 (ports 0) (ports 2) :=
    (boundary_connected_iff 2 2 0 2).mpr (Or.inr (by decide))
  have hsecond := (h.2 2 0 2).mp hfirst
  have hfalse := (boundary_connected_iff 3 2 0 2).mp hsecond
  exact (by decide : ¬((0 : Fin 5) = 2 ∨ mates 3 2 0 = 2)) hfalse

/-- The same component switch has different observations at identical
boundary data. Internal common-web attachments are essential. -/
theorem fixed_component_update_not_determined_by_boundary :
    ∃ c d : Fin 40 → Fin 3, Proper ends c ∧ Proper ends d ∧
      SameBoundaryData c d ∧ Region ends c 0 regionMask ∧ Region ends d 0 regionMask ∧
      (∀ e, regionMask e = true ↔ Connected c 0 (ports 0) e) ∧
      (∀ e, regionMask e = true ↔ Connected d 0 (ports 0) e) ∧
      ¬SameBoundaryData (PentagonKempePlateau.switch c 0 regionMask)
        (PentagonKempePlateau.switch d 0 regionMask) :=
  ⟨coloring 0, coloring 1, colorings_proper 0, colorings_proper 1,
    same_before, common_region 0, common_region 1,
    common_root_component 0, common_root_component 1, different_after⟩

end Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeMateDependence
