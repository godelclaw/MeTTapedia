import Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
import Mathlib.Tactic.FinCases

/-!
# A short extension can require more than one component switch

The old shore is the rectangle 0-1-4-3 of the triangular prism. Adding
0-2 and 1-2 attaches its adjacent triangle. The specified proper rectangle
colouring does not extend, even after any single physical Kempe component
switch. The statement uses literal edge incidence and quantifies over all
components of the existing Kempe operation. Two explicit component switches
do permit extension, so the obstruction is to a single-switch guarantee.
-/

namespace Mettapedia.GraphTheory.FourColor.ShortStepKempeCounterexample

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch

abbrev Vertex := Fin 6
abbrev Edge := Fin 9

/-- Edges 01, 02, 03, 12, 14, 25, 34, 35, 45 of the triangular prism. -/
def inc : Edge → Finset Vertex :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 4}, {2, 5}, {3, 4}, {3, 5}, {4, 5}]

def old : Finset Edge := {0, 2, 4, 6}
def enlarged : Finset Edge := {0, 1, 2, 3, 4, 6}
def assignment : Edge → Fin 3 := ![0, 0, 1, 0, 1, 0, 2, 0, 0]

theorem cubic_incidence :
    (∀ x : Edge, (inc x).card = 2) ∧
      ∀ v : Vertex, (Finset.univ.filter fun x => v ∈ inc x).card = 3 := by
  decide +kernel

theorem assignment_proper : Proper inc old assignment := by decide +kernel

def base : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3) :=
  colouring inc old assignment assignment_proper

theorem missing_first (q : Fin 3) : q ∉ profile inc old base 0 ↔ q = 2 := by
  revert q
  decide +kernel

theorem missing_last (q : Fin 3) : q ∉ profile inc old base 1 ↔ q = 2 := by
  revert q
  decide +kernel

def Extends (a : Edge → Fin 3) : Prop :=
  ∃ d : Edge → Fin 3, Proper inc enlarged d ∧ ∀ x ∈ old, d x = a x

/-- Both new edges would be forced to the same colour at their shared vertex. -/
theorem no_extension_of_equal_missing (a : Edge → Fin 3) (m : Fin 3)
    (hfirst : ∀ q, q ∉ profile inc old a 0 ↔ q = m)
    (hlast : ∀ q, q ∉ profile inc old a 1 ↔ q = m) : ¬ Extends a := by
  rintro ⟨d, hd, hda⟩
  have avoid (x : Edge) (hx : x ∈ enlarged) (hxold : x ∉ old)
      (v : Vertex) (hvx : v ∈ inc x) : d x ∉ profile inc old a v := by
    intro h
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hyold, hvy⟩ := Finset.mem_filter.mp hy
    have hy : y ∈ enlarged := (show old ⊆ enlarged by decide) hyold
    have hxy : x ≠ y := by rintro rfl; exact hxold hyold
    exact hd x hx y hy hxy ⟨v, Finset.mem_inter.mpr ⟨hvx, hvy⟩⟩
      ((hda y hyold).trans heq).symm
  have h1 : d 1 = m := (hfirst _).mp (avoid 1 (by decide) (by decide) 0 (by decide))
  have h3 : d 3 = m := (hlast _).mp (avoid 3 (by decide) (by decide) 1 (by decide))
  exact hd 1 (by decide) 3 (by decide) (by decide) ⟨2, by decide⟩ (h1.trans h3.symm)

theorem base_does_not_extend : ¬ Extends base :=
  no_extension_of_equal_missing base 2 missing_first missing_last

variable {r s : Fin 3} (K : (base.bicoloredSubgraph r s).ConnectedComponent)

private theorem contact_via_shared (hactive : base 0 = r ∨ base 0 = s) :
    Touches base r s K 0 ↔ Touches base r s K 1 := by
  constructor
  · intro h
    exact ⟨0, by decide, by decide,
      mem_component_of_touches base r s K h (by decide) (by decide) hactive⟩
  · intro h
    exact ⟨0, by decide, by decide,
      mem_component_of_touches base r s K h (by decide) (by decide) hactive⟩

private theorem contact_via_other_three
    (h2 : base 2 = r ∨ base 2 = s) (h6 : base 6 = r ∨ base 6 = s)
    (h4 : base 4 = r ∨ base 4 = s) :
    Touches base r s K 0 ↔ Touches base r s K 1 := by
  constructor
  · intro h
    have hx := mem_component_of_touches base r s K h (by decide : (2 : Edge) ∈ old)
      (by decide : (0 : Vertex) ∈ inc 2) h2
    have hm := base.mem_kempeComponentSet_of_adj hx (by decide :
      (IncidenceKempeSwitch.graph inc old).Adj 2 6) h6
    have hy := base.mem_kempeComponentSet_of_adj hm (by decide :
      (IncidenceKempeSwitch.graph inc old).Adj 6 4) h4
    exact ⟨4, by decide, by decide, hy⟩
  · intro h
    have hx := mem_component_of_touches base r s K h (by decide : (4 : Edge) ∈ old)
      (by decide : (1 : Vertex) ∈ inc 4) h4
    have hm := base.mem_kempeComponentSet_of_adj hx (by decide :
      (IncidenceKempeSwitch.graph inc old).Adj 4 6) h6
    have hy := base.mem_kempeComponentSet_of_adj hm (by decide :
      (IncidenceKempeSwitch.graph inc old).Adj 6 2) h2
    exact ⟨2, by decide, by decide, hy⟩

/-- Every nontrivial colour pair has the same component contact at both ends. -/
theorem same_contact (hne : r ≠ s) : Touches base r s K 0 ↔ Touches base r s K 1 := by
  fin_cases r <;> fin_cases s
  all_goals first
    | exact (hne rfl).elim
    | exact contact_via_shared K (by decide)
    | exact contact_via_other_three K (by decide) (by decide) (by decide)

/-- No pair and no single literal component repairs this proper old colouring. -/
theorem no_single_switch : ¬ Extends (base.swapOnKempeComponent r s K) := by
  classical
  have heq :
      (if Touches base r s K 1 then Equiv.swap r s 2 else 2) =
        (if Touches base r s K 0 then Equiv.swap r s 2 else 2) := by
    by_cases hsame : r = s
    · subst s
      simp
    · have hc := same_contact K hsame
      by_cases h : Touches base r s K 0
      · simp only [h, hc.mp h, ite_true]
      · have hl : ¬ Touches base r s K 1 := fun hh => h (hc.mpr hh)
        simp only [h, hl, ite_false]
  apply no_extension_of_equal_missing (base.swapOnKempeComponent r s K) _
    (missing_switch base r s K missing_first)
  intro q
  rw [missing_switch base r s K missing_last q, heq]

/-- The first switch changes edge 01 from colour 0 to colour 2. -/
def afterFirst : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3) :=
  colouring inc old ![2, 0, 1, 0, 1, 0, 2, 0, 0] (by decide +kernel)

/-- The second switch changes edge 03 from colour 1 to colour 0. -/
def afterSecond : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3) :=
  colouring inc old ![2, 0, 0, 0, 1, 0, 2, 0, 0] (by decide +kernel)

def firstComponent : (base.bicoloredSubgraph 0 2).ConnectedComponent :=
  (base.bicoloredSubgraph 0 2).connectedComponentMk ⟨0, Or.inl rfl⟩

def secondComponent : (afterFirst.bicoloredSubgraph 0 1).ConnectedComponent :=
  (afterFirst.bicoloredSubgraph 0 1).connectedComponentMk ⟨2, Or.inr rfl⟩

theorem first_step : afterFirst = base.swapOnKempeComponent 0 2 firstComponent := by
  have hiso : ∀ y : Edge, (IncidenceKempeSwitch.graph inc old).Adj 0 y →
      ¬ (base y = 0 ∨ base y = 2) := by decide +kernel
  apply DFunLike.ext
  intro x
  rw [show firstComponent =
    (base.bicoloredSubgraph 0 2).connectedComponentMk ⟨0, Or.inl rfl⟩ from rfl,
    switch_singleton_apply base 0 2 (Or.inl rfl) hiso]
  revert x
  decide +kernel

theorem second_step : afterSecond = afterFirst.swapOnKempeComponent 0 1 secondComponent := by
  have hiso : ∀ y : Edge, (IncidenceKempeSwitch.graph inc old).Adj 2 y →
      ¬ (afterFirst y = 0 ∨ afterFirst y = 1) := by decide +kernel
  apply DFunLike.ext
  intro x
  rw [show secondComponent =
    (afterFirst.bicoloredSubgraph 0 1).connectedComponentMk ⟨2, Or.inr rfl⟩ from rfl,
    switch_singleton_apply afterFirst 0 1 (Or.inr rfl) hiso]
  revert x
  decide +kernel

theorem afterSecond_extends : Extends afterSecond := by
  refine ⟨![2, 1, 0, 0, 1, 0, 2, 0, 0], ?_⟩
  decide +kernel

/-- A literal two-step Kempe sequence succeeds on the same old patch. -/
theorem two_switches_extend :
    ∃ K : (base.bicoloredSubgraph 0 2).ConnectedComponent,
      ∃ C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3),
        C = base.swapOnKempeComponent 0 2 K ∧
        ∃ L : (C.bicoloredSubgraph 0 1).ConnectedComponent, Extends (C.swapOnKempeComponent 0 1 L) := by
  refine ⟨firstComponent, afterFirst, first_step, secondComponent, ?_⟩
  rw [← second_step]
  exact afterSecond_extends

end Mettapedia.GraphTheory.FourColor.ShortStepKempeCounterexample
