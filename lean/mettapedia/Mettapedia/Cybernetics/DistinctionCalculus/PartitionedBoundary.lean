import Mettapedia.Cybernetics.DistinctionCalculus.PreservationGrade
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Boundary observations that retain independently updated regions

For each interior vertex and update region, the report keeps the set of
colours used by neighbours in that region. An update applies one colour map
per region. The observed update is exactly the image of each retained set.
This law is uniform in the boundary and interior carriers.

The common interior colouring remains one joint witness. Forgetting the
region labels before an update need not preserve that witness's existence.
The Four Colour consumer uses the decoded D0099 graph.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus.PartitionedBoundary

open Mettapedia.GSLT.Core.NonFactorization

universe uB uV uK uL uC

variable {B : Type uB} {V : Type uV} {K : Type uK} {L : Type uL} {C : Type uC}

abbrev Profile (V : Type uV) (K : Type uK) (C : Type uC) := V → K → Set C

/-- Neighbour colours are recorded separately for each update region. -/
def observe (neighbours : V → Set B) (region : B → K) (colour : B → C) :
    Profile V K C :=
  fun v k => {a | ∃ i, i ∈ neighbours v ∧ region i = k ∧ colour i = a}

/-- Each region has one colour map; injectivity is unnecessary for the
observation law. A colouring consumer may require stronger hypotheses. -/
def change (region : B → K) (maps : K → C → C) (colour : B → C) : B → C :=
  fun i => maps (region i) (colour i)

def transport (maps : K → C → C) (p : Profile V K C) : Profile V K C :=
  fun v k => maps k '' p v k

/-- The update square closes at every boundary width. -/
theorem observe_change (neighbours : V → Set B) (region : B → K)
    (maps : K → C → C) (colour : B → C) :
    observe neighbours region (change region maps colour) =
      transport maps (observe neighbours region colour) := by
  funext v k
  apply Set.ext
  intro a
  constructor
  · rintro ⟨i, hi, hk, ha⟩
    exact ⟨colour i, ⟨i, hi, hk, rfl⟩, by simpa [change, hk] using ha⟩
  · rintro ⟨b, ⟨i, hi, hk, hb⟩, ha⟩
    exact ⟨i, hi, hk, by simpa [change, hk, hb] using ha⟩

/-- The exact abstraction uses the same per-region image operation. -/
theorem update_factors (neighbours : V → Set B) (region : B → K)
    (maps : K → C → C) :
    Factors (observe neighbours region)
      (fun colour => observe neighbours region (change region maps colour)) :=
  ⟨transport maps, fun colour => (observe_change neighbours region maps colour).symm⟩

/-- Observed updates compose in the same order as actual updates. -/
theorem transport_comp (first second : K → C → C) (p : Profile V K C) :
    transport second (transport first p) =
      transport (fun k => second k ∘ first k) p := by
  funext v k
  exact Set.image_image _ _ _

/-- Forget a region distinction by taking the union of its retained sets. -/
def coarsen (projection : K → L) (p : Profile V K C) : Profile V L C :=
  fun v l => {a | ∃ k, projection k = l ∧ a ∈ p v k}

theorem observe_coarsen (neighbours : V → Set B) (region : B → K)
    (projection : K → L) (colour : B → C) :
    coarsen projection (observe neighbours region colour) =
      observe neighbours (projection ∘ region) colour := by
  funext v l
  apply Set.ext
  intro a
  constructor
  · rintro ⟨k, hk, i, hi, hic, ha⟩
    exact ⟨i, hi, by simp only [Function.comp_apply, hic, hk], ha⟩
  · rintro ⟨i, hi, hk, ha⟩
    exact ⟨region i, hk, i, hi, rfl, ha⟩

/-- Coarsening commutes with an update that acts uniformly on each coarse
region; the hidden fine regions still share the same colour map. -/
theorem coarsen_transport (projection : K → L) (maps : L → C → C)
    (p : Profile V K C) :
    transport maps (coarsen projection p) =
      coarsen projection (transport (fun k => maps (projection k)) p) := by
  funext v l
  apply Set.ext
  intro a
  constructor
  · rintro ⟨b, ⟨k, hk, hb⟩, ha⟩
    exact ⟨k, hk, b, hb, by simpa only [hk] using ha⟩
  · rintro ⟨k, hk, b, hb, ha⟩
    exact ⟨b, ⟨k, hk, hb⟩, by simpa only [hk] using ha⟩

/-- One common refinement retains either of two update partitions. -/
theorem common_refinement (neighbours : V → Set B) (first : B → K)
    (second : B → L) (colour : B → C) :
    coarsen Prod.fst (observe neighbours (fun i => (first i, second i)) colour) =
        observe neighbours first colour ∧
      coarsen Prod.snd (observe neighbours (fun i => (first i, second i)) colour) =
        observe neighbours second colour :=
  ⟨observe_coarsen neighbours _ Prod.fst colour,
    observe_coarsen neighbours _ Prod.snd colour⟩

def run (region : B → K) : List (K → C → C) → (B → C) → B → C
  | [], colour => colour
  | maps :: rest, colour => run region rest (change region maps colour)

def runProfile : List (K → C → C) → Profile V K C → Profile V K C
  | [], p => p
  | maps :: rest, p => runProfile rest (transport maps p)

/-- Any finite history of the admitted operations has the exact same
retained observation, with no new approximation defect. -/
theorem observe_run (neighbours : V → Set B) (region : B → K)
    (maps : List (K → C → C)) (colour : B → C) :
    observe neighbours region (run region maps colour) =
      runProfile maps (observe neighbours region colour) := by
  induction maps generalizing colour with
  | nil => rfl
  | cons maps rest ih =>
    change observe neighbours region (run region rest (change region maps colour)) = _
    rw [ih, observe_change]
    rfl

/-- A candidate interior colour avoids every retained neighbour colour. -/
def Allows (p : Profile V K C) (v : V) (a : C) : Prop :=
  ∀ k b, b ∈ p v k → a ≠ b

theorem allows_observe (neighbours : V → Set B) (region : B → K)
    (colour : B → C) (v : V) (a : C) :
    Allows (observe neighbours region colour) v a ↔
      ∀ i ∈ neighbours v, a ≠ colour i := by
  constructor
  · intro h i hi
    exact h (region i) (colour i) ⟨i, hi, rfl, rfl⟩
  · rintro h k b ⟨i, hi, _, rfl⟩
    exact h i hi

/-- All constraints share one actual interior witness. -/
def Complete (internal : (V → C) → Prop) (p : Profile V K C) : Prop :=
  ∃ f, internal f ∧ ∀ v, Allows p v (f v)

theorem complete_observe (internal : (V → C) → Prop) (neighbours : V → Set B)
    (region : B → K) (colour : B → C) :
    Complete internal (observe neighbours region colour) ↔
      ∃ f, internal f ∧ ∀ v i, i ∈ neighbours v → f v ≠ colour i := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun v => (allows_observe neighbours region colour v (f v)).mp (h v)⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun v => (allows_observe neighbours region colour v (f v)).mpr (h v)⟩

/-- The crisp d-calculus observer measures equality of these reports. -/
noncomputable def observer (neighbours : V → Set B) (region : B → K) :
    Tolerance (B → C) := by
  classical
  exact Tolerance.ofReport (observe neighbours region)

/-- Region-preserving changes cannot separate states identified by this
observer: their one-sided preservation defect is zero. -/
theorem grade_zero (neighbours : V → Set B) (region : B → K) (maps : K → C → C) :
    Tolerance.ExpandsAtMost (observer neighbours region) (observer neighbours region)
      (change region maps) 0 := by
  classical
  intro x y
  by_cases same : observe neighbours region x = observe neighbours region y
  · have changed : observe neighbours region (change region maps x) =
        observe neighbours region (change region maps y) := by
      rw [observe_change, observe_change, same]
    simp [observer, Tolerance.distance, Tolerance.ofReport, same, changed]
  · have original : (observer neighbours region).distance x y = 1 := by
      simp [observer, Tolerance.distance, Tolerance.ofReport, same]
    simpa only [original, add_zero] using
      (observer neighbours region).distance_bounded (change region maps x) (change region maps y)

end Mettapedia.Cybernetics.DistinctionCalculus.PartitionedBoundary
