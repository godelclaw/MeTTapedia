import MettapediaFourColor.CapRechoice
import Mettapedia.Cybernetics.DistinctionCalculus.PartitionedBoundary

/-!
# Exact boundary distinctions for colouring reconstruction

The d-calculus observer laws are applied to the actual D0099 source.
Its six evaluated elimination relations do not predict extension after an
accepted boundary update. The two-cap seam also fails to determine full
extension when hidden neighbour colours change. These failures force any
exact predictive refinement to distinguish the respective source inputs.

A positive interface retains neighbour colours by independently updated
region. Its update square closes for every finite history of colour maps
constant on each region. The common interior witness reconstructs a full
source colouring whenever the resulting boundary is proper.

The observer and grade definitions are reused from the MIT-licensed
MeTTapedia revision 3b432626d. D0099 provenance is inherited from
`TriangleStripAnchors`; its universal reducibility is not asserted here.
-/

namespace FourColor.BoundaryDistinction

open Color TriangleStripAnchors StripResponseSummary
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Cybernetics.DistinctionCalculus

set_option maxRecDepth 4096

def relationProfile (b : Boundary) : Fin 6 → Color → Color → Bool :=
  fun j a c => decide (relation b j a c)

def extensionAnswer (b : Boundary) : Bool := decide (∃ a c, r5 b a c)

/-- The Boolean observer is exactly the full source-extension question. -/
theorem answer_extension_iff (b : Boundary) (proper : StripSourceExtension.ProperBoundary b) :
    extensionAnswer b = true ↔
      ∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = b i := by
  rw [extensionAnswer, decide_eq_true_eq, terminal_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨StripSourceExtension.colouring b f proper hf, StripSourceExtension.colour_port b f⟩
  · rintro ⟨k, hk⟩
    exact ⟨_, valid_of_colouring b k hk⟩

/-- Exact colour relations are presently equal; the same allowed update
separates their full-extension answers. -/
def snapshotFiber : NonTrivialFiber relationProfile
    (fun b => extensionAnswer (update b)) where
  left := boundary false
  right := boundary true
  sameShadow := by
    funext j a c
    simp only [relationProfile, equal_relations]
  differentValue := by decide +kernel

theorem no_snapshot_prediction :
    ¬ Factors relationProfile (fun b => extensionAnswer (update b)) :=
  snapshotFiber.not_factors

/-- Any refined report that predicts the next answer must separate these
actual source inputs, regardless of the refinement's representation. -/
theorem predictive_refinement_separates {R : Type*} (report : Boundary → R)
    (predicts : Factors report (fun b => extensionAnswer (update b))) :
    report (boundary false) ≠ report (boundary true) := by
  intro same
  exact snapshotFiber.differentValue (predicts.constantOnFibers _ _ same)

noncomputable def snapshotObserver : Tolerance Boundary := by
  classical
  exact Tolerance.ofReport relationProfile

noncomputable def answerObserver : Tolerance Boundary :=
  Tolerance.ofReport extensionAnswer

/-- A predictive comparison from the evaluated snapshot needs the full unit
defect: no positive preservation grade certifies this update. -/
theorem snapshot_defect_lower_bound (δ : ℚ)
    (bound : Tolerance.ExpandsAtMost snapshotObserver answerObserver update δ) :
    1 ≤ δ := by
  classical
  have h := bound snapshotFiber.left snapshotFiber.right
  have same := snapshotFiber.sameShadow
  have different := snapshotFiber.differentValue
  simpa [snapshotObserver, answerObserver, Tolerance.distance, Tolerance.ofReport,
    same, different] using h

def seam (s : Bool) : List Color := CapRechoice.diamondBoundary.map (CapRechoice.selected s)

def capAnswer (s : Bool) : Bool := extensionAnswer (CapRechoice.outer s)

/-- The seam identifies two actual retained-source colourings with distinct
full-extension answers. -/
def seamFiber : NonTrivialFiber seam capAnswer where
  left := false
  right := true
  sameShadow := CapRechoice.same_visible_boundary
  differentValue := by
    intro same
    have repaired : capAnswer true = true :=
      (answer_extension_iff (CapRechoice.outer true) (by decide +kernel)).mpr
        ⟨CapRechoice.repaired, CapRechoice.repaired_outer⟩
    exact CapRechoice.no_initial_extension
      ((answer_extension_iff (CapRechoice.outer false) (by decide +kernel)).mp
        (same.trans repaired))

theorem no_seam_prediction : ¬ Factors seam capAnswer := seamFiber.not_factors

theorem seam_refinement_separates {R : Type*} (report : Bool → R)
    (predicts : Factors report capAnswer) : report false ≠ report true := by
  intro same
  exact seamFiber.differentValue (predicts.constantOnFibers _ _ same)

/-- The fixed interval used in the source update is one independent region;
its complement is the other. -/
def region (i : Fin 11) : Bool := decide (2 ≤ i.val ∧ i.val ≤ 9)

def neighbours (v : Fin 8) : Set (Fin 11) := {i | i ∈ attachments v}

def coreProfile (b : Boundary) : PartitionedBoundary.Profile (Fin 8) Bool Color :=
  PartitionedBoundary.observe neighbours region b

def regionMaps (inside : Bool) (a : Color) : Color := if inside then c3 + a else a

theorem change_eq_update (b : Boundary) :
    PartitionedBoundary.change region regionMaps b = update b := by
  funext i
  simp [PartitionedBoundary.change, region, regionMaps, update]

/-- Region-labelled neighbour sets predict the same actual boundary update. -/
theorem profile_update (b : Boundary) :
    coreProfile (update b) = PartitionedBoundary.transport regionMaps (coreProfile b) := by
  rw [← change_eq_update]
  exact PartitionedBoundary.observe_change neighbours region regionMaps b

/-- This refinement detects the hidden neighbour colour in the snapshot
counterexample; source vertex 16 has boundary neighbours 1, 2 and 3. -/
theorem profile_separates : coreProfile (boundary false) ≠ coreProfile (boundary true) := by
  have left : c0 ∈ coreProfile (boundary false) 5 true := by
    change ∃ i : Fin 11, i ∈ attachments 5 ∧ region i = true ∧ boundary false i = c0
    decide +kernel
  have right : c0 ∉ coreProfile (boundary true) 5 true := by
    change ¬ ∃ i : Fin 11, i ∈ attachments 5 ∧ region i = true ∧ boundary true i = c0
    decide +kernel
  intro same
  rw [same] at left
  exact right left

def internal (f : Fin 8 → Color) : Prop := ∀ e ∈ edges, f e.1 ≠ f e.2

/-- A completed profile means one genuine interior witness, not separate
marginal colour choices. -/
theorem source_extension_iff {K : Type*} (zones : Fin 11 → K) (b : Boundary)
    (proper : StripSourceExtension.ProperBoundary b) :
    (∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = b i) ↔
      PartitionedBoundary.Complete internal (PartitionedBoundary.observe neighbours zones b) := by
  constructor
  · rintro ⟨k, hk⟩
    have valid := valid_of_colouring b k hk
    apply (PartitionedBoundary.complete_observe internal neighbours zones b).mpr
    exact ⟨fun v => k (vertex0099 v), valid.2, valid.1⟩
  · intro completed
    obtain ⟨f, hf, hu⟩ :=
      (PartitionedBoundary.complete_observe internal neighbours zones b).mp completed
    have valid : ValidCore b f := ⟨hu, hf⟩
    exact ⟨StripSourceExtension.colouring b f proper valid,
      StripSourceExtension.colour_port b f⟩

theorem profile_extension_iff (b : Boundary) (proper : StripSourceExtension.ProperBoundary b) :
    (∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = b i) ↔
      PartitionedBoundary.Complete internal (coreProfile b) :=
  source_extension_iff region b proper

/-- Full source reconstruction follows after every finite history admitted
by this partition, subject to the actual proper-boundary hypothesis. -/
theorem history_extension_iff (b : Boundary) (maps : List (Bool → Color → Color))
    (proper : StripSourceExtension.ProperBoundary (PartitionedBoundary.run region maps b)) :
    (∃ k : input0099.graph.Coloring Color,
      ∀ i, k (port i) = PartitionedBoundary.run region maps b i) ↔
      PartitionedBoundary.Complete internal
        (PartitionedBoundary.runProfile maps (coreProfile b)) := by
  have h := profile_extension_iff (PartitionedBoundary.run region maps b) proper
  simpa only [coreProfile, PartitionedBoundary.observe_run] using h

/-- The same observer has zero update defect on the stated operation domain. -/
theorem profile_grade_zero (maps : Bool → Color → Color) :
    Tolerance.ExpandsAtMost (PartitionedBoundary.observer neighbours region)
      (PartitionedBoundary.observer neighbours region)
      (PartitionedBoundary.change region maps) 0 :=
  PartitionedBoundary.grade_zero neighbours region maps

/-- The two actual source updates share three inhabited regions. -/
def commonRegion (i : Fin 11) : Bool × Bool := (region i, decide (i = 5))

def commonProfile (b : Boundary) : PartitionedBoundary.Profile (Fin 8) (Bool × Bool) Color :=
  PartitionedBoundary.observe neighbours commonRegion b

theorem common_forgets_to_interval (b : Boundary) :
    PartitionedBoundary.coarsen Prod.fst (commonProfile b) = coreProfile b :=
  (PartitionedBoundary.common_refinement neighbours region (fun i => decide (i = 5)) b).1

theorem common_interval_update (b : Boundary) :
    PartitionedBoundary.change commonRegion (fun k => regionMaps k.1) b = update b := by
  exact change_eq_update b

/-- The same interface admits the second original matching's single hidden
vertex exchange, which frees a different cap witness. -/
theorem common_cap_update :
    PartitionedBoundary.change commonRegion
      (fun k a => if k.2 then c3 + a else a) (CapRechoice.outer false) =
        CapRechoice.outer true := by
  funext i
  change (if decide (i = 5) then c3 + CapRechoice.outer false i
    else CapRechoice.outer false i) = CapRechoice.outer true i
  revert i
  decide +kernel

/-- Both updates and every admitted composition use this one exact source
interface. Properness and a joint interior witness remain explicit. -/
theorem common_history_extension_iff (b : Boundary)
    (maps : List ((Bool × Bool) → Color → Color))
    (proper : StripSourceExtension.ProperBoundary (PartitionedBoundary.run commonRegion maps b)) :
    (∃ k : input0099.graph.Coloring Color,
      ∀ i, k (port i) = PartitionedBoundary.run commonRegion maps b i) ↔
      PartitionedBoundary.Complete internal
        (PartitionedBoundary.runProfile maps (commonProfile b)) := by
  have h := source_extension_iff commonRegion (PartitionedBoundary.run commonRegion maps b) proper
  simpa only [commonProfile, PartitionedBoundary.observe_run] using h

end FourColor.BoundaryDistinction
