import MettapediaFourColor.CoreProfileSwitchGeometry
import Mettapedia.GraphTheory.Kempe.Symm
import Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation

/-! # Equal core lists need not preserve a rooted Kempe switch

Two proper colourings of the same planar exterior induce identical allowed
colours at all seven core vertices. Their joint core-assignment relations
therefore agree. Swapping colours 0 and 3 on the component of boundary vertex
2 gives an extendible colouring in one case and a nonextendible colouring in
the other. Static extension information does not determine this operation.

The counterexample concerns this summary and this fixed operation. It does
not rule out a richer compositional interface or a different repair choice.
-/

namespace FourColor.CoreProfileSwitchObstruction

open SimpleGraph CoreProfileSwitchGeometry

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

abbrev Palette := Fin 4
abbrev Boundary := Fin 11 → Palette
abbrev Profile := Fin 7 → Palette → Prop

def word (b : Bool) : Boundary :=
  if b then ![0,1,0,2,1,3,1,2,3,2,1] else ![0,1,0,2,3,1,3,2,3,2,1]

def afterWord (b : Bool) : Boundary :=
  if b then ![0,1,3,2,1,3,1,2,3,2,1] else ![0,1,3,2,0,1,3,2,3,2,1]

theorem proper : ∀ b u v, exterior.Adj u v → word b u ≠ word b v := by decide +kernel

def initial (b : Bool) : exterior.Coloring Palette := .mk (word b) (proper b _ _)

def coreVertex (u : Fin 7) : Fin 18 := ⟨11 + u.val, by omega⟩

def profile (w : Boundary) : Profile := fun u c =>
  ∀ j : Fin 11, graph.Adj (coreVertex u) (j.castAdd 7) → c ≠ w j

instance (w u c) : Decidable (profile w u c) := inferInstanceAs (Decidable (∀ _, _))

/-- The lists use exactly the core-to-boundary incidences of the pinned source. -/
theorem profile_source (w : Boundary) (u : Fin 7) (c : Palette) :
    profile w u c ↔ ∀ j : Fin 11,
      FiveTriangleCollapseObstruction.upper.graph.Adj (coreVertex u) (j.castAdd 7) →
        c ≠ w j := by
  have h : ∀ u : Fin 7, ∀ j : Fin 11,
      graph.Adj (coreVertex u) (j.castAdd 7) ↔
      FiveTriangleCollapseObstruction.upper.graph.Adj (coreVertex u) (j.castAdd 7) := by
    decide +kernel
  simp only [profile, h]

def CoreRelation (w : Boundary) (k : Fin 7 → Palette) : Prop :=
  (∀ u v, graph.Adj (coreVertex u) (coreVertex v) → k u ≠ k v) ∧
    ∀ u, profile w u (k u)

theorem same_profile : profile (word false) = profile (word true) := by
  have h : ∀ u c, profile (word false) u c ↔ profile (word true) u c := by decide +kernel
  exact funext fun u => funext fun c => propext (h u c)

/-- The whole joint internal relation agrees, not just its marginals. -/
theorem same_joint_relation : CoreRelation (word false) = CoreRelation (word true) := by
  funext k
  apply propext
  simp only [CoreRelation, same_profile]

def Extends (w : Boundary) : Prop :=
  ∃ K : graph.Coloring Palette, ∀ j : Fin 11, K (j.castAdd 7) = w j

/-- Any genuine extension supplies the joint internal witness. -/
theorem relation_of_extension {w : Boundary} (h : Extends w) :
    ∃ k, CoreRelation w k := by
  obtain ⟨K, fixed⟩ := h
  refine ⟨fun u => K (coreVertex u), ⟨fun _ _ e => K.valid e, ?_⟩⟩
  intro u j e
  rw [← fixed j]
  exact K.valid e

/-- A joint witness reconstructs the whole graph when the exterior is proper. -/
def reconstruct (C : exterior.Coloring Palette) (k : Fin 7 → Palette)
    (h : CoreRelation (fun j => C j) k) : graph.Coloring Palette :=
  .mk (Fin.addCases (motive := fun _ : Fin (11 + 7) => Palette) (fun j => C j) k) (by
    intro u v
    refine Fin.addCases (m := 11) (n := 7) (fun i => ?_) (fun i => ?_) u
    · refine Fin.addCases (m := 11) (n := 7) (fun j => ?_) (fun j => ?_) v
      · intro e
        simpa using C.valid e
      · intro e
        simpa [coreVertex] using (h.2 j i e.symm).symm
    · refine Fin.addCases (m := 11) (n := 7) (fun j => ?_) (fun j => ?_) v
      · intro e
        simpa [coreVertex] using h.2 i j e
      · intro e
        simpa [coreVertex] using h.1 i j e)

theorem extension_iff_relation (C : exterior.Coloring Palette) :
    Extends (fun j => C j) ↔ ∃ k, CoreRelation (fun j => C j) k := by
  constructor
  · exact relation_of_extension
  · rintro ⟨k, h⟩
    refine ⟨reconstruct C k h, fun j => ?_⟩
    change Fin.addCases (motive := fun _ : Fin (11 + 7) => Palette) (fun j => C j) k (j.castAdd 7) = C j
    simp

/-- Exact forbidden colours at two adjacent core vertices give a short
nonextension proof for both initial words and the second switched word. -/
theorem forced_zero : ∀ (b : Bool) (c : Palette),
    (profile (word b) 1 c → c = 0) ∧ (profile (word b) 2 c → c = 0) := by
  decide +kernel

theorem initial_nonextension (b : Bool) : ¬ Extends (word b) := by
  intro h
  obtain ⟨k, edges, lists⟩ := relation_of_extension h
  have h1 := (forced_zero b (k 1)).1 (lists 1)
  have h2 := (forced_zero b (k 2)).2 (lists 2)
  exact edges 1 2 (by decide +kernel) (h1.trans h2.symm)

def componentVertices (b : Bool) : Set (Fin 11) :=
  {v | v = 2 ∨ (b = false ∧ v = 4)}

instance (b : Bool) (v : Fin 11) : Decidable (v ∈ componentVertices b) :=
  inferInstanceAs (Decidable (v = 2 ∨ (b = false ∧ v = 4)))

theorem root_active (b : Bool) : (2 : Fin 11) ∈ (initial b).bicoloredSet 0 3 := by
  cases b <;> exact Or.inl rfl

def component (b : Bool) : ((initial b).bicoloredSubgraph 0 3).ConnectedComponent :=
  ((initial b).bicoloredSubgraph 0 3).connectedComponentMk ⟨2, root_active b⟩

/-- This computes physical connected components in the same exterior graph. -/
theorem actual_component (b : Bool) :
    (initial b).kempeComponentSet 0 3 (component b) = componentVertices b := by
  apply Set.Subset.antisymm
  · apply (initial b).kempeComponentSet_subset_of_closed (root_active b) (Or.inl rfl)
    have closed : ∀ b u v, u ∈ componentVertices b → exterior.Adj u v →
        (word b v = 0 ∨ word b v = 3) → v ∈ componentVertices b := by decide +kernel
    exact closed b
  · intro v hv
    have root : (2 : Fin 11) ∈ (initial b).kempeComponentSet 0 3 (component b) :=
      (initial b).mem_kempeComponentSet_self (root_active b)
    rcases hv with rfl | ⟨rfl, rfl⟩
    · exact root
    · apply (initial false).mem_kempeComponentSet_of_adj root
      · decide +kernel
      · exact Or.inr rfl

noncomputable def switched (b : Bool) : exterior.Coloring Palette :=
  (initial b).swapOnKempeComponent 0 3 (component b)

theorem physical_step (b : Bool) : exterior.KempeStep (initial b) (switched b) :=
  kempeStep_swapOnKempeComponent _ _ _ _

theorem switched_word (b : Bool) (v : Fin 11) : switched b v = afterWord b v := by
  have finite : ∀ b v,
      (if v ∈ componentVertices b then Equiv.swap (0 : Palette) 3 (word b v)
       else word b v) = afterWord b v := by decide +kernel
  by_cases hv : v ∈ componentVertices b
  · have hm : v ∈ (initial b).kempeComponentSet 0 3 (component b) := by
      rw [actual_component]; exact hv
    rw [switched, Coloring.swapOnKempeComponent_apply_of_mem _ hm]
    exact (ite_eq_left hv).symm.trans (finite b v)
  · have hm : v ∉ (initial b).kempeComponentSet 0 3 (component b) := by
      rw [actual_component]; exact hv
    rw [switched, Coloring.swapOnKempeComponent_apply_of_not_mem _ hm]
    exact (ite_eq_right hv).symm.trans (finite b v)

def repairedWord : Fin 18 → Palette := ![0,1,3,2,0,1,3,2,3,2,1,2,3,0,1,0,0,3]

def repaired : graph.Coloring Palette := .mk repairedWord (by decide +kernel)

theorem first_extends : Extends (afterWord false) :=
  ⟨repaired, by decide +kernel⟩

theorem second_nonextension : ¬ Extends (afterWord true) := by
  have forced : ∀ c : Palette,
      (profile (afterWord true) 1 c → c = 0) ∧
      (profile (afterWord true) 2 c → c = 0) := by decide +kernel
  intro h
  obtain ⟨k, edges, lists⟩ := relation_of_extension h
  exact edges 1 2 (by decide +kernel)
    (((forced (k 1)).1 (lists 1)).trans ((forced (k 2)).2 (lists 2)).symm)

theorem different_outcomes :
    Extends (fun v => switched false v) ∧ ¬ Extends (fun v => switched true v) := by
  simpa only [switched_word] using And.intro first_extends second_nonextension

theorem different_profiles : profile (afterWord false) ≠ profile (afterWord true) := by
  intro h
  have absent : ¬ profile (afterWord false) 1 0 := by decide +kernel
  have present : profile (afterWord true) 1 0 := by decide +kernel
  rw [h] at absent
  exact absent present

/-- The fixed rooted switch does not descend to the core-list quotient. -/
theorem no_profile_update : ¬ ∃ update : Profile → Profile,
    ∀ b, update (profile (word b)) = profile (fun v => switched b v) := by
  rintro ⟨update, correct⟩
  have h := congrArg update same_profile
  rw [correct false, correct true] at h
  exact different_profiles (by simpa only [switched_word] using h)

/-- No predicate of the initial core profile alone predicts extension after
this same rooted physical switch, even on these two colourings. -/
theorem no_profile_prediction : ¬ ∃ predict : Profile → Prop,
    ∀ b, predict (profile (word b)) ↔ Extends (fun v => switched b v) := by
  rintro ⟨predict, correct⟩
  have h := (correct false).mpr different_outcomes.1
  rw [same_profile] at h
  exact different_outcomes.2 ((correct true).mp h)

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation

def observe (C : exterior.Coloring Palette) : Profile := profile (fun j => C j)

theorem rooted_switch_initial (b : Bool) : rootedSwitch (initial b) 0 3 2 = switched b := by
  rw [rootedSwitch, dite_eq_left (root_active b)]
  rfl

/-- The source example consumes the common GSLT nonfactorization criterion. -/
theorem no_deterministic_quotient :
    ¬ Factors observe (fun C => observe (rootedSwitch C 0 3 2)) := by
  apply NonTrivialFiber.not_factors
  refine ⟨initial false, initial true, same_profile, ?_⟩
  simpa only [rooted_switch_initial, observe, switched_word] using different_profiles

/-- The obstruction is realized on the induced exterior of a connected
spherical triangulation with the full source reading. -/
theorem planar_counterexample :
    (SimpleGraphBridge.rotationHypermap rotation).Planar ∧
    graph.Connected ∧ ExceptionalOverlap.Triangular rotation ∧
    Nonempty (ThreeBlockDiskBoundary.Reading rotation) ∧
    Nonempty (exterior ≃g graph.induce (ThreeBlockDiskBoundary.keep reading)) ∧
    profile (word false) = profile (word true) ∧
    (∀ b, ¬ Extends (word b)) ∧
    (∀ b, exterior.KempeStep (initial b) (switched b)) ∧
    Extends (fun v => switched false v) ∧ ¬ Extends (fun v => switched true v) :=
  ⟨planar, connected, triangular, ⟨reading⟩, ⟨exteriorIso⟩, same_profile,
    initial_nonextension, physical_step, different_outcomes⟩

end FourColor.CoreProfileSwitchObstruction
