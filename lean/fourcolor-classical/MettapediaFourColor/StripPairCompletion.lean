import MettapediaFourColor.AlternatingPairRepair
import MettapediaFourColor.StripFanProgram

/-!
# The adjacent closing law reconstructs the complete source

The six-stage construction has two remaining adjacent vertices. The
majority law fills both when its eight-port trace has the stated pattern.
All existing interior and exterior vertices may be recoloured together.
The trace guard is an explicit remaining supply obligation.
-/

namespace FourColor.StripPairCompletion

open Color KempeBoundarySplit StripResponseSummary StripSourceExtension
open TriangleStripAnchors StripFanProgram

variable {V : Type*} (H : SimpleGraph V) (p : Fin 11 → V)

abbrev Carrier (V : Type*) := Option (Option (Option (Option (Option (Option (V))))))
def old (v : V) : Carrier V := some (some (some (some (some (some (v))))))
def core : Fin 8 → Carrier V := ![some (some (some (some (some (none))))),some (some (some (none))),none,some (some (some (some (none)))),none,some (none),none,some (some (none))]
def ports : Fin 8 → Carrier V :=
  ![old (p 9), core 6, core 5, old (p 3), old (p 4), core 3, core 1, old (p 8)]

theorem ordered : List.ofFn (ports p) = ring6 p := by
  simp [ports,ring6,core,old,List.ofFn_succ]

def restrict (D : (graph6 H p).Coloring Color) : H.Coloring Color :=
  .mk (fun v => D (old v)) (fun h => D.valid h)

@[simp] theorem restrict_apply (D : (graph6 H p).Coloring Color) (v : V) :
    restrict H p D v = D (old v) := rfl

def values (D : (graph6 H p).Coloring Color) (x y : Color) (v : Fin 8) : Color :=
  if v = 2 then y else if v = 4 then x else D (core v)

theorem attachment_adj : ∀ (v : Fin 8) (i : Fin 11), v ≠ 2 → v ≠ 4 →
    i ∈ attachments v → (graph6 H p).Adj (core v) (old (p i)) := by
  intro v i h2 h4 hi
  fin_cases v <;> fin_cases i <;> simp [attachments] at h2 h4 hi
  all_goals simp [graph1,graph2,graph3,graph4,graph5,graph6,core,old,
    BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]

theorem core_adj : ∀ e ∈ edges, e.1 ≠ 2 → e.1 ≠ 4 → e.2 ≠ 2 → e.2 ≠ 4 →
    (graph6 H p).Adj (core e.1) (core e.2) := by
  intro e he
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [graph1,graph2,graph3,graph4,graph5,graph6,core,
    BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]

/-- Both new colours satisfy every source edge, including their shared edge. -/
theorem valid (D : (graph6 H p).Coloring Color) (x y : Color)
    (fit : AlternatingPairRepair.Fits (fun i => D (ports p i)) x y) :
    ValidCore (fun i => restrict H p D (p i)) (values H p D x y) := by
  rcases fit with ⟨x6,x7,x0,x1,yx,hy⟩
  constructor
  · intro v i hi
    by_cases h2 : v = 2
    · subst v
      have eq : i = 3 ∨ i = 4 := by simpa [attachments] using hi
      rcases eq with rfl | rfl
      · simpa [values,ports] using hy 2
      · simpa [values,ports] using hy 3
    by_cases h4 : v = 4
    · subst v
      have eq : i = 8 ∨ i = 9 := by simpa [attachments] using hi
      rcases eq with rfl | rfl
      · simpa [values,ports] using x7
      · simpa [values,ports] using x0
    simpa [values,h2,h4] using
      D.valid (attachment_adj H p v i h2 h4 hi)
  · intro e he
    simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [values] using D.valid (core_adj H p (0,1)
        (by decide +kernel) (by decide) (by decide) (by decide) (by decide))
    · simpa [values] using D.valid (core_adj H p (0,3)
        (by decide +kernel) (by decide) (by decide) (by decide) (by decide))
    · simpa [values,ports] using (hy 5).symm
    · simpa [values] using D.valid (core_adj H p (1,3)
        (by decide +kernel) (by decide) (by decide) (by decide) (by decide))
    · simpa [values,ports] using x6.symm
    · simpa [values,ports] using hy 4
    · simpa [values,ports] using yx
    · simpa [values,ports] using hy 1
    · simpa [values,ports] using hy 0
    · simpa [values,ports] using x1
    · simpa [values] using D.valid (core_adj H p (5,6)
        (by decide +kernel) (by decide) (by decide) (by decide) (by decide))
    · simpa [values] using D.valid (core_adj H p (5,7)
        (by decide +kernel) (by decide) (by decide) (by decide) (by decide))
    · simpa [values] using D.valid (core_adj H p (6,7)
        (by decide +kernel) (by decide) (by decide) (by decide) (by decide))

/-- The source colouring agrees with the changed exterior at every port. -/
theorem reconstruct
    (embedding : ∀ i j, input0099.graph.Adj (port i) (port j) → H.Adj (p i) (p j))
    (D : (graph6 H p).Coloring Color) (x y : Color)
    (fit : AlternatingPairRepair.Fits (fun i => D (ports p i)) x y) :
    ∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = restrict H p D (p i) := by
  let b : Boundary := fun i => restrict H p D (p i)
  have proper : ProperBoundary b := fun i j edge => (restrict H p D).valid (embedding i j edge)
  exact ⟨colouring b (values H p D x y) proper (valid H p D x y fit),
    fun i => colour_port b (values H p D x y) i⟩

/-- The entire source is restored under the explicit intermediate trace guard.
The initial Kempe closure is preserved through the six earlier insertions. -/
theorem from_program
    (embedding : ∀ i j, input0099.graph.Adj (port i) (port j) → H.Adj (p i) (p j))
    (initial : KempeClosed (GraphTrace H (ring0 p)))
    (g : EdgePerm)
    (guard : GraphTrace (graph6 H p) (ring6 p) ((List.ofFn AlternatingPairRepair.word).map g)) :
    ∃ E : H.Coloring Color, ∃ k : input0099.graph.Coloring Color,
      ∀ i, k (port i) = E (p i) := by
  have closed : KempeClosed (GraphTrace (graph6 H p) (List.ofFn (ports p))) := by
    rw [ordered]
    exact closed6 H p embedding initial
  have start : GraphTrace (graph6 H p) (List.ofFn (ports p))
      ((List.ofFn AlternatingPairRepair.word).map g) := by rwa [ordered]
  obtain ⟨D,x,y,fit⟩ :=
    AlternatingPairRepair.compatible_mapped (graph6 H p) (ports p) closed g start
  obtain ⟨k,hk⟩ := reconstruct H p embedding D x y fit
  exact ⟨restrict H p D,k,hk⟩

end FourColor.StripPairCompletion
