import MettapediaFourColor.RuleMatcher
import MettapediaFourColor.ExceptionalCoreOrientation

/-!
# Shared cyclic closure exposes two diamond reductions

Rule 003_2 and rule 004_1 can meet on the same receiver and the same
neighbour. Their two and three known turns concatenate at that neighbour.
If its actual degree is six, cyclic closure supplies the missing corner.
Triangular face closure then exposes an edge from a five to a six, with a
five on each flank, provided the first sender has degree five.
At shared degree five the same path identifies its endpoint corners. A
degree-five remaining corner then gives the all-pentagonal diamond; the
combined split retains the shared-five/outer-six residual explicitly.

No injectivity, independent boundary choices, or globally bounded face
lengths are assumed. The same actual darts witness both rule readings.
-/

namespace FourColor.RulePairDiamond

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge ExceptionalOverlap ExceptionalCoreOrientation

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} [Finite V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite] (rotation : Data G)

/-- Actual degrees and the two consecutive flanks of one oriented edge. -/
structure MixedAt (d : G.Dart) : Prop where
  five : G.degree d.fst = 5
  six : G.degree d.snd = 6
  next : G.degree (rotation.vertexRotation d).snd = 5
  previous : G.degree (rotation.vertexRotation.symm d).snd = 5

/-- The corresponding all-pentagonal pattern, with both flanks retained. -/
structure PentagonalAt (d : G.Dart) : Prop where
  five : G.degree d.fst = 5
  opposite : G.degree d.snd = 5
  next : G.degree (rotation.vertexRotation d).snd = 5
  previous : G.degree (rotation.vertexRotation.symm d).snd = 5

omit [Finite V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem period [Finite V] (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart) :
    (rotation.vertexRotation ^ G.degree d.fst) d = d := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let fiber : Finset G.Dart := Finset.univ.filter fun e => e.fst = d.fst
  have hc : rotation.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
    simpa [fiber] using cyclic d.fst
  have card : fiber.card = G.degree d.fst := by
    change ({e : G.Dart | e.fst = d.fst} : Finset G.Dart).card = _
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent d.fst _ _).symm
  simpa only [card] using hc.pow_card_apply (show d ∈ fiber by simp [fiber])

abbrev Left (rotation : Data G) := Occurrence rotation (4 : Fin 84)
abbrev Right (rotation : Data G) := Occurrence rotation (5 : Fin 84)

variable {rotation} (x : Left rotation) (y : Right rotation)

private def ld (i j : Vertex (4 : Fin 84)) (h : (graph (4 : Fin 84)).Adj i j) : G.Dart :=
  ⟨(x.vertex i, x.vertex j), x.edge i j h⟩

private def rd (i j : Vertex (5 : Fin 84)) (h : (graph (5 : Fin 84)).Adj i j) : G.Dart :=
  ⟨(y.vertex i, y.vertex j), y.edge i j h⟩

omit [Finite V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem five_turns
    (centre : x.vertex 1 = y.vertex 1) (shared : x.vertex 2 = y.vertex 2) :
    (rotation.vertexRotation ^ 5) (ld x 2 3 (by decide +kernel)) =
      rd y 2 4 (by decide +kernel) := by
  let a := ld x 2 3 (by decide +kernel)
  let b := ld x 2 0 (by decide +kernel)
  let c := ld x 2 1 (by decide +kernel)
  let d := rd y 2 0 (by decide +kernel)
  let e := rd y 2 3 (by decide +kernel)
  let f := rd y 2 4 (by decide +kernel)
  have ab : rotation.vertexRotation a = b := x.turn 2 3 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have bc : rotation.vertexRotation b = c := x.turn 2 0 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have cc : c = rd y 2 1 (by decide +kernel) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext shared centre
  have cd : rotation.vertexRotation c = d := by
    rw [cc]
    exact y.turn 2 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have de : rotation.vertexRotation d = e := y.turn 2 0 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ef : rotation.vertexRotation e = f := y.turn 2 3 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change (rotation.vertexRotation ^ 5) a = f
  simp only [pow_succ', pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    ab, bc, cd, de, ef]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Two partial stars concatenate around their shared vertex. The sixth
turn is forced by its degree and actual cyclic rotation. -/
theorem closing_corner (cyclic : rotation.IsVertexwiseCyclic)
    (centre : x.vertex 1 = y.vertex 1) (shared : x.vertex 2 = y.vertex 2)
    (six : G.degree (x.vertex 2) = 6) :
    Corner rotation (x.vertex 2) (y.vertex 4) (x.vertex 3) := by
  let a := ld x 2 3 (by decide +kernel)
  let f := rd y 2 4 (by decide +kernel)
  have hp := period rotation cyclic a
  have ha : G.degree a.fst = 6 := six
  rw [ha] at hp
  have fa : rotation.vertexRotation f = a := by
    change rotation.vertexRotation ((rotation.vertexRotation ^ 5) a) = a at hp
    rwa [five_turns x y centre shared] at hp
  have hf : G.Adj (x.vertex 2) (y.vertex 4) := shared ▸ y.edge 2 4 (by decide +kernel)
  refine ⟨hf, x.edge 2 3 (by decide +kernel), ?_⟩
  have eqf : (⟨(x.vertex 2, y.vertex 4), hf⟩ : G.Dart) = f := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext shared rfl
  rw [eqf]
  exact fa

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- At degree five the same path closes by identifying its endpoints.
The collision is an actual equality of vertices, not a discarded branch. -/
theorem identified_corner (cyclic : rotation.IsVertexwiseCyclic)
    (centre : x.vertex 1 = y.vertex 1) (shared : x.vertex 2 = y.vertex 2)
    (five : G.degree (x.vertex 2) = 5) : y.vertex 4 = x.vertex 3 := by
  have hp := period rotation cyclic (ld x 2 3 (by decide +kernel))
  change (rotation.vertexRotation ^ G.degree (x.vertex 2)) _ = _ at hp
  rw [five, five_turns x y centre shared] at hp
  exact congrArg (fun d : G.Dart => d.snd) hp

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A closed five-step overlap gives the pentagonal pattern when its
remaining outer corner and first sender also have degree five. -/
theorem pentagonal (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (centre : x.vertex 1 = y.vertex 1) (shared : x.vertex 2 = y.vertex 2)
    (five : G.degree (x.vertex 2) = 5) (sender : G.degree (x.vertex 0) = 5)
    (outer : G.degree (y.vertex 3) = 5) :
    ∃ d : G.Dart, PentagonalAt rotation d := by
  have identified := identified_corner x y cyclic centre shared five
  have close : Corner rotation (x.vertex 2) (y.vertex 3) (x.vertex 3) := by
    rw [shared, ← identified]
    exact ⟨y.edge 2 3 (by decide +kernel), y.edge 2 4 (by decide +kernel),
      y.turn 2 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  have close' := Corner.rotate rotation tri (Corner.rotate rotation tri close)
  have old : Corner rotation (x.vertex 2) (x.vertex 3) (x.vertex 0) :=
    ⟨x.edge 2 3 (by decide +kernel), x.edge 2 0 (by decide +kernel),
      x.turn 2 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  have old' := Corner.rotate rotation tri old
  let d := ld x 3 2 (by decide +kernel)
  obtain ⟨_, hnext, enext⟩ := close'
  obtain ⟨hprev, _, eprev⟩ := old'
  have enx : rotation.vertexRotation d = ⟨(x.vertex 3, y.vertex 3), hnext⟩ := enext
  have epr : rotation.vertexRotation.symm d = ⟨(x.vertex 3, x.vertex 0), hprev⟩ := by
    apply rotation.vertexRotation.injective
    rw [Equiv.apply_symm_apply]
    exact eprev.symm
  have dx : G.degree (x.vertex 3) = 5 := by
    have h := x.degree 3
    rw [show lower 4 3 = 5 from by decide +kernel,
      show upper 4 3 = 5 from by decide +kernel] at h
    omega
  exact ⟨d, dx, five, by rw [enx]; exact outer, by rw [epr]; exact sender⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The two readings force the actual mixed-diamond degree pattern.
The missing triangle is derived from cyclic and triangular closure. -/
theorem mixed (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (centre : x.vertex 1 = y.vertex 1) (shared : x.vertex 2 = y.vertex 2)
    (six : G.degree (x.vertex 2) = 6) (five : G.degree (x.vertex 0) = 5) :
    ∃ d : G.Dart, MixedAt rotation d := by
  have close := closing_corner x y cyclic centre shared six
  have close' := Corner.rotate rotation tri (Corner.rotate rotation tri close)
  have old : Corner rotation (x.vertex 2) (x.vertex 3) (x.vertex 0) :=
    ⟨x.edge 2 3 (by decide +kernel), x.edge 2 0 (by decide +kernel),
      x.turn 2 3 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  have old' := Corner.rotate rotation tri old
  let d := ld x 3 2 (by decide +kernel)
  obtain ⟨_, hnext, enext⟩ := close'
  obtain ⟨hprev, _, eprev⟩ := old'
  have enx : rotation.vertexRotation d = ⟨(x.vertex 3, y.vertex 4), hnext⟩ := enext
  have epr : rotation.vertexRotation.symm d = ⟨(x.vertex 3, x.vertex 0), hprev⟩ := by
    apply rotation.vertexRotation.injective
    rw [Equiv.apply_symm_apply]
    exact eprev.symm
  have dx : G.degree (x.vertex 3) = 5 := by
    have h := x.degree 3
    rw [show lower 4 3 = 5 from by decide +kernel,
      show upper 4 3 = 5 from by decide +kernel] at h
    omega
  have dy : G.degree (y.vertex 4) = 5 := by
    have h := y.degree 4
    rw [show lower 5 4 = 5 from by decide +kernel,
      show upper 5 4 = 5 from by decide +kernel] at h
    omega
  exact ⟨d, dx, six, by rw [enx]; exact dy, by rw [epr]; exact five⟩

/-- The second incoming edge is found by two backward turns at the receiver. -/
def secondRoot (d : G.Dart) : G.Dart :=
  (rotation.vertexRotation.symm (rotation.vertexRotation.symm d.symm)).symm

omit [Finite V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Root alignment implies the two readings share both receiver and corner.
Neither equality is supplied independently by the caller. -/
theorem aligned (d : G.Dart)
    (xs : x.vertex 0 = d.fst) (xt : x.vertex 1 = d.snd)
    (ys : y.vertex 0 = (secondRoot (rotation := rotation) d).fst)
    (yt : y.vertex 1 = (secondRoot (rotation := rotation) d).snd) :
    x.vertex 1 = y.vertex 1 ∧ x.vertex 2 = y.vertex 2 := by
  have rx : ld x 1 0 (by decide +kernel) = d.symm := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext xt xs
  have ry : rd y 1 0 (by decide +kernel) =
      rotation.vertexRotation.symm (rotation.vertexRotation.symm d.symm) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext yt ys
  have tx : rotation.vertexRotation (ld x 1 2 (by decide +kernel)) =
      ld x 1 0 (by decide +kernel) :=
    x.turn 1 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ty : rotation.vertexRotation (rd y 1 0 (by decide +kernel)) =
      rd y 1 2 (by decide +kernel) :=
    y.turn 1 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ex : ld x 1 2 (by decide +kernel) = rotation.vertexRotation.symm d.symm := by
    rw [← rx, ← tx, Equiv.symm_apply_apply]
  have ey : rd y 1 2 (by decide +kernel) = rotation.vertexRotation.symm d.symm := by
    rw [← ty, ry, Equiv.apply_symm_apply]
  have eq := ex.trans ey.symm
  exact ⟨congrArg (fun z : G.Dart => z.fst) eq,
    congrArg (fun z : G.Dart => z.snd) eq⟩

/-- A concrete consumer of the exact matcher: two positive rule checks
and two actual degree observations supply a geometric reduction pattern. -/
theorem mixed_of_checks (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (d : G.Dart) (left : RuleMatcher.check rotation 4 d = true)
    (right : RuleMatcher.check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (five : G.degree d.fst = 5)
    (six : G.degree (RuleMatcher.candidate rotation 4 d 2) = 6) :
    ∃ e : G.Dart, MixedAt rotation e := by
  obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff rotation d).mp left
  obtain ⟨y, ys, yt⟩ := (RuleMatcher.check_iff rotation _).mp right
  obtain ⟨hc, hw⟩ := aligned x y d xs xt ys yt
  apply mixed x y cyclic tri hc hw
  · rwa [RuleMatcher.candidate_eq rotation d x xs xt] at six
  · exact xs ▸ five

/-- The exact matcher also consumes the identified-corner branch. -/
theorem pentagonal_of_checks (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (d : G.Dart) (left : RuleMatcher.check rotation 4 d = true)
    (right : RuleMatcher.check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (sender : G.degree d.fst = 5)
    (five : G.degree (RuleMatcher.candidate rotation 4 d 2) = 5)
    (outer : G.degree (RuleMatcher.candidate rotation 5
      (secondRoot (rotation := rotation) d) 3) = 5) :
    ∃ e : G.Dart, PentagonalAt rotation e := by
  obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff rotation d).mp left
  obtain ⟨y, ys, yt⟩ := (RuleMatcher.check_iff rotation _).mp right
  obtain ⟨hc, hw⟩ := aligned x y d xs xt ys yt
  apply pentagonal x y cyclic tri hc hw
  · rwa [RuleMatcher.candidate_eq rotation d x xs xt] at five
  · exact xs ▸ sender
  · rwa [RuleMatcher.candidate_eq rotation _ y ys yt] at outer

/-- Exact alternatives for every aligned pair with a degree-five first
sender. The unhandled five/six profile is retained explicitly. -/
theorem pair_alternatives (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (d : G.Dart) (left : RuleMatcher.check rotation 4 d = true)
    (right : RuleMatcher.check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (sender : G.degree d.fst = 5) :
    (∃ e : G.Dart, MixedAt rotation e) ∨
    (∃ e : G.Dart, PentagonalAt rotation e) ∨
    (G.degree (RuleMatcher.candidate rotation 4 d 2) = 5 ∧
      G.degree (RuleMatcher.candidate rotation 5
        (secondRoot (rotation := rotation) d) 3) = 6) := by
  obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff rotation d).mp left
  obtain ⟨y, ys, yt⟩ := (RuleMatcher.check_iff rotation _).mp right
  have hx := x.degree 2
  have hy := y.degree 3
  rw [show lower 4 2 = 5 from by decide +kernel,
    show upper 4 2 = 6 from by decide +kernel,
    ← RuleMatcher.candidate_eq rotation d x xs xt] at hx
  rw [show lower 5 3 = 5 from by decide +kernel,
    show upper 5 3 = 6 from by decide +kernel,
    ← RuleMatcher.candidate_eq rotation _ y ys yt] at hy
  by_cases six : G.degree (RuleMatcher.candidate rotation 4 d 2) = 6
  · exact Or.inl (mixed_of_checks cyclic tri d left right sender six)
  have five : G.degree (RuleMatcher.candidate rotation 4 d 2) = 5 := by omega
  by_cases outer : G.degree (RuleMatcher.candidate rotation 5
      (secondRoot (rotation := rotation) d) 3) = 5
  · exact Or.inr (Or.inl (pentagonal_of_checks cyclic tri d left right sender five outer))
  · exact Or.inr (Or.inr ⟨five, by omega⟩)

end FourColor.RulePairDiamond
