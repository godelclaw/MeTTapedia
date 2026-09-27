import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

/-- Incidence data for color-chains that vanish at vertices and on a distinguished boundary. -/
structure ZeroBoundaryData (V E : Type*) where
  incident : V → Finset E
  boundaryEdges : Finset E

namespace ZeroBoundaryData

variable {V E : Type*} (D : ZeroBoundaryData V E)

/-- A chain has zero boundary when each vertex-incidence sum vanishes. -/
def isZeroBoundary (x : E → Color) : Prop :=
  ∀ v : V, ∑ e ∈ D.incident v, x e = 0

/-- Chains that vanish at every vertex and on the distinguished boundary edges. -/
def zeroBoundarySet : Set (E → Color) :=
  {x | D.isZeroBoundary x ∧ ∀ e ∈ D.boundaryEdges, x e = 0}

theorem zeroChain_isZeroBoundary :
    D.isZeroBoundary (zeroChain : E → Color) := by
  intro v
  simp [zeroChain]

theorem zeroChain_mem_zeroBoundarySet :
    (zeroChain : E → Color) ∈ D.zeroBoundarySet := by
  refine ⟨D.zeroChain_isZeroBoundary, ?_⟩
  intro e _he
  rfl

theorem isZeroBoundary_add {x y : E → Color}
    (hx : D.isZeroBoundary x) (hy : D.isZeroBoundary y) :
    D.isZeroBoundary (x + y) := by
  intro v
  simp [Finset.sum_add_distrib, hx v, hy v]

theorem mem_zero_add {x y : E → Color}
    (hx : x ∈ D.zeroBoundarySet) (hy : y ∈ D.zeroBoundarySet) :
    x + y ∈ D.zeroBoundarySet := by
  rcases hx with ⟨hxV, hxB⟩
  rcases hy with ⟨hyV, hyB⟩
  refine ⟨D.isZeroBoundary_add hxV hyV, ?_⟩
  intro e he
  simp [hxB e he, hyB e he]

theorem sum_mem_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → E → Color)
    (h : ∀ i ∈ S, f i ∈ D.zeroBoundarySet) :
    (∑ i ∈ S, f i) ∈ D.zeroBoundarySet := by
  classical
  induction S using Finset.induction with
  | empty =>
      change (0 : E → Color) ∈ D.zeroBoundarySet
      refine ⟨?_, ?_⟩
      · intro v
        simp
      · intro e _he
        rfl
  | insert i S hi ih =>
      have hi' : f i ∈ D.zeroBoundarySet := h i (Finset.mem_insert_self _ _)
      have hS : ∀ j ∈ S, f j ∈ D.zeroBoundarySet :=
        fun j hj => h j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert hi] using D.mem_zero_add hi' (ih hS)

end ZeroBoundaryData

/-- Chain attached to a face boundary, colored by `γ`. -/
def faceBoundaryChain {E : Type*} [DecidableEq E] (γ : Color) (f : Finset E) :
    E → Color :=
  indicatorChain γ f

@[simp] theorem faceBoundaryChain_apply_of_mem {E : Type*} [DecidableEq E]
    (γ : Color) {f : Finset E} {e : E} (he : e ∈ f) :
    faceBoundaryChain γ f e = γ := by
  simp [faceBoundaryChain, he]

@[simp] theorem faceBoundaryChain_apply_of_not_mem {E : Type*} [DecidableEq E]
    (γ : Color) {f : Finset E} {e : E} (he : e ∉ f) :
    faceBoundaryChain γ f e = 0 := by
  simp [faceBoundaryChain, he]

@[simp] theorem fst_faceBoundaryChain_red {E : Type*} [DecidableEq E]
    (f : Finset E) (e : E) :
    (faceBoundaryChain red f e).1 = if e ∈ f then (1 : F2) else 0 := by
  simp [faceBoundaryChain]

@[simp] theorem snd_faceBoundaryChain_blue {E : Type*} [DecidableEq E]
    (f : Finset E) (e : E) :
    (faceBoundaryChain blue f e).2 = if e ∈ f then (1 : F2) else 0 := by
  simp [faceBoundaryChain]

/-- Over `𝔽₂ × 𝔽₂`, adding a face-boundary chain to itself gives the zero chain. -/
theorem faceBoundaryChain_add_self {E : Type*} [DecidableEq E]
    (γ : Color) (f : Finset E) :
    faceBoundaryChain γ f + faceBoundaryChain γ f = zeroChain := by
  simpa [faceBoundaryChain] using indicatorChain_add_self (γ := γ) (S := f)

/-- Toggling a face by `red` flips exactly the first coordinate on that face boundary. -/
theorem support₁_faceBoundaryChain_red {E : Type*} [Fintype E] [DecidableEq E]
    (f : Finset E) :
    support₁ (faceBoundaryChain red f) = f := by
  simpa [faceBoundaryChain] using support₁_indicatorChain_red (S := f)

/-- Toggling a face by `red` changes first-coordinate support by symmetric difference. -/
theorem support₁_after_faceBoundaryChain_red {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {f : Finset E} :
    support₁ (x + faceBoundaryChain red f) =
      (support₁ x \ f) ∪ (f \ support₁ x) := by
  simpa [faceBoundaryChain] using
    (support₁_after_indicatorChain_red (x := x) (S := f))

/-- Toggling a face by `blue` flips exactly the second coordinate on that face boundary. -/
theorem support₂_faceBoundaryChain_blue {E : Type*} [Fintype E] [DecidableEq E]
    (f : Finset E) :
    support₂ (faceBoundaryChain blue f) = f := by
  simpa [faceBoundaryChain] using support₂_indicatorChain_blue (S := f)

/-- Toggling a face by `blue` changes second-coordinate support by symmetric difference. -/
theorem support₂_after_faceBoundaryChain_blue {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {f : Finset E} :
    support₂ (x + faceBoundaryChain blue f) =
      (support₂ x \ f) ∪ (f \ support₂ x) := by
  simpa [faceBoundaryChain] using
    (support₂_after_indicatorChain_blue (x := x) (S := f))

/-- Fold symmetric difference over a list of face boundaries. -/
def symmDiffFold {E : Type*} [DecidableEq E]
    (initial : Finset E) (faces : List (Finset E)) : Finset E :=
  faces.foldl (fun acc f => (acc \ f) ∪ (f \ acc)) initial

@[simp] theorem symmDiffFold_nil {E : Type*} [DecidableEq E] (initial : Finset E) :
    symmDiffFold initial [] = initial :=
  rfl

theorem symmDiffFold_cons {E : Type*} [DecidableEq E]
    (initial : Finset E) (f : Finset E) (faces : List (Finset E)) :
    symmDiffFold initial (f :: faces) =
      symmDiffFold ((initial \ f) ∪ (f \ initial)) faces :=
  rfl

/-- Edges with odd incidence across a finite family of face-boundary sets. -/
def oddOn {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset (Finset E)) : Finset E :=
  Finset.univ.filter fun e =>
    (∑ f ∈ S, (if e ∈ f then (1 : F2) else 0)) ≠ 0

@[simp] theorem mem_oddOn_iff {E : Type*} [Fintype E] [DecidableEq E]
    {S : Finset (Finset E)} {e : E} :
    e ∈ oddOn S ↔ (∑ f ∈ S, (if e ∈ f then (1 : F2) else 0)) ≠ 0 := by
  simp [oddOn]

/-- Span of face-boundary chains, encoded as finite sums over selected faces. -/
def faceBoundarySpan {E : Type*} [DecidableEq E]
    (γ : Color) (faces : Finset (Finset E)) : Set (E → Color) :=
  {x | ∃ S ⊆ faces, x = ∑ f ∈ S, faceBoundaryChain γ f}

theorem mem_faceBoundarySpan_of_subset {E : Type*} [DecidableEq E]
    {γ : Color} {faces S : Finset (Finset E)} (hS : S ⊆ faces) :
    (∑ f ∈ S, faceBoundaryChain γ f) ∈ faceBoundarySpan γ faces := by
  exact ⟨S, hS, rfl⟩

theorem faceBoundarySpan_mono {E : Type*} [DecidableEq E]
    {γ : Color} {faces faces' : Finset (Finset E)}
    (hfaces : faces ⊆ faces') :
    faceBoundarySpan γ faces ⊆ faceBoundarySpan γ faces' := by
  intro x hx
  rcases hx with ⟨S, hS, hsum⟩
  exact ⟨S, hS.trans hfaces, hsum⟩

/-- Sum of face-boundary chains over a finite face set. This is the modern,
geometry-free form of the old `toggleSum` operation. -/
def faceBoundarySum {E : Type*} [DecidableEq E]
    (γ : Color) (faces : Finset (Finset E)) : E → Color :=
  ∑ f ∈ faces, faceBoundaryChain γ f

@[simp] theorem faceBoundarySum_apply {E : Type*} [DecidableEq E]
    (γ : Color) (faces : Finset (Finset E)) (e : E) :
    faceBoundarySum γ faces e = ∑ f ∈ faces, faceBoundaryChain γ f e := by
  simp [faceBoundarySum, Finset.sum_apply]

theorem faceBoundarySum_mem_faceBoundarySpan {E : Type*} [DecidableEq E]
    (γ : Color) (faces : Finset (Finset E)) :
    faceBoundarySum γ faces ∈ faceBoundarySpan γ faces :=
  ⟨faces, subset_rfl, rfl⟩

theorem fst_sum_faceBoundaryChain_red {E : Type*} [Fintype E] [DecidableEq E]
    (faces : Finset (Finset E)) (e : E) :
    ((∑ f ∈ faces, faceBoundaryChain red f) e).1 =
      ∑ f ∈ faces, if e ∈ f then (1 : F2) else 0 := by
  revert e
  refine Finset.induction_on faces ?base ?step
  · intro e
    simp
  · intro face faces hface ih e
    rw [Finset.sum_insert hface, Finset.sum_insert hface, Pi.add_apply]
    show (faceBoundaryChain red face e +
        (∑ f ∈ faces, faceBoundaryChain red f) e).1 =
      (if e ∈ face then 1 else 0) +
        ∑ f ∈ faces, if e ∈ f then 1 else 0
    simp only [Prod.fst_add, fst_faceBoundaryChain_red]
    congr 1
    exact ih e

theorem snd_sum_faceBoundaryChain_blue {E : Type*} [Fintype E] [DecidableEq E]
    (faces : Finset (Finset E)) (e : E) :
    ((∑ f ∈ faces, faceBoundaryChain blue f) e).2 =
      ∑ f ∈ faces, if e ∈ f then (1 : F2) else 0 := by
  revert e
  refine Finset.induction_on faces ?base ?step
  · intro e
    simp
  · intro face faces hface ih e
    rw [Finset.sum_insert hface, Finset.sum_insert hface, Pi.add_apply]
    show (faceBoundaryChain blue face e +
        (∑ f ∈ faces, faceBoundaryChain blue f) e).2 =
      (if e ∈ face then 1 else 0) +
        ∑ f ∈ faces, if e ∈ f then 1 else 0
    simp only [Prod.snd_add, snd_faceBoundaryChain_blue]
    congr 1
    exact ih e

theorem fst_faceBoundarySum_red {E : Type*} [Fintype E] [DecidableEq E]
    (faces : Finset (Finset E)) (e : E) :
    (faceBoundarySum red faces e).1 =
      ∑ f ∈ faces, if e ∈ f then (1 : F2) else 0 := by
  simpa [faceBoundarySum] using fst_sum_faceBoundaryChain_red (faces := faces) e

theorem snd_faceBoundarySum_blue {E : Type*} [Fintype E] [DecidableEq E]
    (faces : Finset (Finset E)) (e : E) :
    (faceBoundarySum blue faces e).2 =
      ∑ f ∈ faces, if e ∈ f then (1 : F2) else 0 := by
  simpa [faceBoundarySum] using snd_sum_faceBoundaryChain_blue (faces := faces) e

theorem support₁_faceBoundarySum_red_eq_oddOn {E : Type*} [Fintype E] [DecidableEq E]
    (faces : Finset (Finset E)) :
    support₁ (faceBoundarySum red faces) = oddOn faces := by
  ext e
  have hfst :
      (faceBoundarySum red faces e).1 =
        ∑ f ∈ faces, if e ∈ f then (1 : F2) else 0 :=
    fst_faceBoundarySum_red (faces := faces) e
  have hodd :
      ((∑ f ∈ faces, if e ∈ f then (1 : F2) else 0) ≠ 0) ↔ e ∈ oddOn faces := by
    simp only [oddOn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlhs :
      e ∈ support₁ (faceBoundarySum red faces) ↔
        ((∑ f ∈ faces, if e ∈ f then (1 : F2) else 0) ≠ 0) := by
    simp only [support₁, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfst]
  rw [hlhs, hodd]

theorem support₂_faceBoundarySum_blue_eq_oddOn {E : Type*} [Fintype E] [DecidableEq E]
    (faces : Finset (Finset E)) :
    support₂ (faceBoundarySum blue faces) = oddOn faces := by
  ext e
  have hsnd :
      (faceBoundarySum blue faces e).2 =
        ∑ f ∈ faces, if e ∈ f then (1 : F2) else 0 :=
    snd_faceBoundarySum_blue (faces := faces) e
  have hodd :
      ((∑ f ∈ faces, if e ∈ f then (1 : F2) else 0) ≠ 0) ↔ e ∈ oddOn faces := by
    simp only [oddOn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlhs :
      e ∈ support₂ (faceBoundarySum blue faces) ↔
        ((∑ f ∈ faces, if e ∈ f then (1 : F2) else 0) ≠ 0) := by
    simp only [support₂, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsnd]
  rw [hlhs, hodd]

/-- Face-boundary chain relative to a boundary-edge set: boundary edges are
zeroed before the chain is formed. This ports the clean part of old
`faceBoundaryChainRel` without importing old disk-geometry assumptions. -/
def relativeFaceBoundaryChain {E : Type*} [DecidableEq E]
    (boundaryEdges : Finset E) (γ : Color) (face : Finset E) : E → Color :=
  indicatorChain γ (face \ boundaryEdges)

@[simp] theorem relativeFaceBoundaryChain_apply {E : Type*} [DecidableEq E]
    (boundaryEdges : Finset E) (γ : Color) (face : Finset E) (e : E) :
    relativeFaceBoundaryChain boundaryEdges γ face e =
      if e ∈ face ∧ e ∉ boundaryEdges then γ else 0 := by
  by_cases he : e ∈ face ∧ e ∉ boundaryEdges
  · simp [relativeFaceBoundaryChain, indicatorChain, he.1, he.2]
  · have hsdiff : e ∉ face \ boundaryEdges := by
      intro h
      exact he ⟨(Finset.mem_sdiff.1 h).1, (Finset.mem_sdiff.1 h).2⟩
    simp [relativeFaceBoundaryChain, indicatorChain, hsdiff, he]

@[simp] theorem relativeFaceBoundaryChain_apply_of_mem_boundary {E : Type*} [DecidableEq E]
    (boundaryEdges : Finset E) (γ : Color) (face : Finset E) {e : E}
    (he : e ∈ boundaryEdges) :
    relativeFaceBoundaryChain boundaryEdges γ face e = 0 := by
  simp [relativeFaceBoundaryChain, indicatorChain, he]

@[simp] theorem relativeFaceBoundaryChain_apply_of_not_mem_face {E : Type*} [DecidableEq E]
    (boundaryEdges : Finset E) (γ : Color) {face : Finset E} {e : E}
    (he : e ∉ face) :
    relativeFaceBoundaryChain boundaryEdges γ face e = 0 := by
  simp [relativeFaceBoundaryChain, indicatorChain, he]

theorem support₁_relativeFaceBoundaryChain_red {E : Type*} [Fintype E] [DecidableEq E]
    (boundaryEdges : Finset E) (face : Finset E) :
    support₁ (relativeFaceBoundaryChain boundaryEdges red face) = face \ boundaryEdges := by
  simpa [relativeFaceBoundaryChain] using
    support₁_indicatorChain_red (S := face \ boundaryEdges)

theorem support₂_relativeFaceBoundaryChain_blue {E : Type*} [Fintype E] [DecidableEq E]
    (boundaryEdges : Finset E) (face : Finset E) :
    support₂ (relativeFaceBoundaryChain boundaryEdges blue face) = face \ boundaryEdges := by
  simpa [relativeFaceBoundaryChain] using
    support₂_indicatorChain_blue (S := face \ boundaryEdges)

/-- Sum of relative face-boundary chains over a finite face set. -/
def relativeFaceBoundarySum {E : Type*} [DecidableEq E]
    (boundaryEdges : Finset E) (γ : Color) (faces : Finset (Finset E)) : E → Color :=
  ∑ f ∈ faces, relativeFaceBoundaryChain boundaryEdges γ f

@[simp] theorem relativeFaceBoundarySum_apply {E : Type*} [DecidableEq E]
    (boundaryEdges : Finset E) (γ : Color) (faces : Finset (Finset E)) (e : E) :
    relativeFaceBoundarySum boundaryEdges γ faces e =
      ∑ f ∈ faces, relativeFaceBoundaryChain boundaryEdges γ f e := by
  simp [relativeFaceBoundarySum, Finset.sum_apply]

theorem relativeFaceBoundarySum_apply_of_mem_boundary {E : Type*} [DecidableEq E]
    (boundaryEdges : Finset E) (γ : Color) (faces : Finset (Finset E))
    {e : E} (he : e ∈ boundaryEdges) :
    relativeFaceBoundarySum boundaryEdges γ faces e = 0 := by
  simp [relativeFaceBoundarySum, Finset.sum_apply, he]

end Mettapedia.GraphTheory.FourColor
