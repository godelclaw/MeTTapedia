import Mettapedia.GraphTheory.FourColor.BoundaryChains

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

variable {V E : Type*}

@[simp] theorem zeroChain_eq_zero {E : Type*} : (zeroChain : E → Color) = 0 :=
  rfl

section SpanAlgebra

variable [DecidableEq E]

/-- Summation helper: inserting a new face adds its boundary chain. -/
theorem sum_faceBoundary_insert {γ : Color} {faces : Finset (Finset E)} {face : Finset E}
    (hface : face ∉ faces) :
    faceBoundaryChain γ face + (∑ f ∈ faces, faceBoundaryChain γ f)
      = ∑ f ∈ insert face faces, faceBoundaryChain γ f := by
  classical
  simp [Finset.sum_insert hface]

/-- Summation helper: a present face plus the sum over the erased set reconstructs the full sum. -/
theorem sum_faceBoundary_face_plus_erase_eq {γ : Color} {faces : Finset (Finset E)}
    {face : Finset E} (hface : face ∈ faces) :
    faceBoundaryChain γ face + (∑ f ∈ faces.erase face, faceBoundaryChain γ f)
      = ∑ f ∈ faces, faceBoundaryChain γ f := by
  classical
  have hnot : face ∉ faces.erase face := Finset.notMem_erase _ _
  have hperm : insert face (faces.erase face) = faces := Finset.insert_erase hface
  calc
    faceBoundaryChain γ face + (∑ f ∈ faces.erase face, faceBoundaryChain γ f)
        = ∑ f ∈ insert face (faces.erase face), faceBoundaryChain γ f := by
          exact sum_faceBoundary_insert (γ := γ) (faces := faces.erase face)
            (face := face) hnot
    _ = ∑ f ∈ faces, faceBoundaryChain γ f := by
          simp [hperm]

/-- Summation helper: erasing a present face toggles by that face boundary. -/
theorem sum_faceBoundary_erase {γ : Color} {faces : Finset (Finset E)} {face : Finset E}
    (hface : face ∈ faces) :
    (∑ f ∈ faces.erase face, faceBoundaryChain γ f)
      = faceBoundaryChain γ face + ∑ f ∈ faces, faceBoundaryChain γ f := by
  classical
  have hsum :=
    sum_faceBoundary_face_plus_erase_eq (γ := γ) (faces := faces) (face := face) hface
  calc
    ∑ f ∈ faces.erase face, faceBoundaryChain γ f
        = zeroChain +
            ∑ f ∈ faces.erase face, faceBoundaryChain γ f := by
              simp
    _ = (faceBoundaryChain γ face + faceBoundaryChain γ face)
            + ∑ f ∈ faces.erase face, faceBoundaryChain γ f := by
              simp [faceBoundaryChain_add_self, add_comm]
    _ = faceBoundaryChain γ face +
            (faceBoundaryChain γ face
              + ∑ f ∈ faces.erase face, faceBoundaryChain γ f) := by
              simp [add_comm, add_left_comm]
    _ = faceBoundaryChain γ face + ∑ f ∈ faces, faceBoundaryChain γ f := by
              simp [hsum]

/-- The finite face-boundary span is closed under toggling by one available face. -/
theorem faceBoundarySpan_add_face {γ : Color} {faces : Finset (Finset E)}
    {x : E → Color} (hx : x ∈ faceBoundarySpan γ faces)
    {face : Finset E} (hface : face ∈ faces) :
    x + faceBoundaryChain γ face ∈ faceBoundarySpan γ faces := by
  classical
  rcases hx with ⟨S, hS, hxS⟩
  by_cases hmem : face ∈ S
  · refine ⟨S.erase face, ?_, ?_⟩
    · intro g hg
      exact hS (Finset.mem_of_mem_erase hg)
    · calc
        x + faceBoundaryChain γ face
            = (∑ g ∈ S, faceBoundaryChain γ g) + faceBoundaryChain γ face := by
                simp [hxS]
        _ = faceBoundaryChain γ face + ∑ g ∈ S, faceBoundaryChain γ g := by
                simp [add_comm]
        _ = ∑ g ∈ S.erase face, faceBoundaryChain γ g := by
                rw [sum_faceBoundary_erase (γ := γ) (faces := S) (face := face) hmem]
  · refine ⟨insert face S, ?_, ?_⟩
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hgS
      · exact hface
      · exact hS hgS
    · calc
        x + faceBoundaryChain γ face
            = (∑ g ∈ S, faceBoundaryChain γ g) + faceBoundaryChain γ face := by
                simp [hxS]
        _ = faceBoundaryChain γ face + ∑ g ∈ S, faceBoundaryChain γ g := by
                simp [add_comm]
        _ = ∑ g ∈ insert face S, faceBoundaryChain γ g := by
                exact sum_faceBoundary_insert (γ := γ) (faces := S) (face := face) hmem

/-- The finite face-boundary span is closed under toggling by a finite set of available faces. -/
theorem faceBoundarySpan_add_sum {γ : Color} {faces T : Finset (Finset E)}
    {x : E → Color} (hx : x ∈ faceBoundarySpan γ faces) (hT : T ⊆ faces) :
    x + (∑ f ∈ T, faceBoundaryChain γ f) ∈ faceBoundarySpan γ faces := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa using hx
  | insert face T hnot ih =>
      have hface : face ∈ faces := hT (Finset.mem_insert_self _ _)
      have hT' : T ⊆ faces := fun g hg => hT (Finset.mem_insert_of_mem hg)
      have hspanT := ih hT'
      have hspanFace := faceBoundarySpan_add_face
        (γ := γ) (faces := faces) (x := x + ∑ f ∈ T, faceBoundaryChain γ f)
        hspanT hface
      simpa [Finset.sum_insert hnot, add_comm, add_left_comm, add_assoc] using hspanFace

/-- The zero chain lies in every finite face-boundary span. -/
theorem zeroChain_mem_faceBoundarySpan {γ : Color} {faces : Finset (Finset E)} :
    (zeroChain : E → Color) ∈ faceBoundarySpan γ faces :=
  ⟨∅, by simp, by simp [faceBoundaryChain]⟩

/-- The finite face-boundary span is closed under addition of two span
members. -/
theorem faceBoundarySpan_add {γ : Color} {faces : Finset (Finset E)}
    {x y : E → Color} (hx : x ∈ faceBoundarySpan γ faces)
    (hy : y ∈ faceBoundarySpan γ faces) :
    x + y ∈ faceBoundarySpan γ faces := by
  rcases hy with ⟨T, hT, rfl⟩
  exact faceBoundarySpan_add_sum (γ := γ) (faces := faces) hx hT

end SpanAlgebra

/-- Algebraic single-face peel data, ported from the old FourColor attempt under a neutral name.
This is only the color-chain induction interface; it does not assert that a planar embedding supplies
the peel. Geometry-facing code should produce one of the Theorem49 peel certificates first. -/
structure BoundaryChainSinglePeelData (V E : Type*) [Fintype E] [DecidableEq E] where
  zero : ZeroBoundaryData V E
  gamma : Color := red
  internalFaces : Finset (Finset E)
  boundary_mem_zero :
    ∀ {f}, f ∈ internalFaces →
      faceBoundaryChain gamma f ∈ zero.zeroBoundarySet
  tight :
    ∀ {x}, x ∈ zero.zeroBoundarySet → support₁ x = ∅ → x = zeroChain
  peel :
    ∀ {x},
      x ∈ zero.zeroBoundarySet →
      support₁ x ≠ ∅ →
      ∃ f ∈ internalFaces, ∃ x',
        x' ∈ zero.zeroBoundarySet ∧
        x = x' + faceBoundaryChain gamma f ∧
        Finset.card (support₁ x') < Finset.card (support₁ x)

/-- Algebraic aggregated-face peel data, matching the old multi-face `LeafPeelSumData` surface.
This is the preferred algebraic interface when the geometry naturally peels a whole leaf subtree. -/
structure BoundaryChainAggregatePeelData (V E : Type*) [Fintype E] [DecidableEq E] where
  zero : ZeroBoundaryData V E
  gamma : Color := red
  internalFaces : Finset (Finset E)
  boundary_mem_zero_sum :
    ∀ {S}, S ⊆ internalFaces →
      (∑ f ∈ S, faceBoundaryChain gamma f) ∈ zero.zeroBoundarySet
  tight :
    ∀ {x}, x ∈ zero.zeroBoundarySet → support₁ x = ∅ → x = zeroChain
  peel_sum :
    ∀ {x},
      x ∈ zero.zeroBoundarySet →
      support₁ x ≠ ∅ →
      ∃ S₀ : Finset (Finset E),
        S₀.Nonempty ∧
        S₀ ⊆ internalFaces ∧
        ∃ x',
          x' ∈ zero.zeroBoundarySet ∧
          x = x' + (∑ f ∈ S₀, faceBoundaryChain gamma f) ∧
          Finset.card (support₁ x') < Finset.card (support₁ x)

namespace BoundaryChainSinglePeelData

variable [Fintype E] [DecidableEq E]

/-- The old single-face peel interface is a special case of the preferred
aggregated-face peel interface, using singleton peel sets. -/
def toBoundaryChainAggregatePeelData
    (data : BoundaryChainSinglePeelData V E) :
    BoundaryChainAggregatePeelData V E where
  zero := data.zero
  gamma := data.gamma
  internalFaces := data.internalFaces
  boundary_mem_zero_sum := by
    intro S hS
    exact data.zero.sum_mem_zero S (fun f => faceBoundaryChain data.gamma f)
      (fun f hf => data.boundary_mem_zero (hS hf))
  tight := data.tight
  peel_sum := by
    intro x hx hsupport
    rcases data.peel hx hsupport with ⟨f, hf, x', hx', hx_eq, hcard⟩
    refine ⟨{f}, by simp, ?_, x', hx', ?_, hcard⟩
    · intro g hg
      rw [Finset.mem_singleton] at hg
      subst g
      exact hf
    · simpa using hx_eq

@[simp]
theorem toBoundaryChainAggregatePeelData_zero
    (data : BoundaryChainSinglePeelData V E) :
    data.toBoundaryChainAggregatePeelData.zero = data.zero :=
  rfl

@[simp]
theorem toBoundaryChainAggregatePeelData_gamma
    (data : BoundaryChainSinglePeelData V E) :
    data.toBoundaryChainAggregatePeelData.gamma = data.gamma :=
  rfl

@[simp]
theorem toBoundaryChainAggregatePeelData_internalFaces
    (data : BoundaryChainSinglePeelData V E) :
    data.toBoundaryChainAggregatePeelData.internalFaces = data.internalFaces :=
  rfl

/-- Single-face peel induction: every zero-boundary chain lies in the face-boundary span. -/
theorem zeroBoundarySet_subset_faceBoundarySpan
    (data : BoundaryChainSinglePeelData V E) :
    data.zero.zeroBoundarySet ⊆ faceBoundarySpan data.gamma data.internalFaces := by
  classical
  have peel_induction :
      ∀ n {x : E → Color}, x ∈ data.zero.zeroBoundarySet →
        Finset.card (support₁ x) ≤ n →
        x ∈ faceBoundarySpan data.gamma data.internalFaces := by
    intro n
    induction n with
    | zero =>
        intro x hx hcard
        have hsupp : support₁ x = ∅ := by
          have hzero : Finset.card (support₁ x) = 0 :=
            Nat.le_antisymm hcard (Nat.zero_le _)
          exact Finset.card_eq_zero.mp hzero
        have hx_zero : x = zeroChain := data.tight hx hsupp
        refine ⟨∅, by simp, ?_⟩
        simp [hx_zero, faceBoundaryChain]
    | succ n ih =>
        intro x hx hcard
        by_cases hzero : support₁ x = ∅
        · have hx_zero : x = zeroChain := data.tight hx hzero
          refine ⟨∅, by simp, ?_⟩
          simp [hx_zero, faceBoundaryChain]
        · rcases data.peel hx hzero with ⟨f, hf, x', hx', hx_eq, hlt⟩
          have hcard' : Finset.card (support₁ x') ≤ n :=
            (Nat.lt_succ_iff).1 (lt_of_lt_of_le hlt hcard)
          have hx'_span := ih hx' hcard'
          rw [hx_eq]
          exact faceBoundarySpan_add_face
            (γ := data.gamma) (faces := data.internalFaces) hx'_span hf
  intro x hx
  exact peel_induction (Finset.card (support₁ x)) hx le_rfl

/-- The face-boundary span generated by the allowed internal faces stays inside
the zero-boundary set. -/
theorem faceBoundarySpan_subset_zeroBoundarySet
    (data : BoundaryChainSinglePeelData V E) :
    faceBoundarySpan data.gamma data.internalFaces ⊆ data.zero.zeroBoundarySet := by
  intro x hx
  rcases hx with ⟨S, hS, rfl⟩
  exact data.zero.sum_mem_zero S (fun f => faceBoundaryChain data.gamma f)
    (fun f hf => data.boundary_mem_zero (hS hf))

/-- A single-face peel certificate identifies the zero-boundary chains exactly
with the finite span of the available face-boundary chains. -/
theorem zeroBoundarySet_eq_faceBoundarySpan
    (data : BoundaryChainSinglePeelData V E) :
    data.zero.zeroBoundarySet = faceBoundarySpan data.gamma data.internalFaces :=
  Set.Subset.antisymm data.zeroBoundarySet_subset_faceBoundarySpan
    data.faceBoundarySpan_subset_zeroBoundarySet

end BoundaryChainSinglePeelData

namespace BoundaryChainAggregatePeelData

variable [Fintype E] [DecidableEq E]

/-- Aggregate peel data also provides each individual face boundary as a
zero-boundary chain, by applying the aggregate condition to a singleton set. -/
theorem boundary_mem_zero
    (data : BoundaryChainAggregatePeelData V E) {f : Finset E}
    (hf : f ∈ data.internalFaces) :
    faceBoundaryChain data.gamma f ∈ data.zero.zeroBoundarySet := by
  simpa using
    data.boundary_mem_zero_sum
      (S := {f}) (by
        intro g hg
        rw [Finset.mem_singleton] at hg
        subst g
        exact hf)

/-- Aggregated-peel induction: every zero-boundary chain lies in the face-boundary span. -/
theorem zeroBoundarySet_subset_faceBoundarySpan
    (data : BoundaryChainAggregatePeelData V E) :
    data.zero.zeroBoundarySet ⊆ faceBoundarySpan data.gamma data.internalFaces := by
  classical
  have peel_induction :
      ∀ n {x : E → Color}, x ∈ data.zero.zeroBoundarySet →
        Finset.card (support₁ x) ≤ n →
        x ∈ faceBoundarySpan data.gamma data.internalFaces := by
    intro n
    induction n with
    | zero =>
        intro x hx hcard
        have hsupp : support₁ x = ∅ := by
          have hzero : Finset.card (support₁ x) = 0 :=
            Nat.le_antisymm hcard (Nat.zero_le _)
          exact Finset.card_eq_zero.mp hzero
        have hx_zero : x = zeroChain := data.tight hx hsupp
        refine ⟨∅, by simp, ?_⟩
        simp [hx_zero, faceBoundaryChain]
    | succ n ih =>
        intro x hx hcard
        by_cases hzero : support₁ x = ∅
        · have hx_zero : x = zeroChain := data.tight hx hzero
          refine ⟨∅, by simp, ?_⟩
          simp [hx_zero, faceBoundaryChain]
        · rcases data.peel_sum hx hzero with ⟨S₀, _hne, hS₀, x', hx', hx_eq, hlt⟩
          have hcard' : Finset.card (support₁ x') ≤ n :=
            (Nat.lt_succ_iff).1 (lt_of_lt_of_le hlt hcard)
          have hx'_span := ih hx' hcard'
          rw [hx_eq]
          exact faceBoundarySpan_add_sum
            (γ := data.gamma) (faces := data.internalFaces) hx'_span hS₀
  intro x hx
  exact peel_induction (Finset.card (support₁ x)) hx le_rfl

/-- The face-boundary span generated by the allowed internal faces stays inside
the zero-boundary set. -/
theorem faceBoundarySpan_subset_zeroBoundarySet
    (data : BoundaryChainAggregatePeelData V E) :
    faceBoundarySpan data.gamma data.internalFaces ⊆ data.zero.zeroBoundarySet := by
  intro x hx
  rcases hx with ⟨S, hS, rfl⟩
  exact data.zero.sum_mem_zero S (fun f => faceBoundaryChain data.gamma f)
    (fun f hf => data.boundary_mem_zero (hS hf))

/-- An aggregate peel certificate identifies the zero-boundary chains exactly
with the finite span of the available face-boundary chains. -/
theorem zeroBoundarySet_eq_faceBoundarySpan
    (data : BoundaryChainAggregatePeelData V E) :
    data.zero.zeroBoundarySet = faceBoundarySpan data.gamma data.internalFaces :=
  Set.Subset.antisymm data.zeroBoundarySet_subset_faceBoundarySpan
    data.faceBoundarySpan_subset_zeroBoundarySet

end BoundaryChainAggregatePeelData

end Mettapedia.GraphTheory.FourColor
