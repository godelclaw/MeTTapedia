import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition
import Mettapedia.GraphTheory.FourColor.ColorAlgebra
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedInterfaceCountLaw

/-!
# The physical gluing bijection

Serial gluing identifies the output ports of one tangle with the input ports of
the next, deletes the two temporary stub endpoints, and joins the underlying
half-edges into one seam edge.  This file proves that restriction and gluing are
inverse operations on proper nonzero Tait colourings, which is the bijection the
bounded-interface Count law consumes.

**Representation.**  The in-tree open-tangle model is `OpenTangleData`, a dart
carrier whose interior darts are paired by an involution and whose boundary darts
are unpaired dangling incidences.  That is exactly the port model wanted here,
except for two fields the bijection never reads: the vertex rotation and its
distinguished root.  Colourings do not see a rotation, and a serial composite
would have to invent one, so this file works with the exact reduct -- the same
data with those two fields dropped -- and supplies the forgetful map from
`OpenTangleData`.  Nothing is duplicated and no rotation is fabricated.

A port is a single dangling incidence, so its colour *is* the boundary letter.
When two ports are identified the seam edge acquires two halves, one on each
side, and a colouring of the composite gives both halves the same colour.  That
common colour is the middle word, and it is the whole content of the bijection.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PortTangleGluing

universe u

open GoertzelV24OpenTangleComposition

/-- An open tangle presented by darts, with an ordered port interface.  This is
`OpenTangleData` without the vertex rotation and its root, which the colouring
bijection never reads. -/
structure PortTangle (V I P : Type*) where
  /-- The vertex carrying each dart. -/
  vert : I ⊕ P → V
  /-- The edge involution on interior darts. -/
  alpha : I → I
  alpha_involutive : ∀ d, alpha (alpha d) = d
  alpha_fixfree : ∀ d, alpha d ≠ d
  /-- An interior edge joins two different vertices. -/
  no_self_loops : ∀ d, vert (Sum.inl d) ≠ vert (Sum.inl (alpha d))

/-- Every in-tree open tangle is a port tangle: forget the rotation and root. -/
def ofOpenTangleData {V I B : Type*} (data : OpenTangleData V I B) :
    PortTangle V I B where
  vert := data.vertOf
  alpha := data.interiorAlpha
  alpha_involutive := data.interiorAlpha_involutive
  alpha_fixfree := data.interiorAlpha_fixfree
  no_self_loops := data.interior_no_self_loops

namespace PortTangle

variable {V I P : Type*}

/-- A colouring assigns a colour to every dart and gives the two halves of an
interior edge the same colour. -/
structure Coloring (T : PortTangle V I P) where
  /-- The colour of each dart. -/
  color : I ⊕ P → Color
  /-- The two halves of an interior edge agree. -/
  invariant : ∀ d : I, color (Sum.inl (T.alpha d)) = color (Sum.inl d)

theorem Coloring.ext' {T : PortTangle V I P} {c d : Coloring T}
    (h : c.color = d.color) : c = d := by
  cases c; cases d; simp_all

/-- A proper nonzero Tait colouring: every colour is a genuine Tait colour, and
two different darts at one vertex carry different colours.  Distinct darts at a
vertex belong to distinct edges, because an interior edge has its two halves at
different vertices. -/
def IsProper {T : PortTangle V I P} (c : Coloring T) : Prop :=
  (∀ d, c.color d ≠ 0) ∧
    ∀ d e, T.vert d = T.vert e → d ≠ e → c.color d ≠ c.color e

/-- The boundary word: the colour read off at each port. -/
def word {T : PortTangle V I P} (c : Coloring T) : P → Color :=
  fun p => c.color (Sum.inr p)

/-- The proper colourings realizing a given boundary word. -/
def Col (T : PortTangle V I P) (x : P → Color) : Type _ :=
  { c : Coloring T // IsProper c ∧ word c = x }

end PortTangle

open PortTangle

/-! ## Serial gluing -/

section Series

variable {V W I K X J Z : Type u}
  (T₁ : PortTangle V I (X ⊕ J)) (T₂ : PortTangle W K (J ⊕ Z))

/-- Vertices of the serial composite.  The two halves of a seam edge sit on the
two sides, at the vertices that carried the identified ports. -/
def seriesVert : ((I ⊕ K) ⊕ (J ⊕ J)) ⊕ (X ⊕ Z) → V ⊕ W
  | Sum.inl (Sum.inl (Sum.inl i)) => Sum.inl (T₁.vert (Sum.inl i))
  | Sum.inl (Sum.inl (Sum.inr k)) => Sum.inr (T₂.vert (Sum.inl k))
  | Sum.inl (Sum.inr (Sum.inl j)) => Sum.inl (T₁.vert (Sum.inr (Sum.inr j)))
  | Sum.inl (Sum.inr (Sum.inr j)) => Sum.inr (T₂.vert (Sum.inr (Sum.inl j)))
  | Sum.inr (Sum.inl x) => Sum.inl (T₁.vert (Sum.inr (Sum.inl x)))
  | Sum.inr (Sum.inr z) => Sum.inr (T₂.vert (Sum.inr (Sum.inr z)))

/-- The edge involution of the composite: old interior edges keep theirs, and
the two halves of each seam edge are paired. -/
def seriesAlpha : (I ⊕ K) ⊕ (J ⊕ J) → (I ⊕ K) ⊕ (J ⊕ J)
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (T₁.alpha i))
  | Sum.inl (Sum.inr k) => Sum.inl (Sum.inr (T₂.alpha k))
  | Sum.inr (Sum.inl j) => Sum.inr (Sum.inr j)
  | Sum.inr (Sum.inr j) => Sum.inr (Sum.inl j)

/-- **The serial composite.**  The stub endpoints are gone: a former port is now
one half of a genuine interior edge. -/
def series : PortTangle (V ⊕ W) ((I ⊕ K) ⊕ (J ⊕ J)) (X ⊕ Z) where
  vert := seriesVert T₁ T₂
  alpha := seriesAlpha T₁ T₂
  alpha_involutive := by
    rintro ((i | k) | (j | j)) <;>
      simp [seriesAlpha, T₁.alpha_involutive, T₂.alpha_involutive]
  alpha_fixfree := by
    rintro ((i | k) | (j | j)) <;>
      simp [seriesAlpha, T₁.alpha_fixfree, T₂.alpha_fixfree]
  no_self_loops := by
    rintro ((i | k) | (j | j))
    · simpa [seriesVert, seriesAlpha] using T₁.no_self_loops i
    · simpa [seriesVert, seriesAlpha] using T₂.no_self_loops k
    · simp [seriesVert, seriesAlpha]
    · simp [seriesVert, seriesAlpha]

/-- The first side, sitting inside the composite: its ports on `J` become the
left halves of the seam edges. -/
def emb₁ : I ⊕ (X ⊕ J) → ((I ⊕ K) ⊕ (J ⊕ J)) ⊕ (X ⊕ Z)
  | Sum.inl i => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl x)
  | Sum.inr (Sum.inr j) => Sum.inl (Sum.inr (Sum.inl j))

/-- The second side, sitting inside the composite. -/
def emb₂ : K ⊕ (J ⊕ Z) → ((I ⊕ K) ⊕ (J ⊕ J)) ⊕ (X ⊕ Z)
  | Sum.inl k => Sum.inl (Sum.inl (Sum.inr k))
  | Sum.inr (Sum.inl j) => Sum.inl (Sum.inr (Sum.inr j))
  | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)

@[simp] theorem vert_emb₁ (d : I ⊕ (X ⊕ J)) :
    seriesVert T₁ T₂ (emb₁ (K := K) (Z := Z) d) = Sum.inl (T₁.vert d) := by
  rcases d with i | (x | j) <;> rfl

@[simp] theorem vert_emb₂ (d : K ⊕ (J ⊕ Z)) :
    seriesVert T₁ T₂ (emb₂ (I := I) (X := X) d) = Sum.inr (T₂.vert d) := by
  rcases d with k | (j | z) <;> rfl

theorem emb₁_injective : Function.Injective (emb₁ (I := I) (K := K) (X := X) (J := J) (Z := Z)) := by
  rintro (i | (x | j)) (i' | (x' | j')) h <;> simp_all [emb₁]

theorem emb₂_injective : Function.Injective (emb₂ (I := I) (K := K) (X := X) (J := J) (Z := Z)) := by
  rintro (k | (j | z)) (k' | (j' | z')) h <;> simp_all [emb₂]

/-- Every composite dart comes from one of the two sides. -/
theorem emb_surjective (d : ((I ⊕ K) ⊕ (J ⊕ J)) ⊕ (X ⊕ Z)) :
    (∃ a, emb₁ (K := K) (Z := Z) a = d) ∨ (∃ b, emb₂ (I := I) (X := X) b = d) := by
  rcases d with ((i | k) | (j | j)) | (x | z)
  · exact Or.inl ⟨Sum.inl i, rfl⟩
  · exact Or.inr ⟨Sum.inl k, rfl⟩
  · exact Or.inl ⟨Sum.inr (Sum.inr j), rfl⟩
  · exact Or.inr ⟨Sum.inr (Sum.inl j), rfl⟩
  · exact Or.inl ⟨Sum.inr (Sum.inl x), rfl⟩
  · exact Or.inr ⟨Sum.inr (Sum.inr z), rfl⟩

/-- A dart lying over the first side comes from the first side. -/
theorem exists_emb₁_of_vert_inl {d : ((I ⊕ K) ⊕ (J ⊕ J)) ⊕ (X ⊕ Z)} {v : V}
    (h : seriesVert T₁ T₂ d = Sum.inl v) : ∃ a, emb₁ (K := K) (Z := Z) a = d := by
  rcases d with ((i | k) | (j | j)) | (x | z)
  · exact ⟨Sum.inl i, rfl⟩
  · simp [seriesVert] at h
  · exact ⟨Sum.inr (Sum.inr j), rfl⟩
  · simp [seriesVert] at h
  · exact ⟨Sum.inr (Sum.inl x), rfl⟩
  · simp [seriesVert] at h

/-- A dart lying over the second side comes from the second side. -/
theorem exists_emb₂_of_vert_inr {d : ((I ⊕ K) ⊕ (J ⊕ J)) ⊕ (X ⊕ Z)} {w : W}
    (h : seriesVert T₁ T₂ d = Sum.inr w) : ∃ b, emb₂ (I := I) (X := X) b = d := by
  rcases d with ((i | k) | (j | j)) | (x | z)
  · simp [seriesVert] at h
  · exact ⟨Sum.inl k, rfl⟩
  · simp [seriesVert] at h
  · exact ⟨Sum.inr (Sum.inl j), rfl⟩
  · simp [seriesVert] at h
  · exact ⟨Sum.inr (Sum.inr z), rfl⟩

end Series

/-! ## Restriction and gluing -/

section Restrict

variable {V W I K X J Z : Type u}
  (T₁ : PortTangle V I (X ⊕ J)) (T₂ : PortTangle W K (J ⊕ Z))

/-- Restrict a composite colouring to the first side.  Its `J`-ports read the
seam colour. -/
def restrict₁ (c : Coloring (series T₁ T₂)) : Coloring T₁ where
  color := fun d => c.color (emb₁ (K := K) (Z := Z) d)
  invariant := fun d => c.invariant (Sum.inl (Sum.inl d))

/-- Restrict a composite colouring to the second side. -/
def restrict₂ (c : Coloring (series T₁ T₂)) : Coloring T₂ where
  color := fun d => c.color (emb₂ (I := I) (X := X) d)
  invariant := fun d => c.invariant (Sum.inl (Sum.inr d))

/-- The middle word: the colour of each seam edge. -/
def mid (c : Coloring (series T₁ T₂)) : J → Color :=
  fun j => c.color (Sum.inl (Sum.inr (Sum.inl j)))

/-- The first side reads the middle word at its `J`-ports. -/
theorem word_restrict₁ (c : Coloring (series T₁ T₂)) (j : J) :
    word (restrict₁ T₁ T₂ c) (Sum.inr j) = mid T₁ T₂ c j := rfl

/-- **The seam agreement.**  The second side reads the *same* middle word,
because the two halves of a seam edge are one edge. -/
theorem word_restrict₂ (c : Coloring (series T₁ T₂)) (j : J) :
    word (restrict₂ T₁ T₂ c) (Sum.inl j) = mid T₁ T₂ c j :=
  c.invariant (Sum.inr (Sum.inl j))

/-- Glue two colourings that agree on the middle word. -/
def glueColoring (c₁ : Coloring T₁) (c₂ : Coloring T₂) : Coloring (series T₁ T₂) where
  color
    | Sum.inl (Sum.inl (Sum.inl i)) => c₁.color (Sum.inl i)
    | Sum.inl (Sum.inl (Sum.inr k)) => c₂.color (Sum.inl k)
    | Sum.inl (Sum.inr (Sum.inl j)) => c₁.color (Sum.inr (Sum.inr j))
    | Sum.inl (Sum.inr (Sum.inr j)) => c₁.color (Sum.inr (Sum.inr j))
    | Sum.inr (Sum.inl x) => c₁.color (Sum.inr (Sum.inl x))
    | Sum.inr (Sum.inr z) => c₂.color (Sum.inr (Sum.inr z))
  invariant := by
    rintro ((i | k) | (j | j))
    · exact c₁.invariant i
    · exact c₂.invariant k
    · rfl
    · rfl

/-! ## Properness is exactly properness on both sides -/

theorem isProper_restrict₁ {c : Coloring (series T₁ T₂)} (h : IsProper c) :
    IsProper (restrict₁ T₁ T₂ c) := by
  refine ⟨fun d => h.1 _, fun d e hvert hne => ?_⟩
  refine h.2 _ _ ?_ (fun hcon => hne (emb₁_injective hcon))
  show seriesVert T₁ T₂ _ = seriesVert T₁ T₂ _
  rw [vert_emb₁, vert_emb₁, hvert]

theorem isProper_restrict₂ {c : Coloring (series T₁ T₂)} (h : IsProper c) :
    IsProper (restrict₂ T₁ T₂ c) := by
  refine ⟨fun d => h.1 _, fun d e hvert hne => ?_⟩
  refine h.2 _ _ ?_ (fun hcon => hne (emb₂_injective hcon))
  show seriesVert T₁ T₂ _ = seriesVert T₁ T₂ _
  rw [vert_emb₂, vert_emb₂, hvert]

/-- **The glued colouring is proper exactly when both restrictions are.**  Every
composite vertex belongs to one side and carries that side's darts, with the seam
half standing in for the identified port. -/
theorem isProper_of_restricts {c : Coloring (series T₁ T₂)}
    (h₁ : IsProper (restrict₁ T₁ T₂ c)) (h₂ : IsProper (restrict₂ T₁ T₂ c)) :
    IsProper c := by
  constructor
  · intro d
    rcases emb_surjective (I := I) (K := K) (X := X) (J := J) (Z := Z) d with
      ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact h₁.1 a
    · exact h₂.1 b
  · intro d e hvert hne
    have hvert' : seriesVert T₁ T₂ d = seriesVert T₁ T₂ e := hvert
    cases hd : seriesVert T₁ T₂ d with
    | inl v =>
        obtain ⟨a, rfl⟩ := exists_emb₁_of_vert_inl T₁ T₂ hd
        have he : seriesVert T₁ T₂ e = Sum.inl v := by rw [← hvert']; exact hd
        obtain ⟨a', rfl⟩ := exists_emb₁_of_vert_inl T₁ T₂ he
        refine h₁.2 a a' ?_ (fun hcon => hne (by rw [hcon]))
        have := hvert'
        rw [vert_emb₁, vert_emb₁] at this
        simpa using this
    | inr w =>
        obtain ⟨b, rfl⟩ := exists_emb₂_of_vert_inr T₁ T₂ hd
        have he : seriesVert T₁ T₂ e = Sum.inr w := by rw [← hvert']; exact hd
        obtain ⟨b', rfl⟩ := exists_emb₂_of_vert_inr T₁ T₂ he
        refine h₂.2 b b' ?_ (fun hcon => hne (by rw [hcon]))
        have := hvert'
        rw [vert_emb₂, vert_emb₂] at this
        simpa using this

end Restrict

/-! ## C1: restriction and gluing are inverse -/

section Bijection

variable {V W I K X J Z : Type u}
  (T₁ : PortTangle V I (X ⊕ J)) (T₂ : PortTangle W K (J ⊕ Z))

theorem restrict₁_glueColoring (c₁ : Coloring T₁) (c₂ : Coloring T₂) :
    restrict₁ T₁ T₂ (glueColoring T₁ T₂ c₁ c₂) = c₁ := by
  refine Coloring.ext' ?_
  funext d
  rcases d with i | (x | j) <;> rfl

theorem restrict₂_glueColoring (c₁ : Coloring T₁) (c₂ : Coloring T₂)
    (hmid : ∀ j : J, c₁.color (Sum.inr (Sum.inr j)) = c₂.color (Sum.inr (Sum.inl j))) :
    restrict₂ T₁ T₂ (glueColoring T₁ T₂ c₁ c₂) = c₂ := by
  refine Coloring.ext' ?_
  funext d
  rcases d with k | (j | z)
  · rfl
  · exact hmid j
  · rfl

theorem glueColoring_restrict (c : Coloring (series T₁ T₂)) :
    glueColoring T₁ T₂ (restrict₁ T₁ T₂ c) (restrict₂ T₁ T₂ c) = c := by
  refine Coloring.ext' ?_
  funext d
  rcases d with ((i | k) | (j | j)) | (x | z)
  · rfl
  · rfl
  · rfl
  · exact (c.invariant (Sum.inr (Sum.inl j))).symm
  · rfl
  · rfl

/-- **The physical gluing bijection.**  A proper colouring of the serial
composite is exactly a middle word together with a proper colouring of each side
realizing it.  Restriction and gluing are mutually inverse.

This is (C1); the Count law's matrix convolution and Boolean support composition
follow from it purely algebraically. -/
def gluingEquiv (x : X → Color) (z : Z → Color) :
    Col (series T₁ T₂) (Sum.elim x z) ≃
      Σ y : J → Color, Col T₁ (Sum.elim x y) × Col T₂ (Sum.elim y z) where
  toFun c :=
    ⟨mid T₁ T₂ c.1,
      ⟨⟨restrict₁ T₁ T₂ c.1, isProper_restrict₁ T₁ T₂ c.2.1, by
        funext d
        rcases d with x' | j
        · exact congrFun c.2.2 (Sum.inl x')
        · rfl⟩,
      ⟨restrict₂ T₁ T₂ c.1, isProper_restrict₂ T₁ T₂ c.2.1, by
        funext d
        rcases d with j | z'
        · exact word_restrict₂ T₁ T₂ c.1 j
        · exact congrFun c.2.2 (Sum.inr z')⟩⟩⟩
  invFun p :=
    ⟨glueColoring T₁ T₂ p.2.1.1 p.2.2.1, by
      refine isProper_of_restricts T₁ T₂ ?_ ?_
      · rw [restrict₁_glueColoring]; exact p.2.1.2.1
      · rw [restrict₂_glueColoring]
        · exact p.2.2.2.1
        · intro j
          exact (congrFun p.2.1.2.2 (Sum.inr j)).trans
            (congrFun p.2.2.2.2 (Sum.inl j)).symm, by
      funext d
      rcases d with x' | z'
      · exact congrFun p.2.1.2.2 (Sum.inl x')
      · exact congrFun p.2.2.2.2 (Sum.inr z')⟩
  left_inv c := by
    apply Subtype.ext
    exact glueColoring_restrict T₁ T₂ c.1
  right_inv p := by
    obtain ⟨y, ⟨c₁, h₁, w₁⟩, ⟨c₂, h₂, w₂⟩⟩ := p
    have hmidj : ∀ j : J, c₁.color (Sum.inr (Sum.inr j)) = c₂.color (Sum.inr (Sum.inl j)) :=
      fun j => (congrFun w₁ (Sum.inr j)).trans (congrFun w₂ (Sum.inl j)).symm
    have hmid : mid T₁ T₂ (glueColoring T₁ T₂ c₁ c₂) = y := by
      funext j
      exact congrFun w₁ (Sum.inr j)
    subst hmid
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and]
    exact ⟨Subtype.ext (restrict₁_glueColoring T₁ T₂ c₁ c₂),
      Subtype.ext (restrict₂_glueColoring T₁ T₂ c₁ c₂ hmidj)⟩

/-! ## Handing the bijection to the Count law -/

/-- **(C1) in the form the bounded-interface Count law consumes.**  Everything
downstream -- the matrix convolution, the Boolean support composition, block
deletion under a repeated support, and port relabelling -- is already proved
there from this one input, so nothing algebraic is redone here. -/
theorem gluingEquivalence_series :
    GoertzelV24BoundedInterfaceCountLaw.GluingEquivalence
      (fun (x : X → Color) (y : J → Color) => Col T₁ (Sum.elim x y))
      (fun (y : J → Color) (z : Z → Color) => Col T₂ (Sum.elim y z))
      (fun (x : X → Color) (z : Z → Color) => Col (series T₁ T₂) (Sum.elim x z)) :=
  fun x z => ⟨gluingEquiv T₁ T₂ x z⟩

/-- The count matrix of a serial composite is the convolution of the two sides'
count matrices, over the middle words.  This is `(C2)`, obtained from `(C1)` by
the Count law with no further geometric input. -/
theorem countMatrix_series [Fintype (J → Color)]
    [∀ (x : X → Color) (y : J → Color), Fintype (Col T₁ (Sum.elim x y))]
    [∀ (y : J → Color) (z : Z → Color), Fintype (Col T₂ (Sum.elim y z))]
    [∀ (x : X → Color) (z : Z → Color), Fintype (Col (series T₁ T₂) (Sum.elim x z))] :
    (GoertzelV24BoundedInterfaceCountLaw.countMatrix
      (Col := fun (x : X → Color) (z : Z → Color) =>
        Col (series T₁ T₂) (Sum.elim x z))) =
      GoertzelV24BoundedInterfaceCountLaw.matMul
        (GoertzelV24BoundedInterfaceCountLaw.countMatrix
          (Col := fun (x : X → Color) (y : J → Color) => Col T₁ (Sum.elim x y)))
        (GoertzelV24BoundedInterfaceCountLaw.countMatrix
          (Col := fun (y : J → Color) (z : Z → Color) => Col T₂ (Sum.elim y z))) :=
  GoertzelV24BoundedInterfaceCountLaw.countMatrix_eq_matMul (gluingEquivalence_series T₁ T₂)

end Bijection

end GoertzelV24PortTangleGluing

end Mettapedia.GraphTheory.FourColor
