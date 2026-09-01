import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.Compositional.BoundaryColorOrbit

/-!
# Colour-orbit classes on a five-cycle boundary

The two boundary classes in Birkhoff's short-five-cycle argument are the
cyclic translates of the patterns `(3,1,1)` and `(2,1,1,1)`, modulo one
global renaming of the three nonzero Tait colours.  This file gives those
classes semantic names and proves that membership in the same class is
exactly enough to align two nonzero boundary words by a zero-fixing colour
equivalence.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FiveCycleColorClass

open BoundaryColorOrbit

/-- Enumerate zero followed by one ordered Tait triple. -/
def taitTripleEnumeration (a b c : Color) : Fin 4 → Color
  | 0 => 0
  | 1 => a
  | 2 => b
  | 3 => c

/-- An ordered Tait triple, together with zero, is all of `Color`. -/
noncomputable def taitTripleEquiv
    {a b c : Color} (triple : IsTaitColorTriple a b c) : Fin 4 ≃ Color := by
  apply Equiv.ofBijective (taitTripleEnumeration a b c)
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, by decide⟩
  intro first second heq
  rcases triple with ⟨ha0, hb0, hc0, hab, hac, hbc⟩
  fin_cases first <;> fin_cases second <;>
    simp [taitTripleEnumeration, ha0, hb0, hc0, ha0.symm, hb0.symm, hc0.symm,
      hab, hac, hbc,
      hab.symm, hac.symm, hbc.symm] at heq ⊢

/-- A zero-fixing colour equivalence carrying one ordered Tait triple to
another. -/
noncomputable def equivalenceBetweenTaitTriples
    {a b c x y z : Color}
    (source : IsTaitColorTriple a b c)
    (target : IsTaitColorTriple x y z) : Color ≃ Color :=
  (taitTripleEquiv source).symm.trans (taitTripleEquiv target)

@[simp]
theorem equivalenceBetweenTaitTriples_zero
    {a b c x y z : Color}
    (source : IsTaitColorTriple a b c)
    (target : IsTaitColorTriple x y z) :
    equivalenceBetweenTaitTriples source target 0 = 0 := by
  change taitTripleEquiv target ((taitTripleEquiv source).symm 0) = 0
  rw [← show taitTripleEquiv source (0 : Fin 4) = 0 by rfl,
    Equiv.symm_apply_apply]
  rfl

@[simp]
theorem equivalenceBetweenTaitTriples_first
    {a b c x y z : Color}
    (source : IsTaitColorTriple a b c)
    (target : IsTaitColorTriple x y z) :
    equivalenceBetweenTaitTriples source target a = x := by
  change taitTripleEquiv target ((taitTripleEquiv source).symm a) = x
  have hsource : (taitTripleEquiv source).symm a = (1 : Fin 4) := by
    apply (taitTripleEquiv source).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hsource]
  rfl

@[simp]
theorem equivalenceBetweenTaitTriples_second
    {a b c x y z : Color}
    (source : IsTaitColorTriple a b c)
    (target : IsTaitColorTriple x y z) :
    equivalenceBetweenTaitTriples source target b = y := by
  change taitTripleEquiv target ((taitTripleEquiv source).symm b) = y
  have hsource : (taitTripleEquiv source).symm b = (2 : Fin 4) := by
    apply (taitTripleEquiv source).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hsource]
  rfl

@[simp]
theorem equivalenceBetweenTaitTriples_third
    {a b c x y z : Color}
    (source : IsTaitColorTriple a b c)
    (target : IsTaitColorTriple x y z) :
    equivalenceBetweenTaitTriples source target c = z := by
  change taitTripleEquiv target ((taitTripleEquiv source).symm c) = z
  have hsource : (taitTripleEquiv source).symm c = (3 : Fin 4) := by
    apply (taitTripleEquiv source).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hsource]
  rfl

/-- Colour relabelling commutes with cyclic rotation of a five-boundary
word. -/
theorem map_rotateBoundaryWordN
    (relabel : Color → Color) (steps : Nat) (word : CAP5BoundaryWord) :
    cap5MapBoundaryWord relabel (cap5RotateBoundaryWordN steps word) =
      cap5RotateBoundaryWordN steps (cap5MapBoundaryWord relabel word) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [cap5RotateBoundaryWordN]
      have hcommute : cap5MapBoundaryWord relabel
          (cap5RotateBoundaryWord (cap5RotateBoundaryWordN steps word)) =
          cap5RotateBoundaryWord
            (cap5MapBoundaryWord relabel (cap5RotateBoundaryWordN steps word)) := by
        funext index
        fin_cases index <;> rfl
      rw [hcommute, ih]

/-- The `P_i` orbit in Birkhoff's proof: three consecutive boundary edges
have one colour and the remaining two have the other two colours. -/
def Primary (index : Fin 5) (word : CAP5BoundaryWord) : Prop :=
  ∃ a b c : Color, IsTaitColorTriple a b c ∧
    word = cap5RotateBoundaryWordN index.1 (cap5BoundaryWord311Of a b c)

/-- The `Q_i` orbit in Birkhoff's proof: the majority colour occupies the
first, second, and fourth positions of the rotated pattern. -/
def Secondary (index : Fin 5) (word : CAP5BoundaryWord) : Prop :=
  ∃ a b c : Color, IsTaitColorTriple a b c ∧
    word = cap5RotateBoundaryWordN index.1 (cap5BoundaryWord2111Of a b c)

/-- Forget the nonzero proofs in an exact physical boundary word. -/
def colorsOfBoundaryWord
    (word : Fin 5 → {color : Color // color ≠ 0}) : CAP5BoundaryWord :=
  fun index => (word index).1

private theorem map_boundaryWord311Of
    {a b c x y z : Color}
    (source : IsTaitColorTriple a b c)
    (target : IsTaitColorTriple x y z) :
    cap5MapBoundaryWord (equivalenceBetweenTaitTriples source target)
        (cap5BoundaryWord311Of a b c) =
      cap5BoundaryWord311Of x y z := by
  funext index
  fin_cases index <;> simp [cap5MapBoundaryWord, cap5BoundaryWord311Of]

private theorem map_boundaryWord2111Of
    {a b c x y z : Color}
    (source : IsTaitColorTriple a b c)
    (target : IsTaitColorTriple x y z) :
    cap5MapBoundaryWord (equivalenceBetweenTaitTriples source target)
        (cap5BoundaryWord2111Of a b c) =
      cap5BoundaryWord2111Of x y z := by
  funext index
  fin_cases index <;> simp [cap5MapBoundaryWord, cap5BoundaryWord2111Of]

/-- Two nonzero words in the same `P_i` class differ only by a global
zero-fixing colour equivalence. -/
theorem equivalent_of_primary
    {left right : Fin 5 → {color : Color // color ≠ 0}}
    {index : Fin 5}
    (hleft : Primary index (colorsOfBoundaryWord left))
    (hright : Primary index (colorsOfBoundaryWord right)) :
    BoundaryColorOrbit.Equivalent left right := by
  rcases hleft with ⟨a, b, c, hsource, hleft⟩
  rcases hright with ⟨x, y, z, htarget, hright⟩
  let relabel := equivalenceBetweenTaitTriples hsource htarget
  refine ⟨relabel, equivalenceBetweenTaitTriples_zero hsource htarget, ?_⟩
  funext coordinate
  apply Subtype.ext
  change relabel (left coordinate).1 = (right coordinate).1
  have hleftAt := congrFun hleft coordinate
  have hrightAt := congrFun hright coordinate
  change (left coordinate).1 = _ at hleftAt
  change (right coordinate).1 = _ at hrightAt
  rw [hleftAt, hrightAt]
  have hmap := congrFun
    (map_rotateBoundaryWordN relabel index.1 (cap5BoundaryWord311Of a b c))
    coordinate
  rw [map_boundaryWord311Of hsource htarget] at hmap
  exact hmap

/-- Two nonzero words in the same `Q_i` class differ only by a global
zero-fixing colour equivalence. -/
theorem equivalent_of_secondary
    {left right : Fin 5 → {color : Color // color ≠ 0}}
    {index : Fin 5}
    (hleft : Secondary index (colorsOfBoundaryWord left))
    (hright : Secondary index (colorsOfBoundaryWord right)) :
    BoundaryColorOrbit.Equivalent left right := by
  rcases hleft with ⟨a, b, c, hsource, hleft⟩
  rcases hright with ⟨x, y, z, htarget, hright⟩
  let relabel := equivalenceBetweenTaitTriples hsource htarget
  refine ⟨relabel, equivalenceBetweenTaitTriples_zero hsource htarget, ?_⟩
  funext coordinate
  apply Subtype.ext
  change relabel (left coordinate).1 = (right coordinate).1
  have hleftAt := congrFun hleft coordinate
  have hrightAt := congrFun hright coordinate
  change (left coordinate).1 = _ at hleftAt
  change (right coordinate).1 = _ at hrightAt
  rw [hleftAt, hrightAt]
  have hmap := congrFun
    (map_rotateBoundaryWordN relabel index.1 (cap5BoundaryWord2111Of a b c))
    coordinate
  rw [map_boundaryWord2111Of hsource htarget] at hmap
  exact hmap

end FiveCycleColorClass

end Mettapedia.GraphTheory.FourColor.Compositional
