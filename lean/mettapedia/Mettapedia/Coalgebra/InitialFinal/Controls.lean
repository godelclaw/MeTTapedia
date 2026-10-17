import Mettapedia.Coalgebra.InitialFinal.Recursive
import Mathlib.Data.QPF.Univariate.Basic

/-!
# Controls for the meeting of initial algebras and final coalgebras

Preservation of monomorphisms does not force a recursive coalgebra to be
well-founded. The coalgebra below is the one in Adámek, Milius, Moss, and
Sousa, *Well-pointed coalgebras*, Example 2.34: its carrier is a two-element
set, its structure is a constant off-diagonal pair, every algebra receives
exactly one solution, and the empty subset is inductive.

The same paper's Example 2.47 separates a functor from the extension that
makes its value on the empty type match its value on a singleton. A one-point
coalgebra is not well-founded for the original functor, and it is well-founded
for that two-point extension.

Uniformity of a quotient presentation is not necessary for injectivity of
`QPF.Cofix.corec QPF.Fix.dest`. The constant one-point functor below is
presented by a childless shape and a shape with one ignored child. Those
shapes abstract to the same point and have different child images, so the
presentation is not uniform, and the support of the point is not that child
image. Every tree is identified with the childless tree, so the meeting map
remains injective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Coalgebra.InitialFinal

open CategoryTheory
open CategoryTheory.Endofunctor
open scoped Classical

universe u

/-- A two-element type in the working universe. -/
inductive Bit : Type u where
  | ff
  | tt

theorem Bit.ff_ne_tt : (Bit.ff : Bit) ≠ Bit.tt := by
  intro h
  cases h

/-- Off-diagonal pairs, together with one diagonal point. -/
inductive OffDiagonal (X : Type u) where
  | diagonal
  | pair (x y : X) (distinct : x ≠ y)

namespace OffDiagonal

noncomputable def map {X Y : Type u} (f : X → Y) : OffDiagonal X → OffDiagonal Y
  | diagonal => diagonal
  | pair x y _ =>
      if images : f x = f y then diagonal else pair (f x) (f y) images

theorem id_map {X : Type u} (shape : OffDiagonal X) : map id shape = shape := by
  cases shape with
  | diagonal => rfl
  | pair x y distinct =>
      simp only [map, id_eq]
      rw [dif_neg distinct]

theorem comp_map {X Y Z : Type u} (f : X → Y) (g : Y → Z) (shape : OffDiagonal X) :
    map (g ∘ f) shape = map g (map f shape) := by
  cases shape with
  | diagonal => rfl
  | pair x y distinct =>
      simp only [map, Function.comp_apply]
      by_cases hxy : f x = f y
      · have hgf : g (f x) = g (f y) := congrArg g hxy
        rw [dif_pos hxy, dif_pos hgf]
      · rw [dif_neg hxy]

theorem map_diagonal {X Y : Type u} (f : X → Y) :
    map f diagonal = diagonal := by
  unfold map
  rfl

theorem map_pair_collapse {X Y : Type u} (f : X → Y) (x y : X) (hxy : x ≠ y)
    (himg : f x = f y) :
    map f (pair x y hxy) = diagonal := by
  simp only [map, dif_pos himg]

theorem map_pair_keep {X Y : Type u} (f : X → Y) (x y : X) (hxy : x ≠ y)
    (himg : f x ≠ f y) :
    map f (pair x y hxy) = pair (f x) (f y) himg := by
  simp only [map, dif_neg himg]

end OffDiagonal

noncomputable instance : Functor OffDiagonal where
  map := OffDiagonal.map

instance : LawfulFunctor OffDiagonal where
  map_const := rfl
  id_map := OffDiagonal.id_map
  comp_map := OffDiagonal.comp_map

/-- The category endofunctor of `OffDiagonal`. -/
noncomputable def offDiagonalFunctor : Type u ⥤ Type u := ofTypeFunctor OffDiagonal

theorem offDiagonal_map_apply {X Y : Type u} (f : X → Y) (shape : OffDiagonal X) :
    offDiagonalFunctor.map (↾ f) shape = OffDiagonal.map f shape := by
  simp only [offDiagonalFunctor, ofTypeFunctor_map, TypeCat.ofHom, TypeCat.Hom.hom,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
  rfl

/-- A two-point coalgebra whose structure is the constant off-diagonal pair. -/
def twoPoint : Coalgebra offDiagonalFunctor where
  V := Bit
  str := ↾ fun _ => OffDiagonal.pair Bit.ff Bit.tt Bit.ff_ne_tt

theorem twoPoint_solution (A : Algebra offDiagonalFunctor) :
    IsSolution twoPoint A (↾ fun _ : Bit => A.str OffDiagonal.diagonal) ∧
      ∀ h' : Bit ⟶ A.a, IsSolution twoPoint A h' →
        h' = ↾ fun _ : Bit => A.str OffDiagonal.diagonal := by
  let h : Bit ⟶ A.a := ↾ fun _ => A.str OffDiagonal.diagonal
  refine ⟨?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro a
    have happly := offDiagonal_map_apply (h : Bit → A.a)
      (OffDiagonal.pair Bit.ff Bit.tt Bit.ff_ne_tt)
    have hcollapse := OffDiagonal.map_pair_collapse (h : Bit → A.a) Bit.ff Bit.tt
      Bit.ff_ne_tt rfl
    simp only [CategoryTheory.comp_apply, twoPoint] 
    rw (config := { transparency := .default }) [happly, hcollapse]
    rfl
  · intro h' hs'
    apply ConcreteCategory.hom_ext
    intro a
    have happ := ConcreteCategory.congr_hom hs' a
    simp only [CategoryTheory.comp_apply, twoPoint] at happ
    have hsame : (h' : Bit → A.a) Bit.ff = (h' : Bit → A.a) Bit.tt := by
      have hfalse := ConcreteCategory.congr_hom hs' Bit.ff
      have htrue := ConcreteCategory.congr_hom hs' Bit.tt
      simp only [CategoryTheory.comp_apply, twoPoint] at hfalse htrue
      by_cases hneq : (h' : Bit → A.a) Bit.ff = (h' : Bit → A.a) Bit.tt
      · exact hneq
      · have hleft := offDiagonal_map_apply (h' : Bit → A.a)
          (OffDiagonal.pair Bit.ff Bit.tt Bit.ff_ne_tt)
        have hkeep := OffDiagonal.map_pair_keep (h' : Bit → A.a) Bit.ff Bit.tt
          Bit.ff_ne_tt hneq
        rw (config := { transparency := .default }) [hleft, hkeep] at hfalse htrue
        exact hfalse.symm.trans htrue
    have happly := offDiagonal_map_apply (h' : Bit → A.a)
      (OffDiagonal.pair Bit.ff Bit.tt Bit.ff_ne_tt)
    have hcollapse := OffDiagonal.map_pair_collapse (h' : Bit → A.a) Bit.ff Bit.tt
      Bit.ff_ne_tt hsame
    rw (config := { transparency := .default }) [happly, hcollapse] at happ
    exact happ.symm

theorem twoPoint_recursive : IsRecursive twoPoint :=
  fun A =>
    ⟨↾ fun _ : Bit => A.str OffDiagonal.diagonal,
      (twoPoint_solution A).1, (twoPoint_solution A).2⟩

theorem twoPoint_empty_inductive : Inductive twoPoint ∅ := by
  intro a ⟨t, ht⟩
  cases t with
  | diagonal =>
      have hbad : OffDiagonal.diagonal =
          OffDiagonal.pair Bit.ff Bit.tt Bit.ff_ne_tt := by
        have hmap := offDiagonal_map_apply (Subtype.val : Subtype (∅ : Set Bit) → Bit)
          OffDiagonal.diagonal
        have hstep := ht
        rw (config := { transparency := .default }) [inclusion, hmap] at hstep
        unfold twoPoint OffDiagonal.map at hstep
        exact hstep
      cases hbad
  | pair x y _ =>
      exact False.elim x.2

theorem twoPoint_not_wellFounded : ¬ IsWellFounded twoPoint := by
  intro hwf
  exact (hwf ∅ twoPoint_empty_inductive Bit.ff)

/-- `OffDiagonal` sends injective functions to injective functions. -/
theorem offDiagonal_preserves_monomorphisms :
    PreservesMonomorphisms offDiagonalFunctor := by
  intro X Y f hf
  rw [mono_iff_injective] at hf ⊢
  intro a b hab
  have happ : OffDiagonal.map (f : X → Y) a = OffDiagonal.map (f : X → Y) b := by
    have ha := offDiagonal_map_apply (f : X → Y) a
    have hb := offDiagonal_map_apply (f : X → Y) b
    exact ha.symm.trans (hab.trans hb)
  cases a with
  | diagonal =>
      cases b with
      | diagonal => rfl
      | pair x y distinct =>
          rw [OffDiagonal.map_diagonal, OffDiagonal.map_pair_keep _ _ _ _ (hf.ne distinct)] at happ
          cases happ
  | pair x y distinct =>
      cases b with
      | diagonal =>
          rw [OffDiagonal.map_pair_keep _ _ _ _ (hf.ne distinct), OffDiagonal.map_diagonal] at happ
          cases happ
      | pair x' y' distinct' =>
          rw [OffDiagonal.map_pair_keep _ _ _ _ (hf.ne distinct),
            OffDiagonal.map_pair_keep _ _ _ _ (hf.ne distinct')] at happ
          injection happ with hx hy
          have hx' : x = x' := hf hx
          have hy' : y = y' := hf hy
          subst hx' hy'
          rfl

/-! ## Example 2.47: a functor and the extension that fills the empty type -/

/-- Two points, the second available only when the argument is nonempty. -/
inductive Gapped (X : Type u) : Type u where
  | b
  | a (occupied : Nonempty X)

namespace Gapped

def map {X Y : Type u} (f : X → Y) : Gapped X → Gapped Y
  | b => b
  | a occupied => a (occupied.map f)

theorem id_map {X : Type u} (shape : Gapped X) : map id shape = shape := by
  cases shape <;> rfl

theorem comp_map {X Y Z : Type u} (f : X → Y) (g : Y → Z) (shape : Gapped X) :
    map (g ∘ f) shape = map g (map f shape) := by
  cases shape <;> rfl

end Gapped

instance : Functor Gapped where
  map := Gapped.map

instance : LawfulFunctor Gapped where
  map_const := rfl
  id_map := Gapped.id_map
  comp_map := Gapped.comp_map

abbrev gappedFunctor : Type u ⥤ Type u := ofTypeFunctor Gapped

theorem gapped_map_apply {X Y : Type u} (f : X → Y) (shape : Gapped X) :
    gappedFunctor.map (↾ f) shape = Gapped.map f shape := by
  simp only [gappedFunctor, ofTypeFunctor_map, TypeCat.ofHom, TypeCat.Hom.hom,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
  rfl

/-- The one-point coalgebra selecting the point that needs an inhabitant. -/
def gappedPoint : Coalgebra gappedFunctor where
  V := PUnit.{u + 1}
  str := ↾ fun _ => Gapped.a ⟨PUnit.unit⟩

theorem gappedPoint_empty_inductive : Inductive gappedPoint ∅ := by
  intro a ⟨t, ht⟩
  cases t with
  | b =>
      have hbad : Gapped.b = Gapped.a ⟨PUnit.unit⟩ := by
        have hred := ht
        simp [inclusion, gappedPoint, gappedFunctor, ofTypeFunctor_map,
          TypeCat.ofHom, TypeCat.Fun.coe_mk] at hred
        exact hred
      cases hbad
  | a occupied =>
      exact False.elim (occupied.elim (fun x => x.2))

theorem gappedPoint_not_wellFounded : ¬ IsWellFounded gappedPoint :=
  fun hwf => (hwf ∅ gappedPoint_empty_inductive PUnit.unit)

/-- The two-point extension. It does not look at the argument. -/
abbrev ClosedPoint (_ : Type u) : Type u := Bit

instance : Functor ClosedPoint where
  map _ := id

instance : LawfulFunctor ClosedPoint where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

abbrev closedFunctor : Type u ⥤ Type u := ofTypeFunctor ClosedPoint

/-- On a nonempty type the gapped functor and the two-point extension agree. -/
def gappedClosedEquiv {X : Type u} [Nonempty X] : Gapped X ≃ Bit where
  toFun
    | Gapped.b => Bit.ff
    | Gapped.a _ => Bit.tt
  invFun
    | Bit.ff => Gapped.b
    | Bit.tt => Gapped.a inferInstance
  left_inv
    | Gapped.b => rfl
    | Gapped.a _ => rfl
  right_inv
    | Bit.ff => rfl
    | Bit.tt => rfl

theorem gapped_closed_natural {X Y : Type u} [Nonempty X] [Nonempty Y] (f : X → Y)
    (shape : Gapped X) :
    gappedClosedEquiv (Gapped.map f shape) = gappedClosedEquiv shape := by
  cases shape <;> rfl

/-- The same one-point carrier, read for the two-point extension. -/
def closedPoint : Coalgebra closedFunctor where
  V := PUnit.{u + 1}
  str := ↾ fun _ => Bit.tt

theorem closedPoint_wellFounded : IsWellFounded closedPoint := by
  intro P hP a
  cases a
  have hnext : PUnit.unit ∈ Next closedPoint ∅ := by
    refine ⟨Bit.tt, ?_⟩
    rfl
  by_contra hnot
  have hempty : P = ∅ := by
    ext x
    cases x
    simpa using hnot
  have : PUnit.unit ∈ P := hP (by simpa [hempty] using hnext)
  exact hnot this

/-! ## A non-uniform presentation whose meeting map stays injective -/

/-- One point, independently of the argument. -/
inductive Ghost (α : Type u) : Type u where
  | point

namespace Ghost

def map {α β : Type u} (_ : α → β) : Ghost α → Ghost β
  | point => point

theorem id_map {α : Type u} (x : Ghost α) : map id x = x := by
  cases x
  rfl

theorem comp_map {α β γ : Type u} (f : α → β) (g : β → γ) (x : Ghost α) :
    map (g ∘ f) x = map g (map f x) := by
  cases x
  rfl

end Ghost

instance : Functor.{u, u} Ghost where
  map := Ghost.map

instance : LawfulFunctor.{u, u} Ghost where
  map_const := rfl
  id_map := Ghost.id_map
  comp_map := Ghost.comp_map

/-- The childless shape, and a shape whose single child is ignored. -/
inductive GhostShape : Type u where
  | stop
  | ghost

/-- `stop` has no child. `ghost` has one child. -/
abbrev ghostChild : GhostShape → Type u
  | .stop => PEmpty.{u + 1}
  | .ghost => PUnit.{u + 1}

/-- The polynomial with those two shapes. -/
abbrev ghostPolynomial : PFunctor.{u, u} :=
  ⟨GhostShape, ghostChild⟩

def ghostAbs {α : Type u} : ghostPolynomial.Obj α → Ghost α
  | _ => Ghost.point

def ghostRepr {α : Type u} : Ghost α → ghostPolynomial.Obj α
  | Ghost.point => ⟨GhostShape.stop, PEmpty.elim⟩

theorem ghost_abs_repr {α : Type u} (x : Ghost α) : ghostAbs (ghostRepr x) = x := by
  cases x
  rfl

theorem ghost_abs_map {α β : Type u} (f : α → β) (shape : ghostPolynomial.Obj α) :
    ghostAbs (ghostPolynomial.map f shape) = f <$> ghostAbs shape := by
  rfl

instance : QPF.{u, u, u} Ghost where
  P := ghostPolynomial
  abs := ghostAbs
  repr := ghostRepr
  abs_repr := ghost_abs_repr
  abs_map := ghost_abs_map

open Functor (supp)
open Set

/-- The two shapes abstract to one point and do not have the same child image. -/
theorem ghost_not_uniform : ¬ @QPF.IsUniform.{u, u} Ghost _ := by
  intro h
  let emptyImage : Set PUnit.{u + 1} :=
    Set.image (PEmpty.elim : PEmpty.{u + 1} → PUnit.{u + 1}) Set.univ
  let ghostImage : Set PUnit.{u + 1} :=
    Set.image (fun _ : PUnit.{u + 1} => PUnit.unit) Set.univ
  have himg : emptyImage = ghostImage :=
    h GhostShape.stop GhostShape.ghost
      (PEmpty.elim : PEmpty.{u + 1} → PUnit.{u + 1})
      (fun _ : PUnit.{u + 1} => PUnit.unit) rfl
  have hmem : PUnit.unit ∈ ghostImage := ⟨PUnit.unit, Set.mem_univ _, rfl⟩
  rw [← himg] at hmem
  rcases hmem with ⟨i, -, -⟩
  exact PEmpty.elim i

/-- Every representation agrees with the childless shape, so nothing is supported. -/
theorem ghost_supp_empty {α : Type u} (x : Ghost α) : supp x = ∅ := by
  ext u
  simp only [mem_empty_iff_false, iff_false]
  intro hu
  have habs : QPF.abs ⟨GhostShape.stop, PEmpty.elim⟩ = x := by
    cases x
    rfl
  have hmem := (QPF.mem_supp x u).1 hu GhostShape.stop PEmpty.elim habs
  rcases hmem with ⟨i, -, -⟩
  exact PEmpty.elim i

/-- The ignored child is not recovered from the support of its abstraction. -/
theorem ghost_supp_ne_image :
    supp (ghostAbs ⟨GhostShape.ghost, fun _ => PUnit.unit⟩) ≠
      Set.image (fun _ : PUnit.{u + 1} => PUnit.unit) univ := by
  intro h
  have habs : ghostAbs ⟨GhostShape.ghost, fun _ => PUnit.unit⟩ = Ghost.point := rfl
  rw [habs, ghost_supp_empty] at h
  have hmem : PUnit.unit ∈ Set.image (fun _ : PUnit.{u + 1} => PUnit.unit) univ :=
    ⟨PUnit.unit, mem_univ _, rfl⟩
  rw [← h] at hmem
  exact notMem_empty _ hmem

/-- Every tree abstracts like the childless tree, so the trees are identified. -/
theorem ghost_wequiv_stop (t : PFunctor.W ghostPolynomial) :
    QPF.Wequiv (F := Ghost) t
      (PFunctor.W.mk (⟨GhostShape.stop, PEmpty.elim⟩ :
        ghostPolynomial.Obj (PFunctor.W ghostPolynomial))) := by
  apply QPF.Wequiv.abs'
  rfl

/-- The initial algebra of this presentation has one element. -/
theorem ghost_fix_subsingleton (x y : QPF.Fix Ghost) : x = y := by
  refine Quotient.inductionOn x ?_
  intro tx
  refine Quotient.inductionOn y ?_
  intro ty
  exact Quotient.sound
    (QPF.Wequiv.trans _ _ _
      (ghost_wequiv_stop tx)
      (QPF.Wequiv.symm _ _ (ghost_wequiv_stop ty)))

/-- The meeting map stays injective: its domain has one element. -/
theorem ghost_meeting_injective :
    Function.Injective
      (QPF.Cofix.corec (QPF.Fix.dest : QPF.Fix Ghost → Ghost (QPF.Fix Ghost))) := by
  intro x y _
  exact ghost_fix_subsingleton x y

/-- Uniformity fails and the meeting map is nevertheless injective. -/
theorem ghost_injective_without_uniform :
    ¬ @QPF.IsUniform.{u, u} Ghost _ ∧
      Function.Injective
        (QPF.Cofix.corec (QPF.Fix.dest : QPF.Fix Ghost → Ghost (QPF.Fix Ghost))) :=
  ⟨ghost_not_uniform, ghost_meeting_injective⟩

end Mettapedia.Coalgebra.InitialFinal

