import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Data.Set.Lattice

/-!
# Well-founded coalgebras

For an endofunctor `F` of a universe of types, the next-time operator of a
coalgebra sends a subset `P` to the states whose structure lands in the image
of `F` on the inclusion of `P`. A subset is inductive when it contains its
next-time. The coalgebra is well-founded when the only inductive subset is
the carrier.

A cartesian subcoalgebra is a coalgebra monomorphism whose square is a
pullback. Preservation of monomorphisms makes the two formulations agree:
the only inductive subset is the carrier exactly when there is no proper
cartesian subcoalgebra. The image of a cartesian subcoalgebra is always a
fixed point of next-time. The converse construction, from a fixed point to a
pullback square, is where preservation of monomorphisms is used.

An initial algebra, read as a coalgebra along the inverse of its structure
map, has no proper cartesian subcoalgebra. No preservation hypothesis is
used. This is the argument of Adámek, Milius, Moss, and Sousa, *Well-pointed
coalgebras*, Proposition 2.11.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.InitialFinal

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits
open CategoryTheory.Limits.Types

universe u

/-- `F` sends monomorphisms of types to monomorphisms. -/
def PreservesMonomorphisms (F : Type u ⥤ Type u) : Prop :=
  ∀ {X Y : Type u} (f : X ⟶ Y), Mono f → Mono (F.map f)

/-- `F` preserves pullbacks of monomorphisms. A pullback of two monomorphisms
is an intersection of subobjects, and the cospan is a finite diagram, so this
is preservation of finite intersections. -/
def PreservesFiniteIntersections (F : Type u ⥤ Type u) : Prop :=
  ∀ {X Y Z : Type u} (f : Y ⟶ X) (g : Z ⟶ X),
    Mono f → Mono g → PreservesLimit (cospan f g) F

variable {F : Type u ⥤ Type u}

/-- The inclusion of a subset into the carrier of a coalgebra. -/
def inclusion {V : Type u} (P : Set V) : Subtype P ⟶ V :=
  ↾ Subtype.val

theorem inclusion_injective {V : Type u} (P : Set V) :
    Function.Injective (inclusion P) :=
  Subtype.val_injective

theorem mono_inclusion {V : Type u} (P : Set V) : Mono (inclusion P) :=
  (mono_iff_injective _).mpr (inclusion_injective P)

/-- A state lies in `Next P` when its structure is the `F`-image of the
inclusion of `P`. -/
def Next (V : Coalgebra F) (P : Set V.V) : Set V.V :=
  fun a => ∃ t : F.obj (Subtype P), F.map (inclusion P) t = V.str a

/-- `P` is inductive when next-time does not leave `P`. -/
def Inductive (V : Coalgebra F) (P : Set V.V) : Prop :=
  Next V P ⊆ P

/-- The carrier is always inductive: `F` preserves the identity. -/
theorem inductive_univ (V : Coalgebra F) : Inductive V Set.univ := by
  intro a ha
  trivial

/-- The coalgebra is well-founded when its only inductive subset is the
carrier. -/
def IsWellFounded (V : Coalgebra F) : Prop :=
  ∀ P : Set V.V, Inductive V P → ∀ a, a ∈ P

theorem next_mono (V : Coalgebra F) {P Q : Set V.V} (hPQ : P ⊆ Q) :
    Next V P ⊆ Next V Q := by
  intro a ⟨t, ht⟩
  let j : Subtype P ⟶ Subtype Q := ↾ fun x => ⟨x.1, hPQ x.2⟩
  have hcomp : inclusion P = j ≫ inclusion Q := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  refine ⟨F.map j t, ?_⟩
  rw [← ht, hcomp, Functor.map_comp, CategoryTheory.comp_apply]

/-- The intersection of every inductive subset. -/
def leastInductive (V : Coalgebra F) : Set V.V :=
  ⋂₀ {P | Inductive V P}

theorem leastInductive_subset {V : Coalgebra F} {P : Set V.V} (hP : Inductive V P) :
    leastInductive V ⊆ P :=
  Set.sInter_subset_of_mem hP

theorem next_leastInductive_subset (V : Coalgebra F) :
    Next V (leastInductive V) ⊆ leastInductive V := by
  intro a ha P hP
  exact hP (next_mono V (leastInductive_subset hP) ha)

theorem inductive_next_leastInductive (V : Coalgebra F) :
    Inductive V (Next V (leastInductive V)) := by
  intro a ha
  exact next_mono V (next_leastInductive_subset V) ha

theorem leastInductive_subset_next (V : Coalgebra F) :
    leastInductive V ⊆ Next V (leastInductive V) :=
  leastInductive_subset (inductive_next_leastInductive V)

/-- By monotonicity, the intersection of the inductive subsets is a fixed
point of next-time. -/
theorem next_leastInductive (V : Coalgebra F) :
    Next V (leastInductive V) = leastInductive V :=
  Set.Subset.antisymm (next_leastInductive_subset V) (leastInductive_subset_next V)

theorem inductive_leastInductive (V : Coalgebra F) :
    Inductive V (leastInductive V) := by
  unfold Inductive
  rw [next_leastInductive]

/-- Well-founded exactly when that intersection is the carrier. -/
theorem isWellFounded_iff_leastInductive_eq_univ (V : Coalgebra F) :
    IsWellFounded V ↔ leastInductive V = Set.univ := by
  constructor
  · intro hwf
    apply Set.eq_univ_of_forall
    exact hwf _ (inductive_leastInductive V)
  · intro h P hP a
    have : a ∈ leastInductive V := by
      rw [h]
      trivial
    exact leastInductive_subset hP this

/-- A coalgebra monomorphism is cartesian when its square is a pullback. -/
def IsCartesian {V W : Coalgebra F} (φ : W ⟶ V) : Prop :=
  Mono φ.f ∧ IsPullback W.str φ.f (F.map φ.f) V.str

/-- No proper cartesian subcoalgebra: every cartesian monomorphism is
surjective, hence an isomorphism. -/
def IsCartesianWellFounded (V : Coalgebra F) : Prop :=
  ∀ (W : Coalgebra F) (φ : W ⟶ V), IsCartesian φ → Function.Surjective φ.f

/-- Membership of a fixed point in its own next-time set. One proof term, so
`Classical.choose` and `Classical.choose_spec` meet. -/
theorem fixedPoint_mem_next (V : Coalgebra F) {P : Set V.V} (hfix : Next V P = P)
    (x : Subtype P) : x.1 ∈ Next V P := by
  rw [hfix]
  exact x.2

/-- The inclusion of a next-time fixed point, with the structure map chosen
from the fixed-point equation. Preservation of monomorphisms makes the
witness unique, so the square is a pullback. -/
noncomputable def fixedPointCoalgebra (V : Coalgebra F) (P : Set V.V)
    (hfix : Next V P = P) (_hF : PreservesMonomorphisms F) : Coalgebra F where
  V := Subtype P
  str := ↾ fun x => Classical.choose (fixedPoint_mem_next V hfix x)

theorem fixedPointCoalgebra_str_spec (V : Coalgebra F) (P : Set V.V)
    (hfix : Next V P = P) (hF : PreservesMonomorphisms F) (x : Subtype P) :
    F.map (inclusion P) ((fixedPointCoalgebra V P hfix hF).str x) = V.str x.1 :=
  Classical.choose_spec (fixedPoint_mem_next V hfix x)

/-- The inclusion of a next-time fixed point is a cartesian subcoalgebra. -/
theorem fixedPoint_isCartesian (V : Coalgebra F) (P : Set V.V)
    (hfix : Next V P = P) (hF : PreservesMonomorphisms F) :
    IsCartesian (show (fixedPointCoalgebra V P hfix hF) ⟶ V from {
      f := inclusion P
      h := by
        apply ConcreteCategory.hom_ext
        intro x
        exact fixedPointCoalgebra_str_spec V P hfix hF x }) := by
  let W := fixedPointCoalgebra V P hfix hF
  let φ : W ⟶ V := {
    f := inclusion P
    h := by
      apply ConcreteCategory.hom_ext
      intro x
      exact fixedPointCoalgebra_str_spec V P hfix hF x }
  refine ⟨mono_inclusion P, ?_⟩
  apply (isPullback_iff _ _ _ _).mpr
  refine ⟨φ.h, ?_, ?_⟩
  · intro x y hxy
    exact inclusion_injective P hxy.2
  · intro t a ht
    have ha : a ∈ P := by
      have : a ∈ Next V P := ⟨t, ht⟩
      rwa [hfix] at this
    let x : Subtype P := ⟨a, ha⟩
    have hinj : Function.Injective (F.map (inclusion P)) :=
      (mono_iff_injective _).mp (hF (inclusion P) (mono_inclusion P))
    have hchosen := fixedPointCoalgebra_str_spec V P hfix hF x
    have : (fixedPointCoalgebra V P hfix hF).str x = t :=
      hinj (hchosen.trans ht.symm)
    exact ⟨x, this, rfl⟩

theorem cartesian_range_fixed (V : Coalgebra F) {W : Coalgebra F} (φ : W ⟶ V)
    (hcart : IsCartesian φ) :
    Next V (Set.range (φ.f : W.V → V.V)) = Set.range (φ.f : W.V → V.V) := by
  let R : Set V.V := Set.range (φ.f : W.V → V.V)
  apply Set.Subset.antisymm
  · intro a ⟨t, ht⟩
    let section_ : Subtype R → W.V := fun x => Classical.choose x.2
    have section_spec (x : Subtype R) : φ.f (section_ x) = x.1 :=
      Classical.choose_spec x.2
    have hfac : inclusion R = (↾ section_) ≫ φ.f := by
      apply ConcreteCategory.hom_ext
      intro x
      exact (section_spec x).symm
    have ht' : F.map φ.f (F.map (↾ section_) t) = V.str a := by
      have hmap := congrArg (fun f : Subtype R ⟶ V.V => F.map f t) hfac
      rw [Functor.map_comp, CategoryTheory.comp_apply] at hmap
      exact hmap.symm.trans ht
    obtain ⟨w, -, hwφ⟩ := exists_of_isPullback hcart.2 (F.map (↾ section_) t) a ht'
    exact ⟨w, hwφ⟩
  · intro a ⟨w, hw⟩
    let toRange : W.V → Subtype R := fun z => ⟨φ.f z, ⟨z, rfl⟩⟩
    refine ⟨F.map (↾ toRange) (W.str w), ?_⟩
    have hfac : (↾ toRange) ≫ inclusion R = φ.f := by
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    have hmap := congrArg (fun f : W.V ⟶ V.V => (F.map f) (W.str w)) hfac
    rw [Functor.map_comp, CategoryTheory.comp_apply] at hmap
    have hcomm := ConcreteCategory.congr_hom φ.h w
    simp only [CategoryTheory.comp_apply] at hcomm
    rw [hmap, hcomm, hw]

theorem cartesian_range_inductive (V : Coalgebra F) {W : Coalgebra F} (φ : W ⟶ V)
    (hcart : IsCartesian φ) :
    Inductive V (Set.range (φ.f : W.V → V.V)) := by
  unfold Inductive
  rw [cartesian_range_fixed V φ hcart]

/-- A well-founded coalgebra has no proper cartesian subcoalgebra. -/
theorem wellFounded_cartesian (V : Coalgebra F) (hwf : IsWellFounded V) :
    IsCartesianWellFounded V := by
  intro W φ hcart a
  have ha : a ∈ leastInductive V := by
    rw [isWellFounded_iff_leastInductive_eq_univ] at hwf
    simp [hwf]
  have hsub := leastInductive_subset (cartesian_range_inductive V φ hcart)
  obtain ⟨w, hw⟩ := hsub ha
  exact ⟨w, hw⟩

/-- Under preservation of monomorphisms, absence of a proper cartesian
subcoalgebra returns inductive well-foundedness. -/
theorem cartesian_wellFounded (V : Coalgebra F) (hF : PreservesMonomorphisms F)
    (hcart : IsCartesianWellFounded V) : IsWellFounded V := by
  rw [isWellFounded_iff_leastInductive_eq_univ]
  let P := leastInductive V
  have hfix : Next V P = P := next_leastInductive V
  let φ : fixedPointCoalgebra V P hfix hF ⟶ V := {
    f := inclusion P
    h := by
      apply ConcreteCategory.hom_ext
      intro x
      exact fixedPointCoalgebra_str_spec V P hfix hF x }
  have hsurj := hcart _ φ (fixedPoint_isCartesian V P hfix hF)
  apply Set.eq_univ_of_forall
  intro a
  obtain ⟨x, hx⟩ := hsurj a
  rw [← hx]
  exact x.2

/-- The two forms of well-foundedness agree when `F` preserves monomorphisms.
The direction from the inductive form to the cartesian form does not use that
hypothesis; see `wellFounded_cartesian`. -/
theorem isWellFounded_iff_cartesian (V : Coalgebra F) (hF : PreservesMonomorphisms F) :
    IsWellFounded V ↔ IsCartesianWellFounded V :=
  ⟨wellFounded_cartesian V, cartesian_wellFounded V hF⟩

/-! ## Initial algebras are cartesian-well-founded -/

/-- The Lambek coalgebra of an initial algebra: the structure map is inverted.
Reducible so the carrier `A.a` and `Algebra.Initial.strInv` stay definitional
at the transparency `simp` and `rw` use. -/
@[reducible]
noncomputable def coalgebraOfInitial {A : Algebra F} (h : Limits.IsInitial A) :
    Coalgebra F where
  V := A.a
  str := Algebra.Initial.strInv h

theorem coalgebraOfInitial_str_left_inv {A : Algebra F} (h : Limits.IsInitial A) :
    (coalgebraOfInitial h).str ≫ A.str = 𝟙 A.a :=
  Algebra.Initial.left_inv h

theorem coalgebraOfInitial_str_right_inv {A : Algebra F} (h : Limits.IsInitial A) :
    A.str ≫ (coalgebraOfInitial h).str = 𝟙 (F.obj A.a) :=
  Algebra.Initial.right_inv h

theorem coalgebraOfInitial_str_left_apply {A : Algebra F} (h : Limits.IsInitial A)
    (x : A.a) : A.str ((coalgebraOfInitial h).str x) = x := by
  have happ := ConcreteCategory.congr_hom (Algebra.Initial.left_inv h) x
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using happ

theorem coalgebraOfInitial_str_right_apply {A : Algebra F} (h : Limits.IsInitial A)
    (y : F.obj A.a) : (coalgebraOfInitial h).str (A.str y) = y := by
  have happ := ConcreteCategory.congr_hom (Algebra.Initial.right_inv h) y
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using happ

theorem coalgebraOfInitial_str_bijective {A : Algebra F} (h : Limits.IsInitial A) :
    Function.Bijective (coalgebraOfInitial h).str := by
  constructor
  · intro x y hxy
    exact (coalgebraOfInitial_str_left_apply h x).symm.trans
      ((congrArg A.str hxy).trans (coalgebraOfInitial_str_left_apply h y))
  · intro y
    exact ⟨A.str y, coalgebraOfInitial_str_right_apply h y⟩

/-- An initial algebra, read as a coalgebra by Lambek's lemma, has no proper
cartesian subcoalgebra. -/
theorem coalgebraOfInitial_cartesianWellFounded {A : Algebra F}
    (h : Limits.IsInitial A) : IsCartesianWellFounded (coalgebraOfInitial h) := by
  intro W φ hcart
  have comm (w : W.V) :
      F.map φ.f (W.str w) = (coalgebraOfInitial h).str (φ.f w) := by
    have happ := ConcreteCategory.congr_hom φ.h w
    simpa only [CategoryTheory.comp_apply] using happ
  have Wstr_bijective : Function.Bijective W.str := by
    constructor
    · intro x y hxy
      have himg : (coalgebraOfInitial h).str (φ.f x) =
          (coalgebraOfInitial h).str (φ.f y) := by
        rw [← comm, ← comm, hxy]
      have hφ : φ.f x = φ.f y :=
        (coalgebraOfInitial_str_bijective h).1 himg
      exact (mono_iff_injective φ.f).mp hcart.1 hφ
    · intro t
      let i := A.str (F.map φ.f t)
      have ht : F.map φ.f t = (coalgebraOfInitial h).str i :=
        (coalgebraOfInitial_str_right_apply h (F.map φ.f t)).symm
      obtain ⟨w, hwstr, _⟩ := exists_of_isPullback hcart.2 t i ht
      exact ⟨w, hwstr⟩
  have hWIso : IsIso W.str := (isIso_iff_bijective W.str).mpr Wstr_bijective
  let Walg : Algebra F := { a := W.V, str := inv W.str (I := hWIso) }
  let φalg : Walg ⟶ A := {
    f := φ.f
    h := by
      apply ConcreteCategory.hom_ext
      intro t
      have hround : W.str (inv W.str (I := hWIso) t) = t := by
        simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using
          ConcreteCategory.congr_hom (IsIso.inv_hom_id W.str (I := hWIso)) t
      have hcomm : F.map φ.f t =
          (coalgebraOfInitial h).str (φ.f (inv W.str (I := hWIso) t)) := by
        have hstep := comm (inv W.str (I := hWIso) t)
        rwa [hround] at hstep
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hcomm]
      exact coalgebraOfInitial_str_left_apply h (φ.f (inv W.str (I := hWIso) t)) }
  let fold : A ⟶ Walg := h.to Walg
  have hret : fold ≫ φalg = 𝟙 A := IsInitial.hom_ext h _ _
  intro a
  refine ⟨fold.f a, ?_⟩
  have hf := congrArg Algebra.Hom.f hret
  have happ := ConcreteCategory.congr_hom hf a
  simpa only [Algebra.comp_f, Algebra.id_f, CategoryTheory.comp_apply,
    CategoryTheory.id_apply] using happ

/-- Under preservation of monomorphisms, the Lambek coalgebra of an initial
algebra is inductively well-founded. -/
theorem coalgebraOfInitial_wellFounded {A : Algebra F} (h : Limits.IsInitial A)
    (hF : PreservesMonomorphisms F) : IsWellFounded (coalgebraOfInitial h) :=
  cartesian_wellFounded _ hF (coalgebraOfInitial_cartesianWellFounded h)

end Mettapedia.Coalgebra.InitialFinal

