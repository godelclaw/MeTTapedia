import Mettapedia.Coalgebra.InitialFinal.Recursive
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Logic.Views
import Mathlib.Data.QPF.Univariate.Basic

/-
Compare type arguments of metavariables, and implicit arguments of rewrites, at
default transparency. `qpfFunctor` and `fixAlgebra` stay reducible so their
carriers match `F` and `QPF.Fix` at the transparency `rw` uses.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Where a quotient polynomial functor's initial algebra meets its final coalgebra

For a quotient of a polynomial functor, `QPF.Fix` is an initial algebra and
`QPF.Cofix` is a final coalgebra. The unique coalgebra morphism from the
Lambek coalgebra of `QPF.Fix` into `QPF.Cofix` is `QPF.Cofix.corec QPF.Fix.dest`.
The same function is the algebra fold of `QPF.Cofix` along the inverse of its
structure map.

Inductive well-foundedness of `QPF.Fix` uses `QPF.Fix.ind` and does not ask the
functor to be uniform. A well-founded coalgebra of a uniform quotient admits
exactly one coalgebra-to-algebra map, by recursion along `supp`. Uniformity is
the hypothesis used for that recursion, for injectivity of the meeting map, and
for the identification of its image with the accessible part of `QPF.Cofix`.

The argument that an initial algebra is the final recursive coalgebra, for an
arbitrary endofunctor of types, is in `Recursive`. The comparison recorded by
Adámek, Milius, Moss, and Sousa, *Well-pointed coalgebras*, Theorem 2.38, is
proved here for uniform quotients of polynomial functors.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.InitialFinal

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits
open Functor (Liftp Liftr supp)
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.ViewPluralism

universe u

variable {F : Type u → Type u} [QPF F] [LawfulFunctor F]

/-- Object part of the endofunctor. Named separately so that `Liftp` and `supp`
are applied to `F`, and so later declarations do not project the object field
of the categorical structure. -/
abbrev qpfObj (α : Type u) : Type u := F α

/-- The endofunctor of types presented by a lawful quotient polynomial functor. -/
def qpfFunctor : Type u ⥤ Type u where
  obj := qpfObj
  map {X Y} (f : X ⟶ Y) :=
    ↾ fun (x : F X) => _root_.Functor.map (TypeCat.Hom.hom f) x
  map_id α := by
    apply ConcreteCategory.hom_ext
    intro x
    simp only [TypeCat.ofHom_apply]
    have hid : (ConcreteCategory.hom (𝟙 α) : α → α) = id := rfl
    have hidF : (ConcreteCategory.hom (𝟙 (F α)) : F α → F α) x = x := rfl
    rw [hid, id_map]
    exact hidF.symm
  map_comp {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) := by
    apply ConcreteCategory.hom_ext
    intro x
    simp only [TypeCat.ofHom_apply, CategoryTheory.comp_apply]
    have hcomp : (ConcreteCategory.hom (f ≫ g) : X → Z) =
        (ConcreteCategory.hom g : Y → Z) ∘ (ConcreteCategory.hom f : X → Y) := rfl
    rw [hcomp, comp_map]

attribute [reducible] qpfFunctor

theorem qpfFunctor_map_apply {α β : Type u} (f : α → β) (x : F α) :
    qpfFunctor.map (↾ f) x = f <$> x := by
  unfold qpfFunctor
  simp only [TypeCat.Hom.hom, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]

/-- Read a categorical element as an element of `F`.

Irreducible so an application keeps the result type `F α`. A reducible identity
would be replaced by its argument, whose type is the object projection, and
`Liftp` / `supp` would look for a functor structure on that projection. -/
def asF {α : Type u} (x : @qpfObj F α) : F α := x

/-- Read an element of `F` as a categorical element. -/
def toObj {α : Type u} (x : F α) : @qpfObj F α := x

attribute [irreducible] asF toObj

omit [QPF F] [LawfulFunctor F] in
theorem asF_toObj {α : Type u} (x : F α) : asF (F := F) (toObj (F := F) x) = x := by
  unfold asF toObj
  rfl

omit [QPF F] [LawfulFunctor F] in
theorem toObj_asF {α : Type u} (x : @qpfObj F α) : toObj (F := F) (asF (F := F) x) = x := by
  unfold asF toObj
  rfl

omit [QPF F] [LawfulFunctor F] in
theorem asF_injective {α : Type u} : Function.Injective (asF (F := F) (α := α)) := by
  intro x y h
  unfold asF at h
  exact h

omit [QPF F] [LawfulFunctor F] in
theorem asF_eq {α : Type u} (x : @qpfObj F α) : asF (F := F) x = x := by
  unfold asF
  rfl

omit [QPF F] [LawfulFunctor F] in
theorem toObj_eq {α : Type u} (x : F α) : toObj (F := F) x = x := by
  unfold toObj
  rfl

theorem map_asF {α β : Type u} (f : α → β) (x : @qpfObj F α) :
    asF (F := F) (qpfFunctor.map (↾ f) x) = f <$> asF (F := F) x := by
  unfold asF qpfFunctor
  simp only [TypeCat.Hom.hom, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]

theorem mem_next_iff_liftp (V : Coalgebra (qpfFunctor (F := F))) (P : Set V.V) (a : V.V) :
    a ∈ Next V P ↔ Liftp (· ∈ P) (asF (F := F) (V.str a)) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨asF (F := F) t, ?_⟩
    calc
      Subtype.val <$> asF (F := F) t = asF (F := F) (qpfFunctor.map (↾ Subtype.val) t) := (map_asF _ _).symm
      _ = asF (F := F) (qpfFunctor.map (inclusion P) t) := rfl
      _ = asF (F := F) (V.str a) := by rw [ht]
  · rintro ⟨u, hu⟩
    refine ⟨toObj (F := F) u, ?_⟩
    apply asF_injective
    calc
      asF (F := F) (qpfFunctor.map (inclusion P) (toObj (F := F) u)) = Subtype.val <$> asF (F := F) (toObj (F := F) u) := by
        have hinc : inclusion P = (↾ Subtype.val : Subtype P ⟶ V.V) := rfl
        rw [hinc]
        exact map_asF _ _
      _ = Subtype.val <$> u := by rw [asF_toObj]
      _ = asF (F := F) (V.str a) := hu

theorem mem_next_iff_supp (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (P : Set V.V) (a : V.V) :
    a ∈ Next V P ↔ supp (asF (F := F) (V.str a)) ⊆ P := by
  rw [mem_next_iff_liftp, QPF.liftp_iff_of_isUniform hU (asF (F := F) (V.str a)) (· ∈ P)]
  constructor
  · intro h u hu
    exact h u hu
  · intro h u hu
    exact h hu

/-- A state is a child of another when it lies in the support of the structure. -/
def child (V : Coalgebra (qpfFunctor (F := F))) (x y : V.V) : Prop :=
  x ∈ supp (asF (F := F) (V.str y))

/-- States reachable by a finite chain of children. -/
def accessible (V : Coalgebra (qpfFunctor (F := F))) : Set V.V :=
  {a | Acc (child V) a}

theorem accessible_inductive (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F))) :
    Inductive V (accessible V) := by
  intro a ha
  rw [mem_next_iff_supp hU] at ha
  refine Acc.intro a ?_
  intro x hx
  exact ha hx

theorem accessible_least (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    {P : Set V.V} (hP : Inductive V P) {a : V.V} (ha : a ∈ accessible V) : a ∈ P := by
  induction ha with
  | intro a _ ih =>
      have hsupp : supp (asF (F := F) (V.str a)) ⊆ P := by
        intro x hx
        exact ih x hx
      rw [← mem_next_iff_supp hU] at hsupp
      exact hP hsupp

theorem isWellFounded_iff_accessible (hU : QPF.IsUniform (F := F))
    (V : Coalgebra (qpfFunctor (F := F))) :
    IsWellFounded V ↔ accessible V = Set.univ := by
  constructor
  · intro hwf
    ext a
    simp only [Set.mem_univ, iff_true]
    exact hwf _ (accessible_inductive hU V) a
  · intro h P hP a
    have ha : a ∈ accessible V := by
      rw [h]
      trivial
    exact accessible_least hU V hP ha

theorem wellFounded_child (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) : WellFounded (child V) := by
  rw [isWellFounded_iff_accessible hU] at hwf
  refine ⟨?_⟩
  intro a
  have ha : a ∈ accessible V := by
    rw [hwf]
    trivial
  exact ha

/-- One support witness, so `Classical.choose` and `Classical.choose_spec` meet. -/
theorem supp_lift (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F))) (b : V.V) :
    Liftp (fun x => child V x b) (asF (F := F) (V.str b)) := by
  rw [QPF.liftp_iff_of_isUniform hU]
  intro x hx
  exact hx

noncomputable def suppWitness (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (b : V.V) : F {x // child V x b} :=
  Classical.choose (supp_lift hU V b)

theorem suppWitness_spec (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (b : V.V) :
    (Subtype.val <$> suppWitness hU V b) = asF (F := F) (V.str b) :=
  Classical.choose_spec (supp_lift hU V b)

/-- The coalgebra-to-algebra map, by recursion along `supp`. -/
noncomputable def supportFold (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) (A : Algebra (qpfFunctor (F := F))) : V.V → A.a :=
  WellFounded.fix (wellFounded_child hU V hwf) fun b rec =>
    A.str (qpfFunctor.map (↾ fun x : {x // child V x b} => rec x.1 x.2)
      (toObj (F := F) (suppWitness hU V b)))

theorem supportFold_eq (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) (A : Algebra (qpfFunctor (F := F))) (b : V.V) :
    supportFold hU V hwf A b =
      A.str (qpfFunctor.map
        (↾ fun x : {x // child V x b} => supportFold hU V hwf A x.1)
        (toObj (F := F) (suppWitness hU V b))) := by
  unfold supportFold
  rw [WellFounded.fix_eq]

theorem supportFold_solution (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) (A : Algebra (qpfFunctor (F := F))) :
    IsSolution V A (↾ supportFold hU V hwf A) := by
  apply ConcreteCategory.hom_ext
  intro b
  simp only [CategoryTheory.comp_apply, TypeCat.ofHom_apply]
  rw [supportFold_eq hU V hwf A b]
  apply congrArg A.str
  apply asF_injective
  calc
    asF (F := F) (qpfFunctor.map (↾ supportFold hU V hwf A) (V.str b))
        = supportFold hU V hwf A <$> asF (F := F) (V.str b) := map_asF _ _
    _ = supportFold hU V hwf A <$> (Subtype.val <$> suppWitness hU V b) := by
          rw [← suppWitness_spec hU V b]
    _ = (supportFold hU V hwf A ∘ Subtype.val) <$> suppWitness hU V b := by
          rw [comp_map]
    _ = asF (F := F) (qpfFunctor.map
          (↾ fun x : {x // child V x b} => supportFold hU V hwf A x.1)
          (toObj (F := F) (suppWitness hU V b))) := by
          rw [map_asF, asF_toObj]
          rfl

/-- A well-founded coalgebra of a uniform quotient polynomial functor is
recursive. Uniqueness holds for every endofunctor; existence is the recursion
along `supp`. -/
theorem uniform_wellFounded_recursive (hU : QPF.IsUniform (F := F))
    (V : Coalgebra (qpfFunctor (F := F))) (hwf : IsWellFounded V) : IsRecursive V := by
  intro A
  refine ⟨↾ supportFold hU V hwf A, supportFold_solution hU V hwf A, ?_⟩
  intro h' hs'
  apply ConcreteCategory.hom_ext
  intro a
  have huniq := wellFounded_solution_unique hwf A
    (supportFold_solution hU V hwf A) hs'
  exact (ConcreteCategory.congr_hom huniq a).symm

/-- Functions that agree on `supp` agree after `F`. -/
theorem map_agree_on_supp (hU : QPF.IsUniform (F := F)) {α β : Type u}
    (g₁ g₂ : α → β) (x : F α) (h : ∀ a ∈ supp x, g₁ a = g₂ a) :
    g₁ <$> x = g₂ <$> x := by
  have hL : Liftp (fun a => g₁ a = g₂ a) x := by
    rw [QPF.liftp_iff_of_isUniform hU x (fun a => g₁ a = g₂ a)]
    exact h
  obtain ⟨u, hu⟩ := hL
  have hfun : g₁ ∘ Subtype.val = g₂ ∘ (Subtype.val : {a // g₁ a = g₂ a} → α) := by
    funext a
    exact a.2
  calc
    g₁ <$> x = g₁ <$> (Subtype.val <$> u) := by rw [hu]
    _ = (g₁ ∘ Subtype.val) <$> u := by rw [← comp_map]
    _ = (g₂ ∘ Subtype.val) <$> u := by rw [hfun]
    _ = g₂ <$> (Subtype.val <$> u) := comp_map (Subtype.val) g₂ u
    _ = g₂ <$> x := by rw [hu]

/-! ## `QPF.Fix` is the initial algebra -/

/-- The initial algebra of a quotient polynomial functor. -/
@[reducible] def fixAlgebra : Algebra (qpfFunctor (F := F)) where
  a := QPF.Fix F
  str := ↾ fun t => QPF.Fix.mk (asF (F := F) t)

/-- Fold an algebra out of `QPF.Fix`. -/
def fixFold (A : Algebra (qpfFunctor (F := F))) : QPF.Fix F → A.a :=
  QPF.Fix.rec (fun t => A.str (toObj (F := F) t))

theorem fixFold_mk (A : Algebra (qpfFunctor (F := F))) (x : F (QPF.Fix F)) :
    fixFold A (QPF.Fix.mk x) = A.str (toObj (F := F) (fixFold A <$> x)) :=
  QPF.Fix.rec_eq (fun t => A.str (toObj (F := F) t)) x

/-- The algebra morphism induced by `fixFold`. -/
def fixHom (A : Algebra (qpfFunctor (F := F))) : fixAlgebra ⟶ A where
  f := ↾ fixFold A
  h := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
    rw [fixFold_mk A (asF (F := F) t)]
    apply congrArg (ConcreteCategory.hom A.str)
    apply asF_injective
    rw [asF_toObj]
    unfold asF
    rfl

/-- Structure map of the initial algebra, recorded while that algebra is reducible. -/
theorem fixAlgebra_str_apply (t : @qpfObj F (QPF.Fix F)) :
    fixAlgebra.str t = QPF.Fix.mk (asF (F := F) t) := rfl

/-- There is exactly one algebra morphism out of `QPF.Fix`. -/
theorem fixHom_unique (A : Algebra (qpfFunctor (F := F))) (m : fixAlgebra ⟶ A) :
    m = fixHom A := by
  apply Algebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro x
  have hrec : fixFold A = (m.f : QPF.Fix F → A.a) := by
    apply QPF.Fix.rec_unique (fun t => A.str (toObj (F := F) t))
    intro y
    have hm := ConcreteCategory.congr_hom m.h y
    rw (config := { transparency := .default })
      [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hm
    have hstr : fixAlgebra.str y = QPF.Fix.mk y := by
      rw [fixAlgebra_str_apply]
      exact congrArg QPF.Fix.mk (asF_eq y)
    have hmap :
        qpfFunctor.map (↾ (m.f : QPF.Fix F → A.a)) y =
          toObj (F := F) ((m.f : QPF.Fix F → A.a) <$> y) := by
      apply asF_injective
      rw [map_asF, asF_eq, asF_toObj]
    have hsame : qpfFunctor.map m.f y =
        qpfFunctor.map (↾ (m.f : QPF.Fix F → A.a)) y :=
      congrArg (fun f => qpfFunctor.map f y) (TypeCat.ofHom_hom m.f).symm
    rw [hstr, hsame, hmap] at hm
    exact hm.symm
  exact (congrFun hrec x).symm

/-- `QPF.Fix` as a coalgebra along `QPF.Fix.dest`. -/
def fixCoalgebra : Coalgebra (qpfFunctor (F := F)) where
  V := QPF.Fix F
  str := ↾ fun x => toObj (F := F) (QPF.Fix.dest x)

theorem fixCoalgebra_str_left : fixCoalgebra.str ≫ fixAlgebra.str = 𝟙 (QPF.Fix F) := by
  apply ConcreteCategory.hom_ext
  intro x
  rw (config := { transparency := .default })
    [CategoryTheory.comp_apply, CategoryTheory.id_apply, fixAlgebra_str_apply, asF_toObj]
  exact QPF.Fix.mk_dest x

theorem fixCoalgebra_str_right :
    fixAlgebra.str ≫ fixCoalgebra.str = 𝟙 (qpfFunctor.obj (QPF.Fix F)) := by
  apply ConcreteCategory.hom_ext
  intro t
  rw (config := { transparency := .default })
    [CategoryTheory.comp_apply, CategoryTheory.id_apply, fixAlgebra_str_apply,
      TypeCat.ofHom_apply, QPF.Fix.dest_mk, toObj_asF]

/-- `QPF.Fix`, read along `QPF.Fix.dest`, is inductively well-founded. -/
theorem fix_wellFounded :
    IsWellFounded (F := qpfFunctor (F := F)) fixCoalgebra := by
  intro P hP x
  revert x
  apply QPF.Fix.ind
  intro y hy
  have hnext : QPF.Fix.mk y ∈ Next fixCoalgebra P := by
    rw [mem_next_iff_liftp]
    have hdest : asF (F := F) (fixCoalgebra.str (QPF.Fix.mk y)) = y := by
      rw (config := { transparency := .default }) [asF_toObj, QPF.Fix.dest_mk]
    rw [hdest]
    exact hy
  exact hP hnext

/-- The Lambek coalgebra of `QPF.Fix` solves the recursion equation by `fixHom`,
and that solution is the only one. -/
theorem fixCoalgebra_solution (A : Algebra (qpfFunctor (F := F))) :
    IsSolution fixCoalgebra A (fixHom A).f ∧
      ∀ h' : fixCoalgebra.V ⟶ A.a,
        IsSolution fixCoalgebra A h' → h' = (fixHom A).f := by
  have hsol : IsSolution fixCoalgebra A (fixHom A).f := by
    have halg : qpfFunctor.map (fixHom A).f ≫ A.str =
        fixAlgebra.str ≫ (fixHom A).f := (fixHom A).h
    calc
      fixCoalgebra.str ≫ qpfFunctor.map (fixHom A).f ≫ A.str
          = fixCoalgebra.str ≫ (fixAlgebra.str ≫ (fixHom A).f) := by
            rw (config := { transparency := .default }) [halg]
      _ = (fixCoalgebra.str ≫ fixAlgebra.str) ≫ (fixHom A).f := by
            rw (config := { transparency := .default }) [Category.assoc]
      _ = 𝟙 _ ≫ (fixHom A).f := by
            rw (config := { transparency := .default }) [fixCoalgebra_str_left]
      _ = (fixHom A).f := by
            rw (config := { transparency := .default }) [Category.id_comp]
  refine ⟨hsol, ?_⟩
  intro h' hs'
  let h'alg : fixAlgebra ⟶ A := {
    f := h'
    h := by
      calc
        qpfFunctor.map h' ≫ A.str
            = 𝟙 _ ≫ qpfFunctor.map h' ≫ A.str := by
              rw (config := { transparency := .default }) [Category.id_comp]
        _ = (fixAlgebra.str ≫ fixCoalgebra.str) ≫ qpfFunctor.map h' ≫ A.str := by
              rw (config := { transparency := .default }) [← fixCoalgebra_str_right]
        _ = fixAlgebra.str ≫ (fixCoalgebra.str ≫ qpfFunctor.map h' ≫ A.str) := by
              rw (config := { transparency := .default }) [Category.assoc]
        _ = fixAlgebra.str ≫ h' := by
              rw (config := { transparency := .default }) [hs'] }
  exact congrArg Algebra.Hom.f (fixHom_unique A h'alg)

/-- The Lambek coalgebra of `QPF.Fix` is recursive. -/
theorem fixCoalgebra_recursive :
    IsRecursive (F := qpfFunctor (F := F)) fixCoalgebra := by
  intro A
  obtain ⟨hsol, huniq⟩ := fixCoalgebra_solution A
  exact ⟨(fixHom A).f, hsol, huniq⟩

/-- The Lambek coalgebra of `QPF.Fix` is the final recursive coalgebra. -/
theorem fixCoalgebra_finalRecursive :
    IsFinalRecursive (F := qpfFunctor (F := F)) fixCoalgebra := by
  refine ⟨fixCoalgebra_recursive, ?_⟩
  intro W hW
  obtain ⟨h, hs, huniq⟩ := hW fixAlgebra
  have hhom : W.str ≫ qpfFunctor.map h = h ≫ fixCoalgebra.str := by
    calc
      W.str ≫ qpfFunctor.map h
          = W.str ≫ qpfFunctor.map h ≫ 𝟙 _ := by
            rw (config := { transparency := .default }) [Category.comp_id]
      _ = W.str ≫ qpfFunctor.map h ≫ (fixAlgebra.str ≫ fixCoalgebra.str) := by
            rw (config := { transparency := .default }) [fixCoalgebra_str_right]
      _ = (W.str ≫ qpfFunctor.map h ≫ fixAlgebra.str) ≫ fixCoalgebra.str := by
            rw (config := { transparency := .default }) [Category.assoc, Category.assoc]
      _ = h ≫ fixCoalgebra.str := by
            rw (config := { transparency := .default }) [hs]
  let φ : W ⟶ fixCoalgebra := { f := h, h := hhom }
  refine ⟨φ, ?_⟩
  intro ψ
  have hψsol : IsSolution W fixAlgebra ψ.f := by
    calc
      W.str ≫ qpfFunctor.map ψ.f ≫ fixAlgebra.str
          = (W.str ≫ qpfFunctor.map ψ.f) ≫ fixAlgebra.str := by
            rw (config := { transparency := .default }) [Category.assoc]
      _ = (ψ.f ≫ fixCoalgebra.str) ≫ fixAlgebra.str := by
            rw (config := { transparency := .default }) [ψ.h]
      _ = ψ.f ≫ (fixCoalgebra.str ≫ fixAlgebra.str) := by
            rw (config := { transparency := .default }) [Category.assoc]
      _ = ψ.f ≫ 𝟙 fixCoalgebra.V := by
            rw (config := { transparency := .default }) [fixCoalgebra_str_left]
            rfl
      _ = ψ.f := by
            rw (config := { transparency := .default }) [Category.comp_id]
  have hf : ψ.f = h := huniq ψ.f hψsol
  apply Coalgebra.Hom.ext
  exact hf

/-- Under uniformity, the Lambek coalgebra of `QPF.Fix` is final among
well-founded coalgebras. Uniformity supplies a solution out of any
well-founded coalgebra; finality among recursive coalgebras then supplies
the unique coalgebra map. This is Theorem 2.38 of Adámek, Milius, Moss, and
Sousa, *Well-pointed coalgebras*, for a uniform quotient of a polynomial
functor, with `QPF.IsUniform` in place of preservation of finite intersections. -/
theorem uniform_fix_final_wellFounded (hU : QPF.IsUniform (F := F))
    (W : Coalgebra (qpfFunctor (F := F))) (hw : IsWellFounded W) :
    ∃ φ : W ⟶ fixCoalgebra, ∀ ψ : W ⟶ fixCoalgebra, ψ = φ :=
  (fixCoalgebra_finalRecursive).2 W (uniform_wellFounded_recursive hU W hw)

/-! ## `QPF.Cofix` is the final coalgebra -/

/-- The final coalgebra of a quotient polynomial functor. -/
def cofixCoalgebra : Coalgebra (qpfFunctor (F := F)) where
  V := QPF.Cofix F
  str := ↾ fun y => toObj (F := F) (QPF.Cofix.dest y)

theorem cofix_str_dest (y : QPF.Cofix F) :
    asF (F := F) (cofixCoalgebra.str y) = QPF.Cofix.dest y := by
  simp only [cofixCoalgebra]
  exact asF_toObj _

/-- Behaviour into `QPF.Cofix`. -/
def cofixUnfold (V : Coalgebra (qpfFunctor (F := F))) : V.V → QPF.Cofix F :=
  fun a => QPF.Cofix.corec (fun b => asF (F := F) (V.str b)) a

theorem cofixUnfold_dest (V : Coalgebra (qpfFunctor (F := F))) (a : V.V) :
    QPF.Cofix.dest (cofixUnfold V a) = cofixUnfold V <$> asF (F := F) (V.str a) :=
  QPF.Cofix.dest_corec (fun b => asF (F := F) (V.str b)) a

/-- The coalgebra morphism into `QPF.Cofix`. -/
def cofixHom (V : Coalgebra (qpfFunctor (F := F))) : V ⟶ cofixCoalgebra where
  f := ↾ cofixUnfold V
  h := by
    apply ConcreteCategory.hom_ext
    intro a
    apply asF_injective (α := QPF.Cofix F)
    calc
      asF (F := F) ((V.str ≫ qpfFunctor.map (↾ cofixUnfold V)) a)
          = asF (F := F) (qpfFunctor.map (↾ cofixUnfold V) (V.str a)) := by
            rw [CategoryTheory.comp_apply]
      _ = cofixUnfold V <$> asF (F := F) (V.str a) := map_asF _ _
      _ = QPF.Cofix.dest (cofixUnfold V a) := (cofixUnfold_dest V a).symm
      _ = asF (F := F) (cofixCoalgebra.str (cofixUnfold V a)) := (cofix_str_dest _).symm
      _ = asF (F := F) (((↾ cofixUnfold V) ≫ cofixCoalgebra.str) a) := by
            rw [CategoryTheory.comp_apply, TypeCat.ofHom_apply]
            rfl

theorem cofix_dest_injective :
    Function.Injective (QPF.Cofix.dest : QPF.Cofix F → F (QPF.Cofix F)) := by
  intro x y hxy
  apply QPF.Cofix.bisim (fun a b => QPF.Cofix.dest a = QPF.Cofix.dest b) ?_ x y hxy
  intro a b hab
  rw [QPF.liftr_iff]
  rcases hrepr : QPF.repr (QPF.Cofix.dest a) with ⟨s, children⟩
  have habs : QPF.abs ⟨s, children⟩ = QPF.Cofix.dest a := by
    rw [← hrepr]
    exact QPF.abs_repr (QPF.Cofix.dest a)
  refine ⟨s, children, children, habs.symm, ?_, fun _ => rfl⟩
  rw [← hab, habs.symm]

theorem hom_dest {V : Coalgebra (qpfFunctor (F := F))} (φ : V ⟶ cofixCoalgebra) (b : V.V) :
    QPF.Cofix.dest (φ.f b) = (φ.f : V.V → QPF.Cofix F) <$> asF (F := F) (V.str b) := by
  have hm := ConcreteCategory.congr_hom φ.h b
  rw (config := { transparency := .default })
    [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hm
  replace hm := congrArg (asF (F := F)) hm
  rw (config := { transparency := .default }) [map_asF, cofix_str_dest] at hm
  exact hm.symm

/-- Coalgebra morphisms into `QPF.Cofix` agree. -/
theorem cofixHom_unique (V : Coalgebra (qpfFunctor (F := F))) (φ ψ : V ⟶ cofixCoalgebra) : φ = ψ := by
  apply Coalgebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro a
  let r : QPF.Cofix F → QPF.Cofix F → Prop :=
    fun x y => ∃ b, x = φ.f b ∧ y = ψ.f b
  have hbis : ∀ x y, r x y → x = y := by
    apply QPF.Cofix.bisim r
    intro x y ⟨b, hx, hy⟩
    rw [QPF.liftr_iff]
    rcases hreprEq : QPF.repr (asF (F := F) (V.str b)) with ⟨s, children⟩
    have hrepr : QPF.abs ⟨s, children⟩ = asF (F := F) (V.str b) := by
      rw [← hreprEq]
      exact QPF.abs_repr (asF (F := F) (V.str b))
    refine ⟨s, fun i => φ.f (children i), fun i => ψ.f (children i), ?_, ?_, ?_⟩
    · rw [hx, hom_dest, ← hrepr]
      exact (QPF.abs_map (fun z => φ.f z) ⟨s, children⟩).symm
    · rw [hy, hom_dest, ← hrepr]
      exact (QPF.abs_map (fun z => ψ.f z) ⟨s, children⟩).symm
    · intro i
      exact ⟨children i, rfl, rfl⟩
  exact hbis _ _ ⟨a, rfl, rfl⟩

/-- `QPF.Cofix` is terminal: a coalgebra morphism into it is the behaviour map. -/
theorem cofixHom_spec (V : Coalgebra (qpfFunctor (F := F))) (φ : V ⟶ cofixCoalgebra) :
    φ = cofixHom V :=
  cofixHom_unique V φ (cofixHom V)

/-- The meeting map. It is `QPF.Cofix.corec QPF.Fix.dest`. -/
def iota : QPF.Fix F → QPF.Cofix F :=
  QPF.Cofix.corec QPF.Fix.dest

theorem iota_hom :
    fixCoalgebra.str ≫ qpfFunctor.map (X := QPF.Fix F) (Y := QPF.Cofix F) (↾ iota) =
      (↾ iota) ≫ cofixCoalgebra.str := by
  apply ConcreteCategory.hom_ext
  intro x
  apply asF_injective (α := QPF.Cofix F)
  simp only [CategoryTheory.comp_apply, TypeCat.ofHom_apply, TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk, fixCoalgebra, cofixCoalgebra, asF_eq, toObj_eq, asF_toObj, iota]
  exact (QPF.Cofix.dest_corec QPF.Fix.dest x).symm

/-- `iota` as the coalgebra morphism out of the Lambek coalgebra. -/
def lambekToCofix :
    Coalgebra.Hom (F := qpfFunctor (F := F)) fixCoalgebra cofixCoalgebra where
  f := ↾ iota
  h := iota_hom

/-- `iota` is the unique coalgebra morphism from the Lambek coalgebra of the
initial algebra into the final coalgebra. -/
theorem iota_unique_from_lambek
    (φ : Coalgebra.Hom (F := qpfFunctor (F := F)) fixCoalgebra cofixCoalgebra) :
    φ.f = ↾ iota := by
  have hid := cofixHom_unique fixCoalgebra φ lambekToCofix
  exact congrArg Coalgebra.Hom.f hid

/-- A section of `QPF.Cofix.dest`. It is the structure map of the Lambek algebra. -/
def cofixMk (y : F (QPF.Cofix F)) : QPF.Cofix F :=
  QPF.Cofix.corec (Functor.map QPF.Cofix.dest) y

theorem cofixMk_dest_step (y : F (QPF.Cofix F)) :
    QPF.Cofix.dest (cofixMk y) = cofixMk <$> (QPF.Cofix.dest <$> y) :=
  QPF.Cofix.dest_corec (Functor.map QPF.Cofix.dest) y

theorem cofixMk_dest (x : QPF.Cofix F) : cofixMk (QPF.Cofix.dest x) = x := by
  let r : QPF.Cofix F → QPF.Cofix F → Prop :=
    fun a b => a = cofixMk (QPF.Cofix.dest (F := F) b)
  have hbis : ∀ a b, r a b → a = b := by
    apply QPF.Cofix.bisim (F := F) r
    intro a b hab
    rw [QPF.liftr_iff (F := F)]
    rcases hrepr : QPF.repr (F := F) (QPF.Cofix.dest (F := F) b) with ⟨s, children⟩
    have hb : QPF.abs (F := F) ⟨s, children⟩ = QPF.Cofix.dest (F := F) b := by
      rw [← hrepr]
      exact QPF.abs_repr (F := F) _
    refine ⟨s, fun i => cofixMk (QPF.Cofix.dest (F := F) (children i)), children, ?_, hb.symm, ?_⟩
    · rw [hab, cofixMk_dest_step (QPF.Cofix.dest (F := F) b), ← comp_map, ← hb]
      exact (QPF.abs_map (F := F) (fun z => cofixMk (QPF.Cofix.dest (F := F) z)) ⟨s, children⟩).symm
    · intro i
      rfl
  exact hbis (cofixMk (QPF.Cofix.dest (F := F) x)) x rfl

theorem dest_cofixMk (y : F (QPF.Cofix F)) : QPF.Cofix.dest (cofixMk y) = y := by
  rw [cofixMk_dest_step, ← comp_map]
  have hfun : (cofixMk ∘ QPF.Cofix.dest (F := F)) = id := by
    funext x
    exact cofixMk_dest x
  rw [hfun, id_map]

/-- `QPF.Cofix` as an algebra along the inverse of `QPF.Cofix.dest`.
Reducible so the carrier `QPF.Cofix F` stays definitional at the transparency
`rw` uses. -/
@[reducible]
def cofixAlgebra : Algebra (qpfFunctor (F := F)) where
  a := QPF.Cofix F
  str := ↾ fun t => cofixMk (asF (F := F) t)

theorem cofixAlgebra_str_apply (t : F (QPF.Cofix F)) :
    cofixAlgebra.str (toObj (F := F) t) = cofixMk t := by
  unfold cofixAlgebra
  rw [TypeCat.ofHom_apply]
  exact congrArg cofixMk (asF_toObj t)

/-- `iota` is the fold of the Lambek algebra of `QPF.Cofix`. -/
theorem iota_eq_fixFold : iota (F := F) = fixFold cofixAlgebra := by
  have hrec : QPF.Fix.rec (F := F) cofixMk = iota := by
    apply QPF.Fix.rec_unique (F := F)
    intro x
    have hdest : QPF.Cofix.dest (F := F) (iota (QPF.Fix.mk x)) = iota <$> x := by
      rw [iota, QPF.Cofix.dest_corec, QPF.Fix.dest_mk]
    rw [← cofixMk_dest (iota (QPF.Fix.mk x)), hdest]
  have hg : (fun t : F (QPF.Cofix F) => cofixAlgebra.str (toObj (F := F) t)) = cofixMk := by
    funext t
    exact cofixAlgebra_str_apply t
  unfold fixFold
  rw [hg]
  exact hrec.symm

/-- `iota` is the underlying map of the unique algebra morphism into the
Lambek algebra of `QPF.Cofix`. -/
theorem iota_eq_fixHom : (fixHom cofixAlgebra).f = ↾ iota (F := F) := by
  unfold fixHom
  exact congrArg (fun g : QPF.Fix F → QPF.Cofix F => ↾ g) iota_eq_fixFold.symm

/-- The support fold is a coalgebra morphism into `QPF.Fix`. -/
noncomputable def foldHom (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) : V ⟶ fixCoalgebra where
  f := ↾ supportFold hU V hwf fixAlgebra
  h := by
    apply ConcreteCategory.hom_ext
    intro a
    apply asF_injective (α := QPF.Fix F)
    have hsol := ConcreteCategory.congr_hom (supportFold_solution hU V hwf fixAlgebra) a
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hsol
    have hstr := fixAlgebra_str_apply
      (qpfFunctor.map (↾ supportFold hU V hwf fixAlgebra) (V.str a))
    have hdest : QPF.Fix.dest (supportFold hU V hwf fixAlgebra a) =
        asF (F := F) (qpfFunctor.map (↾ supportFold hU V hwf fixAlgebra) (V.str a)) := by
      have happ : (↾ supportFold hU V hwf fixAlgebra) a =
          supportFold hU V hwf fixAlgebra a := TypeCat.ofHom_apply _ _
      rw [← happ, ← hsol, hstr]
      exact QPF.Fix.dest_mk _
    calc
      asF (F := F) (qpfFunctor.map (↾ supportFold hU V hwf fixAlgebra) (V.str a))
          = QPF.Fix.dest (supportFold hU V hwf fixAlgebra a) := hdest.symm
      _ = asF (F := F) (toObj (F := F) (QPF.Fix.dest (supportFold hU V hwf fixAlgebra a))) :=
          (asF_toObj _).symm
      _ = asF (F := F) (fixCoalgebra.str (supportFold hU V hwf fixAlgebra a)) := by
          unfold fixCoalgebra
          rw [TypeCat.ofHom_apply]

/-- On a well-founded coalgebra, behaviour is the meeting map after the fold. -/
theorem behaviour_eq_iota_fold (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) :
    cofixUnfold V = iota ∘ supportFold hU V hwf fixAlgebra := by
  let through : V ⟶ cofixCoalgebra := {
    f := (foldHom hU V hwf).f ≫ (↾ iota)
    h := by
      rw (config := { transparency := .default }) [Functor.map_comp]
      calc
        V.str ≫ qpfFunctor.map (foldHom hU V hwf).f ≫
            qpfFunctor.map (X := QPF.Fix F) (Y := QPF.Cofix F) (↾ iota)
            = ((foldHom hU V hwf).f ≫ fixCoalgebra.str) ≫
                qpfFunctor.map (X := QPF.Fix F) (Y := QPF.Cofix F) (↾ iota) := by
              rw (config := { transparency := .default }) [← Category.assoc, (foldHom hU V hwf).h]
        _ = (foldHom hU V hwf).f ≫
            (fixCoalgebra.str ≫
              qpfFunctor.map (X := QPF.Fix F) (Y := QPF.Cofix F) (↾ iota)) := by
              rw (config := { transparency := .default }) [Category.assoc]
        _ = (foldHom hU V hwf).f ≫ ((↾ iota) ≫ cofixCoalgebra.str) := by
              rw (config := { transparency := .default }) [iota_hom]
        _ = ((foldHom hU V hwf).f ≫ (↾ iota)) ≫ cofixCoalgebra.str := by
              rw (config := { transparency := .default }) [← Category.assoc] }
  have hid := cofixHom_unique V (cofixHom V) through
  funext a
  have happ := ConcreteCategory.congr_hom (congrArg Coalgebra.Hom.f hid) a
  simpa [cofixHom, through, foldHom, CategoryTheory.comp_apply] using happ

/-! ## Image of the meeting map -/

/-- Children in `QPF.Cofix`, read along the coalgebra structure. -/
def cofixChild (x y : QPF.Cofix F) : Prop :=
  child cofixCoalgebra x y

/-- Predecessor along an accessible chain. -/
theorem accInv {y z : QPF.Cofix F} (h : Acc cofixChild y) (hz : cofixChild z y) :
    Acc cofixChild z :=
  h.inv hz

/-- The accessible part of `QPF.Cofix`. -/
abbrev Accessible : Type u := {y : QPF.Cofix F // Acc cofixChild y}

/-- The child relation of the accessible part. -/
def accRel (a b : Accessible (F := F)) : Prop := cofixChild (F := F) a.1 b.1

theorem accRel_wf : WellFounded (accRel (F := F)) := by
  have hacc : ∀ z (hz : Acc cofixChild z),
      Acc (accRel (F := F)) (⟨z, hz⟩ : Accessible (F := F)) := by
    intro z hz
    induction hz with
    | intro z h ih =>
        refine Acc.intro _ ?_
        intro y hy
        have hy' : y = ⟨y.1, h y.1 hy⟩ := Subtype.ext rfl
        rw [hy']
        exact ih y.1 hy
  exact ⟨fun a => hacc a.1 a.2⟩

noncomputable def accessibleChildren (hU : QPF.IsUniform (F := F)) (y : Accessible (F := F)) :
    F (Accessible (F := F)) :=
  (fun c : {c // child cofixCoalgebra c y.1} => (⟨c.1, accInv y.2 c.2⟩ : Accessible)) <$>
    suppWitness hU cofixCoalgebra y.1

@[reducible] noncomputable def accessibleCoalgebra (hU : QPF.IsUniform (F := F)) :
    Coalgebra (qpfFunctor (F := F)) where
  V := Accessible
  str := ↾ fun y => toObj (F := F) (accessibleChildren hU y)

theorem accessible_children_spec (hU : QPF.IsUniform (F := F)) (y : Accessible (F := F)) :
    Subtype.val <$> accessibleChildren hU y = QPF.Cofix.dest y.1 := by
  unfold accessibleChildren
  rw (config := { transparency := .default }) [← comp_map]
  have hcomp :
      (Subtype.val ∘ fun c : {c // child cofixCoalgebra c y.1} =>
        (⟨c.1, accInv y.2 c.2⟩ : Accessible (F := F))) = Subtype.val := by
    funext c
    rfl
  rw (config := { transparency := .default }) [hcomp, suppWitness_spec, cofix_str_dest]

/-- The inclusion of the accessible part is a coalgebra morphism. -/
def accessibleIncl (hU : QPF.IsUniform (F := F)) :
    accessibleCoalgebra hU ⟶ cofixCoalgebra where
  f := ↾ (show (accessibleCoalgebra hU).V → cofixCoalgebra.V from Subtype.val)
  h := by
    apply ConcreteCategory.hom_ext
    intro y
    apply asF_injective (α := QPF.Cofix F)
    simp only [CategoryTheory.comp_apply, TypeCat.ofHom_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, accessibleCoalgebra, cofixCoalgebra, asF_eq, toObj_eq]
    exact accessible_children_spec hU y

theorem accessibleIncl_mono (hU : QPF.IsUniform (F := F)) : Mono (accessibleIncl hU).f :=
  (mono_iff_injective _).mpr Subtype.val_injective

theorem accessibleCoalgebra_wellFounded (hU : QPF.IsUniform (F := F)) :
    IsWellFounded (accessibleCoalgebra hU) := by
  intro P hP a
  apply accRel_wf.induction a
  intro a ih
  apply hP
  rw [mem_next_iff_liftp]
  let emb : {c // child cofixCoalgebra c a.1} → Subtype P :=
    fun c => ⟨⟨c.1, accInv a.2 c.2⟩, ih ⟨c.1, accInv a.2 c.2⟩ c.2⟩
  refine ⟨emb <$> suppWitness hU cofixCoalgebra a.1, ?_⟩
  rw (config := { transparency := .default }) [← comp_map]
  have hcomp : (Subtype.val ∘ emb) =
      fun c : {c // child cofixCoalgebra c a.1} =>
        (⟨c.1, accInv a.2 c.2⟩ : Accessible (F := F)) := by
    funext c
    rfl
  rw (config := { transparency := .default }) [hcomp]
  unfold accessibleCoalgebra accessibleChildren
  rw [TypeCat.ofHom_apply, asF_eq, toObj_eq]

/-- Fold the accessible part back into `QPF.Fix`. -/
noncomputable def recover (hU : QPF.IsUniform (F := F)) : Accessible (F := F) → QPF.Fix F :=
  WellFounded.fix (accRel_wf) fun y rec =>
    QPF.Fix.mk (asF (F := F) (qpfFunctor.map
      (↾ fun x : {x : Accessible (F := F) // (accRel (F := F)) x y} => rec x.1 x.2)
      (toObj (F := F) ((fun c : {c // child cofixCoalgebra c y.1} =>
        (⟨⟨c.1, accInv y.2 c.2⟩, c.2⟩ :
          {x : Accessible (F := F) // (accRel (F := F)) x y})) <$>
            suppWitness hU cofixCoalgebra y.1))))

theorem recover_eq (hU : QPF.IsUniform (F := F)) (y : Accessible) :
    recover hU y =
      QPF.Fix.mk (asF (F := F) (qpfFunctor.map
        (↾ fun x : {x : Accessible // accRel x y} => recover hU x.1)
        (toObj (F := F) ((fun c : {c // child cofixCoalgebra c y.1} =>
          (⟨⟨c.1, accInv y.2 c.2⟩, c.2⟩ :
            {x : Accessible // accRel x y})) <$> suppWitness hU cofixCoalgebra y.1)))) := by
  unfold recover
  rw [WellFounded.fix_eq]

theorem recover_proof_irrel (hU : QPF.IsUniform (F := F)) {z : QPF.Cofix F}
    (h₁ h₂ : Acc cofixChild z) :
    recover hU ⟨z, h₁⟩ = recover hU ⟨z, h₂⟩ := by
  have : (⟨z, h₁⟩ : Accessible) = ⟨z, h₂⟩ := Subtype.ext rfl
  exact congrArg (recover hU) this

/-- Every accessible state is the meeting image of its recovery. -/
theorem iota_recover (hU : QPF.IsUniform (F := F)) (y : Accessible) :
    iota (recover hU y) = y.1 := by
  apply accRel_wf.induction y
  intro y ih
  rw [recover_eq]
  apply cofix_dest_injective
  rw (config := { transparency := .default }) [iota, QPF.Cofix.dest_corec, QPF.Fix.dest_mk,
    map_asF, asF_toObj]
  rw (config := { transparency := .default }) [← comp_map, ← comp_map]
  have hstep :
      ((fun x : {x : Accessible (F := F) // (accRel (F := F)) x y} =>
          iota (recover hU x.1)) ∘
        fun c : {c // child cofixCoalgebra c y.1} =>
          (⟨⟨c.1, accInv y.2 c.2⟩, c.2⟩ :
            {x : Accessible (F := F) // (accRel (F := F)) x y})) = Subtype.val := by
    funext c
    exact ih ⟨c.1, accInv y.2 c.2⟩ c.2
  rw (config := { transparency := .default }) [hstep, suppWitness_spec, cofix_str_dest]

/-- Every constructed state is accessible in `QPF.Cofix`. -/
theorem iota_accessible (hU : QPF.IsUniform (F := F)) (x : QPF.Fix F) :
    Acc cofixChild (iota x) := by
  revert x
  apply QPF.Fix.ind
  intro y hy
  refine Acc.intro (iota (QPF.Fix.mk y)) ?_
  intro z hz
  have hdest : QPF.Cofix.dest (iota (QPF.Fix.mk y)) = iota <$> y := by
    rw [iota, QPF.Cofix.dest_corec, QPF.Fix.dest_mk]
  have hz' : z ∈ supp (iota <$> y) := by
    unfold cofixChild child at hz
    rw [cofix_str_dest, hdest] at hz
    exact hz
  rw [QPF.supp_map hU iota y] at hz'
  obtain ⟨c, hc, rfl⟩ := hz'
  rw [QPF.liftp_iff_of_isUniform hU y (fun c => Acc cofixChild (iota c))] at hy
  exact hy c hc

/-- A total inverse of `iota` on its image, using a fallback off that image. -/
noncomputable def invAt (hU : QPF.IsUniform (F := F)) (fallback : QPF.Fix F)
    (z : QPF.Cofix F) : QPF.Fix F :=
  @dite _ (Acc cofixChild z) (Classical.propDecidable _)
    (fun h => recover hU ⟨z, h⟩) (fun _ => fallback)

theorem invAt_iota (hU : QPF.IsUniform (F := F)) (fallback : QPF.Fix F) (x : QPF.Fix F) :
    invAt hU fallback (iota x) = recover hU ⟨iota x, iota_accessible hU x⟩ := by
  unfold invAt
  split_ifs with hAcc
  · exact recover_proof_irrel hU hAcc (iota_accessible hU x)
  · exact absurd (iota_accessible hU x) hAcc

theorem recover_iota (hU : QPF.IsUniform (F := F)) (x : QPF.Fix F) :
    recover hU ⟨iota x, iota_accessible hU x⟩ = x := by
  revert x
  apply QPF.Fix.ind
  intro y hy
  rw [QPF.liftp_iff_of_isUniform hU y
    (fun c => recover hU ⟨iota c, iota_accessible hU c⟩ = c)] at hy
  rw [recover_eq]
  apply congrArg QPF.Fix.mk
  rw [map_asF, asF_toObj]
  let g : QPF.Cofix F → QPF.Fix F := invAt hU (QPF.Fix.mk y)
  have hginv : ∀ c ∈ supp y, g (iota c) = c := by
    intro c hc
    change invAt hU (QPF.Fix.mk y) (iota c) = c
    rw [invAt_iota]
    exact hy c hc
  have hpull : g <$> (iota <$> y) = y := by
    rw [← comp_map]
    have : (g ∘ iota) <$> y = id <$> y :=
      map_agree_on_supp hU (g ∘ iota) id y hginv
    simpa [id_map] using this
  have hwitness := suppWitness_spec hU cofixCoalgebra (iota (QPF.Fix.mk y))
  have hdest : asF (F := F) (cofixCoalgebra.str (iota (QPF.Fix.mk y))) = iota <$> y := by
    rw [cofix_str_dest, iota, QPF.Cofix.dest_corec, QPF.Fix.dest_mk]
  rw [hdest] at hwitness
  let step : {c // child cofixCoalgebra c (iota (QPF.Fix.mk y))} → QPF.Fix F :=
    fun c => recover hU ⟨c.1, accInv (iota_accessible hU (QPF.Fix.mk y)) c.2⟩
  have hstep : ∀ c ∈ supp (suppWitness hU cofixCoalgebra (iota (QPF.Fix.mk y))),
      step c = g c.1 := by
    intro c hc
    have hval : c.1 ∈ supp (Subtype.val <$> suppWitness hU cofixCoalgebra
        (iota (QPF.Fix.mk y))) := by
      rw [QPF.supp_map hU Subtype.val]
      exact ⟨c, hc, rfl⟩
    rw [hwitness, QPF.supp_map hU iota y] at hval
    obtain ⟨d, hd, hd'⟩ := hval
    have hgd : g (iota d) = d := hginv d hd
    have hrec : step c = d := by
      have hc1 : c.1 = iota d := hd'.symm
      have hsub :
          (⟨c.1, accInv (iota_accessible hU (QPF.Fix.mk y)) c.2⟩ : Accessible (F := F)) =
            ⟨iota d, iota_accessible hU d⟩ :=
        Subtype.ext hc1
      unfold step
      exact (congrArg (recover hU) hsub).trans (hy d hd)
    rw [hrec, ← hgd, hd']
  have hmap := map_agree_on_supp hU step (fun c => g c.1)
    (suppWitness hU cofixCoalgebra (iota (QPF.Fix.mk y))) hstep
  -- `recover_eq` leaves two nested maps. Their composition is `step`.
  rw [← comp_map]
  have hfuse :
      ((fun x : {x : Accessible (F := F) //
            (accRel (F := F)) x ⟨iota (QPF.Fix.mk y), iota_accessible hU (QPF.Fix.mk y)⟩} =>
          recover hU x.1) ∘
        fun c : {c // child cofixCoalgebra c (iota (QPF.Fix.mk y))} =>
          (⟨⟨c.1, accInv (iota_accessible hU (QPF.Fix.mk y)) c.2⟩, c.2⟩ :
            {x : Accessible (F := F) //
              (accRel (F := F)) x ⟨iota (QPF.Fix.mk y), iota_accessible hU (QPF.Fix.mk y)⟩})) =
        step := by
    funext c
    rfl
  rw [hfuse]
  calc
    step <$> suppWitness hU cofixCoalgebra (iota (QPF.Fix.mk y))
        = (fun c => g c.1) <$> suppWitness hU cofixCoalgebra (iota (QPF.Fix.mk y)) := hmap
    _ = g <$> (Subtype.val <$> suppWitness hU cofixCoalgebra (iota (QPF.Fix.mk y))) := by
          rw (config := { transparency := .default }) [← comp_map]
          rfl
    _ = g <$> (iota <$> y) := by rw [hwitness]
    _ = y := hpull

/-- The meeting map is injective for a uniform quotient. -/
theorem iota_injective (hU : QPF.IsUniform (F := F)) :
    Function.Injective (iota (F := F)) := by
  intro x y hxy
  have hx := recover_iota hU x
  have hy := recover_iota hU y
  have hacc : (⟨iota x, iota_accessible hU x⟩ : Accessible (F := F)) =
      ⟨iota y, iota_accessible hU y⟩ :=
    Subtype.ext hxy
  exact hx.symm.trans ((congrArg (recover hU) hacc).trans hy)

theorem mem_image_iff_accessible (hU : QPF.IsUniform (F := F)) (y : QPF.Cofix F) :
    (∃ x : QPF.Fix F, iota x = y) ↔ Acc cofixChild y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact iota_accessible hU x
  · intro hy
    exact ⟨recover hU ⟨y, hy⟩, iota_recover hU ⟨y, hy⟩⟩

theorem behaviour_mem_accessible (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) (a : V.V) : Acc cofixChild (cofixUnfold V a) := by
  apply (wellFounded_child hU V hwf).induction a
  intro a ih
  refine Acc.intro (cofixUnfold V a) ?_
  intro z hz
  have hz' : z ∈ supp (cofixUnfold V <$> asF (F := F) (V.str a)) := by
    unfold cofixChild child at hz
    rw [cofix_str_dest, cofixUnfold_dest] at hz
    exact hz
  rw [QPF.supp_map hU (cofixUnfold V)] at hz'
  obtain ⟨c, hc, rfl⟩ := hz'
  exact ih c hc

theorem wf_hom_mem_accessible (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) (φ : V ⟶ cofixCoalgebra) (a : V.V) :
    Acc cofixChild (φ.f a) := by
  have hid := cofixHom_unique V φ (cofixHom V)
  have happ := ConcreteCategory.congr_hom (congrArg Coalgebra.Hom.f hid) a
  rw [cofixHom] at happ
  have : (φ.f : V.V → QPF.Cofix F) a = cofixUnfold V a := by
    simpa [TypeCat.ofHom_apply] using happ
  rw [this]
  exact behaviour_mem_accessible hU V hwf a

/-- Behaviour of a well-founded coalgebra lands in the accessible part, and the
inclusion of that part recovers behaviour. -/
theorem behaviour_factors_through_accessible (hU : QPF.IsUniform (F := F))
    (V : Coalgebra (qpfFunctor (F := F))) (hwf : IsWellFounded V) :
    Factors (fun a => (⟨cofixUnfold V a, behaviour_mem_accessible hU V hwf a⟩ : Accessible))
      (cofixUnfold V) :=
  ⟨Subtype.val, fun _ => rfl⟩

/-! ## Construction and behaviour factor through each other -/

/-- The two views of a well-founded coalgebra. -/
inductive ViewSide where
  | construction
  | behaviour

/-- Construction lands in `QPF.Fix`. Behaviour lands in the accessible part. -/
abbrev wfCod (s : ViewSide) : Type u :=
  match s with
  | .construction => QPF.Fix F
  | .behaviour => Accessible (F := F)

noncomputable def wfView (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) : (s : ViewSide) → V.V →
      match s with
      | ViewSide.construction => QPF.Fix F
      | ViewSide.behaviour => Accessible (F := F)
  | ViewSide.construction, a => supportFold hU V hwf fixAlgebra a
  | ViewSide.behaviour, a => ⟨cofixUnfold V a, behaviour_mem_accessible hU V hwf a⟩

theorem construction_finest (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) : Finest (wfView hU V hwf) .construction := by
  intro s
  cases s with
  | construction =>
      exact ⟨id, fun _ => rfl⟩
  | behaviour =>
      refine ⟨fun x => (⟨iota x, iota_accessible hU x⟩ : Accessible (F := F)), ?_⟩
      intro a
      apply Subtype.ext
      exact (congrFun (behaviour_eq_iota_fold hU V hwf) a).symm

theorem behaviour_finest (hU : QPF.IsUniform (F := F)) (V : Coalgebra (qpfFunctor (F := F)))
    (hwf : IsWellFounded V) : Finest (wfView hU V hwf) .behaviour := by
  intro s
  cases s with
  | behaviour =>
      exact ⟨id, fun _ => rfl⟩
  | construction =>
      refine ⟨recover hU, ?_⟩
      intro a
      show recover hU ⟨cofixUnfold V a, behaviour_mem_accessible hU V hwf a⟩ =
        supportFold hU V hwf fixAlgebra a
      have hbeh : cofixUnfold V a = iota (supportFold hU V hwf fixAlgebra a) :=
        congrFun (behaviour_eq_iota_fold hU V hwf) a
      have hrec := recover_iota hU (supportFold hU V hwf fixAlgebra a)
      have hsub :
          (⟨cofixUnfold V a, behaviour_mem_accessible hU V hwf a⟩ : Accessible (F := F)) =
            ⟨iota (supportFold hU V hwf fixAlgebra a),
              iota_accessible hU (supportFold hU V hwf fixAlgebra a)⟩ :=
        Subtype.ext hbeh
      exact (congrArg (recover hU) hsub).trans hrec

end Mettapedia.Coalgebra.InitialFinal

