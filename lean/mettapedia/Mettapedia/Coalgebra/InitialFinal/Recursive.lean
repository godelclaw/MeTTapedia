import Mettapedia.Coalgebra.InitialFinal.WellFounded

/-!
# Recursive coalgebras

A coalgebra is recursive when every algebra receives exactly one
coalgebra-to-algebra morphism. Inductive well-foundedness yields uniqueness
of that morphism for every endofunctor of types. Existence is not claimed
here.

The Lambek coalgebra of an initial algebra is a final recursive coalgebra,
and the Lambek algebra of a final recursive coalgebra is initial. The two
notions therefore coincide for every endofunctor of types. The argument is
the one recorded by Adámek, Milius, Moss, and Sousa, *Well-pointed
coalgebras*, Remark 2.37, following Capretta, Uustalu, and Vene, *Recursive
coalgebras from comonads*: the image of a recursive coalgebra under `F` is
recursive, and an endomorphism of a final recursive coalgebra is the
identity.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.InitialFinal

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits

universe u

variable {F : Type u ⥤ Type u}

/-- `h` solves the recursion equation of coalgebra `V` into algebra `A`. -/
def IsSolution (V : Coalgebra F) (A : Algebra F) (h : V.V ⟶ A.a) : Prop :=
  V.str ≫ F.map h ≫ A.str = h

/-- Every algebra receives exactly one solution. -/
def IsRecursive (V : Coalgebra F) : Prop :=
  ∀ A : Algebra F, ∃ h : V.V ⟶ A.a, IsSolution V A h ∧
    ∀ h' : V.V ⟶ A.a, IsSolution V A h' → h' = h

/-- A recursive coalgebra that receives exactly one coalgebra morphism from
every recursive coalgebra. -/
def IsFinalRecursive (V : Coalgebra F) : Prop :=
  IsRecursive V ∧
    ∀ W : Coalgebra F, IsRecursive W → ∃ φ : W ⟶ V, ∀ ψ : W ⟶ V, ψ = φ

theorem finalRecursive_hom_unique {V W : Coalgebra F} (h : IsFinalRecursive V)
    (hW : IsRecursive W) (φ ψ : W ⟶ V) : φ = ψ := by
  obtain ⟨ρ, hρ⟩ := h.2 W hW
  exact (hρ φ).trans (hρ ψ).symm

/-- Inductive well-foundedness yields at most one solution, for every
endofunctor. The equalizer of two solutions is inductive. -/
theorem wellFounded_solution_unique {V : Coalgebra F} (hwf : IsWellFounded V)
    (A : Algebra F) {h₁ h₂ : V.V ⟶ A.a} (s₁ : IsSolution V A h₁)
    (s₂ : IsSolution V A h₂) : h₁ = h₂ := by
  let P : Set V.V := {a | h₁ a = h₂ a}
  have hind : Inductive V P := by
    intro a ⟨t, ht⟩
    have apply₁ : h₁ a = A.str (F.map h₁ (V.str a)) := by
      have happ := ConcreteCategory.congr_hom s₁ a
      simp only [CategoryTheory.comp_apply] at happ
      exact happ.symm
    have apply₂ : h₂ a = A.str (F.map h₂ (V.str a)) := by
      have happ := ConcreteCategory.congr_hom s₂ a
      simp only [CategoryTheory.comp_apply] at happ
      exact happ.symm
    have hagree : inclusion P ≫ h₁ = inclusion P ≫ h₂ := by
      apply ConcreteCategory.hom_ext
      intro x
      exact x.2
    have hmap := congrArg (fun f : Subtype P ⟶ A.a => (F.map f) t) hagree
    rw [F.map_comp, CategoryTheory.comp_apply, F.map_comp, CategoryTheory.comp_apply] at hmap
    rw [ht] at hmap
    have heq : h₁ a = h₂ a := by
      rw [apply₁, apply₂, hmap]
    simpa only [P, Set.mem_ofPred_eq] using heq
  apply ConcreteCategory.hom_ext
  intro a
  exact hwf P hind a

/-- The coalgebra `F` sends `V` to. Reducible so the carrier `F.obj V.V`
stays definitional at the transparency `rw` uses. -/
@[reducible]
def mapCoalgebra (V : Coalgebra F) : Coalgebra F where
  V := F.obj V.V
  str := F.map V.str

theorem solution_apply {V : Coalgebra F} {A : Algebra F} {h : V.V ⟶ A.a}
    (s : IsSolution V A h) (a : V.V) :
    h a = A.str (F.map h (V.str a)) := by
  have happ := ConcreteCategory.congr_hom s a
  simp only [CategoryTheory.comp_apply] at happ
  exact happ.symm

/-- `F` preserves recursive coalgebras. -/
theorem mapCoalgebra_recursive {V : Coalgebra F} (hV : IsRecursive V) :
    IsRecursive (mapCoalgebra V) := by
  intro A
  obtain ⟨h, hs, huniq⟩ := hV A
  let k : (mapCoalgebra V).V ⟶ A.a := F.map h ≫ A.str
  have hk_apply (y : F.obj V.V) : k y = A.str (F.map h y) := by
    simp [k, CategoryTheory.comp_apply]
  have h_eq_k : h = V.str ≫ k := by
    apply ConcreteCategory.hom_ext
    intro a
    rw [CategoryTheory.comp_apply, hk_apply, solution_apply hs]
  have hsol : IsSolution (mapCoalgebra V) A k := by
    apply ConcreteCategory.hom_ext
    intro y
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hk_apply]
    have : F.map k (F.map V.str y) = F.map h y := by
      have hfun : V.str ≫ k = h := h_eq_k.symm
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, hfun]
    rw [this]
  refine ⟨k, hsol, ?_⟩
  intro k' hk'
  apply ConcreteCategory.hom_ext
  intro y
  have hcomp' : V.str ≫ k' = h := by
    apply huniq
    apply ConcreteCategory.hom_ext
    intro a
    simp only [CategoryTheory.comp_apply]
    have happ := solution_apply hk' (V.str a)
    rw [Functor.map_comp, CategoryTheory.comp_apply]
    exact happ.symm
  have hfun : F.map V.str ≫ F.map k' = F.map h := by
    rw [← F.map_comp, hcomp']
  have hinner := ConcreteCategory.congr_hom hfun y
  simp only [CategoryTheory.comp_apply] at hinner
  have hstr : (mapCoalgebra V).str y = F.map V.str y := rfl
  rw [solution_apply hk' y, hstr, hinner, hk_apply]

theorem coalgebraOfInitial_solution {A : Algebra F} (hA : Limits.IsInitial A)
    (B : Algebra F) :
    IsSolution (coalgebraOfInitial hA) B (hA.to B).f ∧
      ∀ h' : (coalgebraOfInitial hA).V ⟶ B.a,
        IsSolution (coalgebraOfInitial hA) B h' → h' = (hA.to B).f := by
  let f : A ⟶ B := hA.to B
  have hsol : IsSolution (coalgebraOfInitial hA) B f.f := by
    -- `strInv ≫ F.map f ≫ B.str = strInv ≫ A.str ≫ f = f`
    have halg : F.map f.f ≫ B.str = A.str ≫ f.f := f.h
    calc
      (coalgebraOfInitial hA).str ≫ F.map f.f ≫ B.str
          = (coalgebraOfInitial hA).str ≫ (A.str ≫ f.f) := by rw [halg]
      _ = ((coalgebraOfInitial hA).str ≫ A.str) ≫ f.f := by rw [Category.assoc]
      _ = 𝟙 _ ≫ f.f := by rw [coalgebraOfInitial_str_left_inv]
      _ = f.f := Category.id_comp _
  refine ⟨hsol, ?_⟩
  intro h' hs'
  let h'alg : A ⟶ B := {
    f := h'
    h := by
      calc
        F.map h' ≫ B.str
            = 𝟙 _ ≫ F.map h' ≫ B.str := by rw [Category.id_comp]
        _ = (A.str ≫ (coalgebraOfInitial hA).str) ≫ F.map h' ≫ B.str := by
          rw [coalgebraOfInitial_str_right_inv]
        _ = A.str ≫ ((coalgebraOfInitial hA).str ≫ F.map h' ≫ B.str) := by
          rw [Category.assoc]
        _ = A.str ≫ h' := by rw [hs'] }
  exact congrArg Algebra.Hom.f (IsInitial.hom_ext hA h'alg f)

/-- The Lambek coalgebra of an initial algebra is recursive. -/
theorem coalgebraOfInitial_recursive {A : Algebra F} (hA : Limits.IsInitial A) :
    IsRecursive (coalgebraOfInitial hA) := by
  intro B
  obtain ⟨hsol, huniq⟩ := coalgebraOfInitial_solution hA B
  exact ⟨(hA.to B).f, hsol, huniq⟩

/-- The Lambek coalgebra of an initial algebra is the final recursive
coalgebra. -/
theorem coalgebraOfInitial_finalRecursive {A : Algebra F} (hA : Limits.IsInitial A) :
    IsFinalRecursive (coalgebraOfInitial hA) := by
  refine ⟨coalgebraOfInitial_recursive hA, ?_⟩
  intro W hW
  obtain ⟨h, hs, huniq⟩ := hW A
  have hhom : W.str ≫ F.map h = h ≫ (coalgebraOfInitial hA).str := by
    have hright := coalgebraOfInitial_str_right_inv hA
    calc
      W.str ≫ F.map h
          = W.str ≫ F.map h ≫ 𝟙 _ := by rw [Category.comp_id]
      _ = W.str ≫ F.map h ≫ (A.str ≫ (coalgebraOfInitial hA).str) := by rw [hright]
      _ = (W.str ≫ F.map h ≫ A.str) ≫ (coalgebraOfInitial hA).str := by
        rw [Category.assoc, Category.assoc]
      _ = h ≫ (coalgebraOfInitial hA).str := by rw [hs]
  let φ : W ⟶ coalgebraOfInitial hA := { f := h, h := hhom }
  refine ⟨φ, ?_⟩
  intro ψ
  have hψsol : IsSolution W A ψ.f := by
    calc
      W.str ≫ F.map ψ.f ≫ A.str
          = (W.str ≫ F.map ψ.f) ≫ A.str := by rw [Category.assoc]
      _ = (ψ.f ≫ (coalgebraOfInitial hA).str) ≫ A.str := by rw [ψ.h]
      _ = ψ.f ≫ ((coalgebraOfInitial hA).str ≫ A.str) := by rw [Category.assoc]
      _ = ψ.f ≫ 𝟙 _ := by rw [coalgebraOfInitial_str_left_inv]
      _ = ψ.f := Category.comp_id _
  have hf : ψ.f = h := huniq ψ.f hψsol
  apply Coalgebra.Hom.ext
  exact hf

/-! ## A final recursive coalgebra is an initial algebra -/

/-- The unique coalgebra morphism from `F V` into a final recursive coalgebra.
It is the inverse of the structure map. -/
noncomputable def lambekInverse {V : Coalgebra F} (h : IsFinalRecursive V) :
    (mapCoalgebra V) ⟶ V :=
  Classical.choose (h.2 (mapCoalgebra V) (mapCoalgebra_recursive h.1))

theorem lambekInverse_spec {V : Coalgebra F} (h : IsFinalRecursive V)
    (ψ : mapCoalgebra V ⟶ V) : ψ = lambekInverse h :=
  Classical.choose_spec (h.2 (mapCoalgebra V) (mapCoalgebra_recursive h.1)) ψ

theorem lambekInverse_right_inv {V : Coalgebra F} (h : IsFinalRecursive V) :
    V.str ≫ (lambekInverse h).f = 𝟙 V.V := by
  let ψ : V ⟶ V := {
    f := V.str ≫ (lambekInverse h).f
    h := by
      have hφ := (lambekInverse h).h
      -- `F.map V.str ≫ F.map φ = φ ≫ V.str`
      calc
        V.str ≫ F.map (V.str ≫ (lambekInverse h).f)
            = V.str ≫ (F.map V.str ≫ F.map (lambekInverse h).f) := by
              rw [Functor.map_comp]
        _ = V.str ≫ ((lambekInverse h).f ≫ V.str) := by rw [hφ]
        _ = (V.str ≫ (lambekInverse h).f) ≫ V.str := by rw [Category.assoc] }
  have hid : ψ = 𝟙 V := finalRecursive_hom_unique h h.1 ψ (𝟙 V)
  change ψ.1 = 𝟙 V.1
  simpa only [Coalgebra.id_f] using congrArg (fun (ρ : V ⟶ V) => ρ.1) hid

theorem lambekInverse_left_inv {V : Coalgebra F} (h : IsFinalRecursive V) :
    (lambekInverse h).f ≫ V.str = 𝟙 (F.obj V.V) := by
  have hφ := (lambekInverse h).h
  -- `F.map V.str ≫ F.map φ = φ ≫ V.str`, and `V.str ≫ φ = 1`, so `φ ≫ V.str = 1`.
  have : F.map (V.str ≫ (lambekInverse h).f) = (lambekInverse h).f ≫ V.str := by
    rw [F.map_comp, hφ]
  rw [lambekInverse_right_inv, F.map_id] at this
  exact this.symm

/-- The Lambek algebra of a final recursive coalgebra. -/
noncomputable def algebraOfFinalRecursive {V : Coalgebra F} (h : IsFinalRecursive V) :
    Algebra F where
  a := V.V
  str := (lambekInverse h).f

theorem algebraOfFinalRecursive_str {V : Coalgebra F} (h : IsFinalRecursive V) :
    (algebraOfFinalRecursive h).str = (lambekInverse h).f :=
  rfl

theorem solution_iff_algebraHom {V : Coalgebra F} (h : IsFinalRecursive V)
    (B : Algebra F) (k : V.V ⟶ B.a) :
    IsSolution V B k ↔ F.map k ≫ B.str = (algebraOfFinalRecursive h).str ≫ k := by
  constructor
  · intro hs
    calc
      F.map k ≫ B.str
          = 𝟙 _ ≫ F.map k ≫ B.str := by rw [Category.id_comp]
      _ = ((lambekInverse h).f ≫ V.str) ≫ F.map k ≫ B.str := by
        rw [lambekInverse_left_inv]
      _ = (lambekInverse h).f ≫ (V.str ≫ F.map k ≫ B.str) := by
        rw [Category.assoc]
      _ = (lambekInverse h).f ≫ k := by rw [hs]
  · intro halg
    rw [algebraOfFinalRecursive_str] at halg
    calc
      V.str ≫ F.map k ≫ B.str
          = V.str ≫ ((lambekInverse h).f ≫ k) :=
            congrArg (fun f => V.str ≫ f) halg
      _ = (V.str ≫ (lambekInverse h).f) ≫ k := by rw [← Category.assoc]
      _ = 𝟙 _ ≫ k := by rw [lambekInverse_right_inv]
      _ = k := Category.id_comp _

/-- The chosen solution of a recursive coalgebra into an algebra. -/
noncomputable def recursiveSolution {V : Coalgebra F} (hV : IsRecursive V) (B : Algebra F) :
    V.V ⟶ B.a :=
  Classical.choose (hV B)

theorem recursiveSolution_spec {V : Coalgebra F} (hV : IsRecursive V) (B : Algebra F) :
    IsSolution V B (recursiveSolution hV B) ∧
      ∀ h' : V.V ⟶ B.a, IsSolution V B h' → h' = recursiveSolution hV B :=
  Classical.choose_spec (hV B)

/-- A final recursive coalgebra, read as an algebra along the inverse of its
structure map, is initial. -/
theorem algebraOfFinalRecursive_initial {V : Coalgebra F} (h : IsFinalRecursive V) :
    Nonempty (Limits.IsInitial (algebraOfFinalRecursive h)) := by
  refine ⟨Limits.IsInitial.ofUniqueHom
    (fun B => {
      f := recursiveSolution h.1 B
      h := (solution_iff_algebraHom h B (recursiveSolution h.1 B)).mp
        (recursiveSolution_spec h.1 B).1 })
    (fun B m => ?_)⟩
  have hm := (solution_iff_algebraHom h B m.f).mpr m.h
  have : m.f = recursiveSolution h.1 B := (recursiveSolution_spec h.1 B).2 m.f hm
  apply Algebra.Hom.ext
  exact this

/-! ## One meeting map, read both ways -/

/-- The Lambek algebra of a final coalgebra. Its structure map is the inverse
of the coalgebra structure. Reducible so the carrier `T.V` stays definitional
at the transparency `rw` uses. -/
@[reducible]
noncomputable def algebraOfTerminal {T : Coalgebra F} (hT : Limits.IsTerminal T) :
    Algebra F where
  a := T.V
  str := Coalgebra.Terminal.strInv hT

theorem algebraOfTerminal_str {T : Coalgebra F} (hT : Limits.IsTerminal T) :
    (algebraOfTerminal hT).str = Coalgebra.Terminal.strInv hT :=
  rfl

/-- When an endofunctor has both an initial algebra and a final coalgebra, the
unique coalgebra map out of the Lambek coalgebra and the unique algebra map
into the Lambek algebra are the same arrow. -/
theorem meeting_underlying_eq {A : Algebra F} (hA : Limits.IsInitial A)
    {T : Coalgebra F} (hT : Limits.IsTerminal T) :
    (hT.from (coalgebraOfInitial hA)).f = (hA.to (algebraOfTerminal hT)).f := by
  let φ : coalgebraOfInitial hA ⟶ T := hT.from (coalgebraOfInitial hA)
  have hφ :
      (coalgebraOfInitial hA).str ≫ F.map φ.f ≫ Coalgebra.Terminal.strInv hT = φ.f := by
    calc
      (coalgebraOfInitial hA).str ≫ F.map φ.f ≫ Coalgebra.Terminal.strInv hT
          = (φ.f ≫ T.str) ≫ Coalgebra.Terminal.strInv hT := by
            rw [← Category.assoc, φ.h]
      _ = φ.f ≫ (T.str ≫ Coalgebra.Terminal.strInv hT) := by
            rw [Category.assoc]
      _ = φ.f ≫ 𝟙 T.V := by
            rw [Coalgebra.Terminal.right_inv]
      _ = φ.f := by
            rw [Category.comp_id]
  let φAlg : A ⟶ algebraOfTerminal hT := {
    f := φ.f
    h := by
      rw [algebraOfTerminal_str]
      conv =>
        rhs
        rw [← hφ]
      rw [← Category.assoc]
      rw [coalgebraOfInitial_str_right_inv]
      rw [Category.id_comp] }
  have huniq : φAlg = hA.to (algebraOfTerminal hT) := hA.hom_ext φAlg _
  exact congrArg Algebra.Hom.f huniq

end Mettapedia.Coalgebra.InitialFinal


