import Mathlib.CategoryTheory.Elements
import Mettapedia.Logic.WorldModel.Indexed.FixedQueryBridge

/-!
# Dependent answer types

The evidence of a question may depend on the question: a count is answered by
a number, a binary question by a pair of counts.  The general evidence functor
is therefore a presheaf on the category of elements of the query functor,
`E : (Q.Elements)ᵒᵖ ⥤ AddCommMonCat`, and the profiles at a world are the
dependent functions `∀ q : Q b, E (b, q)` (`dependentProfileFunctor`).
Restriction along `f` reads the answer to `Q f q` back along the element arrow
`(b, q) ⟶ (c, Q f q)`.

* Evidence that depends only on the world is the special case
  `E = π.op ⋙ E'`, and gives back `profileFunctor Q E'`
  (`dependentProfileFunctor_of_world`).
* Over the one-world base with one count question and one binary question, a
  state of counts is a world model with heterogeneous answers (`demoModel`);
  its identity is a morphism (`demo_identity_hom`) and swapping the binary
  counts is not (`demo_swap_not_hom`).
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed

universe vB uB u

section Dependent

variable {B : Type uB} [Category.{vB} B] (Q : B ⥤ Type u)
variable (E : (Q.Elements)ᵒᵖ ⥤ AddCommMonCat.{u})

/-- The element arrow of a world arrow at a question. -/
def elementArrow {b c : B} (f : b ⟶ c) (q : Q.obj b) :
    Q.elementsMk b q ⟶ Q.elementsMk c (Q.map f q) :=
  ⟨f, rfl⟩

/-- Reading back along two element arrows with the same world arrow and equal
targets gives the same answer. -/
theorem map_congr_target {b d : B} {q : Q.obj b} {y₁ y₂ : Q.obj d} (h : y₁ = y₂)
    (g₁ : Q.elementsMk b q ⟶ Q.elementsMk d y₁) (g₂ : Q.elementsMk b q ⟶ Q.elementsMk d y₂)
    (hv : g₁.val = g₂.val) (p : ∀ y : Q.obj d, E.obj (op (Q.elementsMk d y))) :
    (E.map g₁.op).hom (p y₁) = (E.map g₂.op).hom (p y₂) := by
  subst h
  obtain rfl : g₁ = g₂ := Subtype.ext hv
  rfl

/-- Restriction of dependent profiles along a world arrow. -/
def restrictDependent {b c : B} (f : b ⟶ c) :
    (∀ q' : Q.obj c, E.obj (op ⟨c, q'⟩)) →+ (∀ q : Q.obj b, E.obj (op ⟨b, q⟩)) where
  toFun p q := (E.map (elementArrow Q f q).op).hom (p (Q.map f q))
  map_zero' := by
    funext q
    simp
  map_add' p p' := by
    funext q
    simp

/-- The dependent answer-profile functor. -/
def dependentProfileFunctor : Bᵒᵖ ⥤ AddCommMonCat.{u} where
  obj b := AddCommMonCat.of (∀ q : Q.obj b.unop, E.obj (op ⟨b.unop, q⟩))
  map {b c} f := AddCommMonCat.ofHom (restrictDependent Q E f.unop)
  map_id b := by
    ext p q
    show (E.map (elementArrow Q (𝟙 b.unop) q).op).hom (p (Q.map (𝟙 b.unop) q)) = p q
    rw [map_congr_target Q E (by simp) (elementArrow Q (𝟙 b.unop) q) (𝟙 _) rfl p]
    simp
  map_comp {b c d} f g := by
    ext p q
    show (E.map (elementArrow Q (g.unop ≫ f.unop) q).op).hom (p (Q.map (g.unop ≫ f.unop) q)) =
      (E.map (elementArrow Q g.unop q).op).hom
        ((E.map (elementArrow Q f.unop (Q.map g.unop q)).op).hom
          (p (Q.map f.unop (Q.map g.unop q))))
    rw [map_congr_target Q E (by simp) (elementArrow Q (g.unop ≫ f.unop) q)
      (elementArrow Q g.unop q ≫ elementArrow Q f.unop (Q.map g.unop q)) rfl p]
    simp

/-- Evidence that depends only on the world gives back the profile functor. -/
theorem dependentProfileFunctor_of_world (E' : Bᵒᵖ ⥤ AddCommMonCat.{u}) :
    dependentProfileFunctor Q ((CategoryOfElements.π Q).op ⋙ E') = profileFunctor Q E' :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by
    ext p
    rfl)

end Dependent

/-! ## Heterogeneous answers over one world -/

namespace DemoDependent

open FixedQueryBridge

/-- A count question and a binary question. -/
inductive Question
  | count
  | binary
  deriving DecidableEq

/-- Counts answer the count question; pairs of counts the binary one. -/
def Answer : Question → AddCommMonCat
  | .count => AddCommMonCat.of ℕ
  | .binary => AddCommMonCat.of (ℕ × ℕ)

/-- The two questions at the one world. -/
def questions : Point ⥤ Type := (Functor.const _).obj Question

/-- On the one-world base every element arrow is an identity on its question. -/
theorem element_arrow_question {x y : questions.Elements} (g : x ⟶ y) : x.2 = y.2 :=
  g.2

/-- Answers along element arrows: the transport along the equality of questions. -/
def answerMap {x y : questions.Elements} (g : x ⟶ y) : Answer y.2 ⟶ Answer x.2 :=
  eqToHom (congrArg Answer (element_arrow_question g).symm)

/-- The dependent evidence functor. -/
def evidence : (questions.Elements)ᵒᵖ ⥤ AddCommMonCat where
  obj x := Answer x.unop.2
  map g := answerMap g.unop
  map_id _ := by simp [answerMap]
  map_comp _ _ := by simp [answerMap]

/-- The dependent profiles at the world. -/
abbrev profiles := dependentProfileFunctor questions evidence

/-- Extraction from a count and a pair of counts. -/
def demoExtract : ℕ × (ℕ × ℕ) →+ ∀ q : Question, Answer q where
  toFun n q := match q with
    | .count => (n.1 : ℕ)
    | .binary => (n.2 : ℕ × ℕ)
  map_zero' := by funext q; cases q <;> rfl
  map_add' _ _ := by funext q; cases q <;> rfl

/-- A world model with heterogeneous answers. -/
def demoModel : Over (profiles.obj (op ⟨PUnit.unit⟩)) :=
  Over.mk (AddCommMonCat.ofHom demoExtract :
    AddCommMonCat.of (ℕ × (ℕ × ℕ)) ⟶ profiles.obj (op ⟨PUnit.unit⟩))

/-- Restriction along the identity of the world does nothing. -/
theorem profiles_map_id_apply (p : profiles.obj (op ⟨PUnit.unit⟩)) :
    (profiles.map (𝟙 (⟨PUnit.unit⟩ : Point)).op).hom p = p := by
  rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Swap the two coordinates of the binary answer. -/
def swapBinary : AddCommMonCat.of (ℕ × (ℕ × ℕ)) ⟶ AddCommMonCat.of (ℕ × (ℕ × ℕ)) :=
  AddCommMonCat.ofHom ((AddMonoidHom.fst ℕ (ℕ × ℕ)).prod
    ((AddMonoidHom.snd ℕ ℕ).prod (AddMonoidHom.fst ℕ ℕ) |>.comp (AddMonoidHom.snd ℕ (ℕ × ℕ))))

/-- Positive: the identity is a morphism of the heterogeneous world model. -/
theorem demo_identity_hom :
    𝟙 demoModel.left ≫ demoModel.hom ≫ profiles.map (𝟙 (⟨PUnit.unit⟩ : Point)).op =
      demoModel.hom := by
  ext W
  exact profiles_map_id_apply _

/-- Negative: swapping the binary counts is not a morphism; it changes the
answer to the binary question. -/
theorem demo_swap_not_hom :
    ¬ (swapBinary ≫ demoModel.hom ≫ profiles.map (𝟙 (⟨PUnit.unit⟩ : Point)).op =
      demoModel.hom) := by
  intro h
  have hmap : profiles.map (𝟙 (⟨PUnit.unit⟩ : Point)).op = 𝟙 _ := by
    rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rw [hmap] at h
  have := congrArg (fun k : AddCommMonCat.of (ℕ × (ℕ × ℕ)) ⟶ profiles.obj (op ⟨PUnit.unit⟩) =>
    k.hom ((0 : ℕ), ((1 : ℕ), (0 : ℕ))) Question.binary) h
  have pair : ((0 : ℕ), (1 : ℕ)) = ((1 : ℕ), (0 : ℕ)) := this
  exact absurd (congrArg Prod.fst pair) (by decide)

end DemoDependent

end Mettapedia.Logic.WorldModel.Indexed
