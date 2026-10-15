import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Nat.Defs

/-!
# The indexed world-model doctrine

A world model over a fixed set of questions is an additive state monoid with an
additive extraction into answer profiles; such world models form the slice of
commutative monoids over the profile monoid.  Here the framework itself varies.

* A base category `B` of semantic worlds.  An arrow `f : b ⟶ c` moves to a world
  with more questions, other evidence, or a finer observer.
* A profile functor `P : Bᵒᵖ ⥤ AddCommMonCat`: the answer profiles at each world,
  with restriction back along every arrow.  Its usual presentation is
  `P b = Q b → E b` for a query functor `Q : B ⥤ Type` (questions translate
  forward) and an evidence functor `E : Bᵒᵖ ⥤ AddCommMonCat` (evidence is read
  back); restriction is `p ↦ E f ∘ p ∘ Q f` (`profileFunctor`).
* The fibre over `b` is the slice `Over (P b)`; reindexing along `f` is
  postcomposition with the restriction (`Over.map`).  These fibres form a
  pseudofunctor `fibres P`, and the world models over all worlds form its
  co-Grothendieck construction `Total P`, fibred over `B` (`worldOf_isFibered`).

A morphism of the total category over `f : b ⟶ c` is an additive state map `h`
with `restrict_f (ext_c (h W)) = ext_b W` (`totalHomEquiv`); in the query
presentation, `E f (ext_c (h W) (Q f q)) = ext_b W q` for every question `q` of
`b` (`overArrow_iff`).

The examples at the end use the walking arrow `false ⟶ true`: an arrow that adds
a question, an arrow that changes the evidence monoid, and a state map that keeps
the old answers only under another evidence reading and is therefore not a
morphism over the arrow.
-/

set_option autoImplicit false

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory

namespace Mettapedia.Logic.WorldModel.Indexed

universe vB uB u

section Profiles

variable {B : Type uB} [Category.{vB} B]

/-- Restriction of answer profiles along a world arrow `f : b ⟶ c`: a profile at
`c` is read at `b` by translating each question of `b` forward along `Q f` and
reading the answer back along `E f`. -/
def restrictProfile (Q : B ⥤ Type u) (E : Bᵒᵖ ⥤ AddCommMonCat.{u}) {b c : B}
    (f : b ⟶ c) : (Q.obj c → E.obj (op c)) →+ (Q.obj b → E.obj (op b)) where
  toFun p q := (E.map f.op).hom (p (Q.map f q))
  map_zero' := by
    funext q
    simp
  map_add' p p' := by
    funext q
    simp

@[simp] theorem restrictProfile_apply (Q : B ⥤ Type u) (E : Bᵒᵖ ⥤ AddCommMonCat.{u})
    {b c : B} (f : b ⟶ c) (p : Q.obj c → E.obj (op c)) (q : Q.obj b) :
    restrictProfile Q E f p q = (E.map f.op).hom (p (Q.map f q)) := rfl

/-- The answer-profile functor of a query functor and an evidence functor:
`b ↦ (Q b → E b)` with pointwise addition, restricted by `restrictProfile`. -/
def profileFunctor (Q : B ⥤ Type u) (E : Bᵒᵖ ⥤ AddCommMonCat.{u}) :
    Bᵒᵖ ⥤ AddCommMonCat.{u} where
  obj b := AddCommMonCat.of (Q.obj b.unop → E.obj b)
  map {b c} f := AddCommMonCat.ofHom (restrictProfile Q E f.unop)
  map_id b := by
    ext p q
    simp [restrictProfile]
  map_comp f g := by
    ext p q
    simp [restrictProfile]

@[simp] theorem profileFunctor_map_apply (Q : B ⥤ Type u) (E : Bᵒᵖ ⥤ AddCommMonCat.{u})
    {b c : B} (f : b ⟶ c) (p : Q.obj c → E.obj (op c)) (q : Q.obj b) :
    ((profileFunctor Q E).map f.op).hom p q = (E.map f.op).hom (p (Q.map f q)) := rfl

end Profiles

section Doctrine

variable {B : Type uB} [Category.{vB} B]

/-- The fibres of the doctrine: world `b` goes to the slice of commutative
monoids over its answer profiles, and an arrow acts by postcomposition with
restriction. -/
def fibres (P : Bᵒᵖ ⥤ AddCommMonCat.{u}) : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat :=
  (P ⋙ Over.mapFunctor AddCommMonCat.{u}).toPseudofunctor'

/-- World models over all worlds: the co-Grothendieck construction of the
fibres. An object is a world together with a world model at that world. -/
abbrev Total (P : Bᵒᵖ ⥤ AddCommMonCat.{u}) := Pseudofunctor.CoGrothendieck (fibres P)

/-- The world of a world model. -/
abbrev worldOf (P : Bᵒᵖ ⥤ AddCommMonCat.{u}) : Total P ⥤ B :=
  Pseudofunctor.CoGrothendieck.forget (fibres P)

/-- The world projection is a fibred category: every world model at `c`
restricts along every arrow `b ⟶ c` by a strongly cartesian morphism. -/
theorem worldOf_isFibered (P : Bᵒᵖ ⥤ AddCommMonCat.{u}) : (worldOf P).IsFibered :=
  inferInstance

variable (P : Bᵒᵖ ⥤ AddCommMonCat.{u})

/-- A world model at world `b`, read in the slice over its profiles. -/
abbrev Total.model (X : Total P) : Over (P.obj (op X.base)) := X.fiber

/-- Package a world and a world model at it as an object of the total category. -/
abbrev Total.mk (b : B) (X : Over (P.obj (op b))) : Total P := ⟨b, X⟩

/-- Reindexing a world model along a world arrow is postcomposition of its
extraction with restriction. -/
theorem fibres_map_obj {b c : B} (f : b ⟶ c) (Y : Over (P.obj (op c))) :
    (((fibres P).map f.op.toLoc).toFunctor.obj Y : Over (P.obj (op b))) =
      Over.mk (Y.hom ≫ P.map f.op) := rfl

/-- The morphisms of world models: a world arrow together with an additive state
map whose extraction, restricted along the arrow, is the source extraction. -/
def totalHomEquiv {X Y : Total P} :
    (X ⟶ Y) ≃ Σ f : X.base ⟶ Y.base,
      {h : (Total.model P X).left ⟶ (Total.model P Y).left //
        h ≫ (Total.model P Y).hom ≫ P.map f.op = (Total.model P X).hom} where
  toFun φ := ⟨φ.base, φ.fiber.left, Over.w φ.fiber⟩
  invFun d := ⟨d.1, Over.homMk d.2.1 d.2.2⟩
  left_inv φ := by
    cases φ
    rfl
  right_inv d := by
    obtain ⟨f, h, w⟩ := d
    rfl

/-- The morphism of the total category given by a world arrow and a state map
satisfying the restriction equation. -/
def homOver {b c : B} (f : b ⟶ c) {X : Over (P.obj (op b))} {Y : Over (P.obj (op c))}
    (h : X.left ⟶ Y.left) (w : h ≫ Y.hom ≫ P.map f.op = X.hom) :
    Total.mk P b X ⟶ Total.mk P c Y :=
  ⟨f, Over.homMk h w⟩

@[simp] theorem homOver_base {b c : B} (f : b ⟶ c) {X : Over (P.obj (op b))}
    {Y : Over (P.obj (op c))} (h : X.left ⟶ Y.left)
    (w : h ≫ Y.hom ≫ P.map f.op = X.hom) : (homOver P f h w).base = f := rfl

/-- The fibre of the world projection over `b` is equivalent to the slice over
the profiles at `b`. -/
noncomputable def fibreEquivalence (b : B) :
    Over (P.obj (op b)) ≌ (worldOf P).Fiber b :=
  (Functor.Fiber.inducedFunctor
    (Pseudofunctor.CoGrothendieck.comp_const (fibres P) b)).asEquivalence

end Doctrine

section Presentation

variable {B : Type uB} [Category.{vB} B]
variable (Q : B ⥤ Type u) (E : Bᵒᵖ ⥤ AddCommMonCat.{u})

/-- In the query presentation, a state map is a morphism over `f` exactly when
every answer at the target, to a translated question, read back along `E f`, is
the source answer. -/
theorem overArrow_iff {b c : B} (f : b ⟶ c)
    (X : Over ((profileFunctor Q E).obj (op b)))
    (Y : Over ((profileFunctor Q E).obj (op c))) (h : X.left ⟶ Y.left) :
    h ≫ Y.hom ≫ (profileFunctor Q E).map f.op = X.hom ↔
      ∀ W q, (E.map f.op).hom (Y.hom.hom (h.hom W) (Q.map f q)) = X.hom.hom W q := by
  constructor
  · intro w W q
    exact congrArg (fun k : X.left ⟶ (profileFunctor Q E).obj (op b) => k.hom W q) w
  · intro w
    ext W
    funext q
    exact w W q

end Presentation

/-! ## Examples over the walking arrow -/

namespace WalkingArrow

/-- The walking arrow `false ⟶ true`, as the order category of `Bool`. -/
abbrev World := Bool

/-- The unique arrow from the smaller world to the larger one. -/
def up : (false : World) ⟶ true := homOfLE (by decide)

/-- One question at the smaller world, two at the larger one. -/
def Question : World → Type
  | false => Unit
  | true => Bool

/-- Questions translate forward: the old question is the first new one. -/
def translate : {b c : World} → (b ⟶ c) → Question b → Question c
  | false, false, _ => id
  | false, true, _ => fun _ => false
  | true, false, f => absurd (leOfHom f) (by decide)
  | true, true, _ => id

/-- The query functor of the walking arrow. -/
def questions : World ⥤ Type where
  obj := Question
  map f := ↾(translate f)
  map_id b := by cases b <;> rfl
  map_comp {a b c} f g := by
    cases a <;> cases b <;> cases c
    all_goals first
      | rfl
      | exact absurd (leOfHom f) (by decide)

/-- Natural-number evidence at both worlds. -/
def countEvidence : Worldᵒᵖ ⥤ AddCommMonCat := (Functor.const _).obj (AddCommMonCat.of ℕ)

/-- Profiles for the question-adding arrow. -/
abbrev addQuestions := profileFunctor questions countEvidence

/-- The extraction of the one-count model: its single question reads the count. -/
def oneCountExtract : ℕ →+ (Question false → ℕ) where
  toFun n _ := n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The extraction of the two-count model: the old question reads the first
count, the new question the second. -/
def twoCountsExtract : ℕ × ℕ →+ (Question true → ℕ) where
  toFun n q := match q with
    | false => n.1
    | true => n.2
  map_zero' := by funext q; cases q <;> rfl
  map_add' _ _ := by funext q; cases q <;> rfl

/-- A one-count world model at `false`. -/
def oneCount : Over (addQuestions.obj (op false)) :=
  Over.mk (AddCommMonCat.ofHom oneCountExtract :
    AddCommMonCat.of ℕ ⟶ addQuestions.obj (op false))

/-- A two-count world model at `true`: the old count and a new count. -/
def twoCounts : Over (addQuestions.obj (op true)) :=
  Over.mk (AddCommMonCat.ofHom twoCountsExtract :
    AddCommMonCat.of (ℕ × ℕ) ⟶ addQuestions.obj (op true))

/-- Embed the old count as the first count, with nothing yet on the new question. -/
def embedOld : (AddCommMonCat.of ℕ) ⟶ AddCommMonCat.of (ℕ × ℕ) :=
  AddCommMonCat.ofHom (AddMonoidHom.inl ℕ ℕ)

/-- **Positive: an arrow that adds a question.** Embedding the old count is a
morphism over the arrow. -/
def addQuestionHom :
    Total.mk addQuestions false oneCount ⟶ Total.mk addQuestions true twoCounts :=
  homOver addQuestions up (X := oneCount) (Y := twoCounts) embedOld
    ((overArrow_iff questions countEvidence up oneCount twoCounts embedOld).2
      (fun _ _ => rfl))

/-! ### An arrow that changes the evidence monoid -/

/-- Total counts at the smaller world, positive and negative counts at the larger. -/
def CountEvidence : World → AddCommMonCat
  | false => AddCommMonCat.of ℕ
  | true => AddCommMonCat.of (ℕ × ℕ)

/-- The total of a pair of counts. -/
def total : ℕ × ℕ →+ ℕ := AddMonoidHom.coprod (AddMonoidHom.id ℕ) (AddMonoidHom.id ℕ)

@[simp] theorem total_apply (n : ℕ × ℕ) : total n = n.1 + n.2 := rfl

/-- Evidence is read back along the arrow by totalling. -/
def readBack : {b c : World} → (b ⟶ c) → (CountEvidence c ⟶ CountEvidence b)
  | false, false, _ => 𝟙 _
  | false, true, _ => AddCommMonCat.ofHom total
  | true, false, f => absurd (leOfHom f) (by decide)
  | true, true, _ => 𝟙 _

/-- The evidence functor that refines totals into signed counts. -/
def refinedEvidence : Worldᵒᵖ ⥤ AddCommMonCat where
  obj b := CountEvidence b.unop
  map f := readBack f.unop
  map_id b := by
    cases b with
    | op b => cases b <;> rfl
  map_comp {a b c} f g := by
    cases a with
    | op a =>
    cases b with
    | op b =>
    cases c with
    | op c =>
    cases a <;> cases b <;> cases c
    all_goals first
      | rfl
      | exact absurd (leOfHom f.unop) (by decide)
      | exact absurd (leOfHom g.unop) (by decide)

/-- One question at both worlds. -/
def oneQuestion : World ⥤ Type := (Functor.const _).obj Unit

/-- Profiles for the evidence-refining arrow. -/
abbrev refineEvidence := profileFunctor oneQuestion refinedEvidence

/-- Extraction of signed counts at the larger world. -/
def signedExtract : ℕ × ℕ →+ (Unit → ℕ × ℕ) where
  toFun n _ := n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Extraction of totals at the smaller world, from the same signed state. -/
def totalExtract : ℕ × ℕ →+ (Unit → ℕ) where
  toFun n _ := total n
  map_zero' := rfl
  map_add' n m := by funext; simp only [map_add]; rfl

/-- The signed-count world model at the larger world. -/
def signedModel : Over (refineEvidence.obj (op true)) :=
  Over.mk (AddCommMonCat.ofHom signedExtract :
    AddCommMonCat.of (ℕ × ℕ) ⟶ refineEvidence.obj (op true))

/-- The total-count world model at the smaller world. -/
def totalModel : Over (refineEvidence.obj (op false)) :=
  Over.mk (AddCommMonCat.ofHom totalExtract :
    AddCommMonCat.of (ℕ × ℕ) ⟶ refineEvidence.obj (op false))

/-- **Positive: an arrow that changes the evidence monoid.** The identity of the
signed state is a morphism over the arrow: the larger world's signed answer,
totalled, is the smaller world's answer. -/
def refineEvidenceHom :
    Total.mk refineEvidence false totalModel ⟶ Total.mk refineEvidence true signedModel :=
  homOver refineEvidence up (X := totalModel) (Y := signedModel) (𝟙 _)
    ((overArrow_iff oneQuestion refinedEvidence up totalModel signedModel (𝟙 _)).2
      (fun _ _ => rfl))

/-- Extraction of positive counts only, at the smaller world. -/
def positiveExtract : ℕ →+ (Unit → ℕ) where
  toFun n _ := n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A positive-count world model at the smaller world. -/
def positiveModel : Over (refineEvidence.obj (op false)) :=
  Over.mk (AddCommMonCat.ofHom positiveExtract :
    AddCommMonCat.of ℕ ⟶ refineEvidence.obj (op false))

/-- The diagonal: a count `n` becomes `n` positive and `n` negative counts. -/
def diagonal : ℕ →+ ℕ × ℕ := AddMonoidHom.prod (AddMonoidHom.id ℕ) (AddMonoidHom.id ℕ)

/-- The diagonal keeps every old answer under the reading "first coordinate". -/
theorem diagonal_keeps_answers_under_first_reading (n : ℕ) :
    (signedExtract (diagonal n) ()).1 = positiveExtract n () := rfl

/-- **Negative.** The same diagonal fails the restriction equation, because the
doctrine reads evidence back by totalling: one positive count becomes two. -/
theorem diagonal_not_over_arrow :
    ¬ ((AddCommMonCat.ofHom diagonal : positiveModel.left ⟶ signedModel.left) ≫
        signedModel.hom ≫ refineEvidence.map up.op = positiveModel.hom) := by
  intro h
  have one := (overArrow_iff oneQuestion refinedEvidence up positiveModel signedModel
    (AddCommMonCat.ofHom diagonal)).1 h (1 : ℕ) ()
  have two : (1 : ℕ) + 1 = 1 := one
  exact absurd two (by decide)

/-- Positive control for the same pair of models: the inclusion as positive
counts is a morphism over the arrow. -/
def positiveHom :
    Total.mk refineEvidence false positiveModel ⟶ Total.mk refineEvidence true signedModel :=
  homOver refineEvidence up (X := positiveModel) (Y := signedModel)
    (AddCommMonCat.ofHom (AddMonoidHom.inl ℕ ℕ))
    ((overArrow_iff oneQuestion refinedEvidence up positiveModel signedModel _).2
      (fun W _ => by
        show total (W, 0) = W
        exact add_zero (W : ℕ)))

end WalkingArrow

end Mettapedia.Logic.WorldModel.Indexed
