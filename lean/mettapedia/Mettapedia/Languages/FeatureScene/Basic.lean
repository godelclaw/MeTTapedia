import Mathlib.Data.List.Basic

/-!
# A finite feature-scene calculus

A quantifier-free, many-sorted equality/conjunction example. Objects are
extensional shape/colour pairs, not physical identities; scenes are ordered
object pairs. Names are typed variables interpreted by a valuation. This is
an independently specified toy calculus, not a MeTTa dialect or all of FOL.
-/

namespace Mettapedia.Languages.FeatureScene

inductive Shape where
  | circle | square
  deriving DecidableEq, Repr

inductive Colour where
  | black | white
  deriving DecidableEq, Repr

inductive Ty where
  | shape | colour | object | scene
  deriving DecidableEq, Repr

abbrev Object := Shape × Colour

def Meaning : Ty → Type
  | .shape => Shape
  | .colour => Colour
  | .object => Object
  | .scene => Object × Object

inductive Projection : Ty → Ty → Type where
  | shape : Projection .object .shape
  | colour : Projection .object .colour
  | left : Projection .scene .object
  | right : Projection .scene .object

def Projection.run : Projection a b → Meaning a → Meaning b
  | .shape, value => value.1
  | .colour, value => value.2
  | .left, value => value.1
  | .right, value => value.2

inductive Expr : Ty → Type where
  | var (sort : Ty) (name : Nat) : Expr sort
  | circle : Expr .shape
  | square : Expr .shape
  | black : Expr .colour
  | white : Expr .colour
  | object : Expr .shape → Expr .colour → Expr .object
  | pair : Expr .object → Expr .object → Expr .scene
  | project : Projection a b → Expr a → Expr b

abbrev Valuation := (sort : Ty) → Nat → Meaning sort

def Expr.eval (env : Valuation) : Expr sort → Meaning sort
  | .var sort name => env sort name
  | .circle => .circle
  | .square => .square
  | .black => .black
  | .white => .white
  | .object shape colour => (shape.eval env, colour.eval env)
  | .pair left right => (left.eval env, right.eval env)
  | .project projection value => projection.run (value.eval env)

def Expr.rename (names : (sort : Ty) → Nat → Nat) : Expr sort → Expr sort
  | .var sort name => .var sort (names sort name)
  | .circle => .circle
  | .square => .square
  | .black => .black
  | .white => .white
  | .object shape colour => .object (shape.rename names) (colour.rename names)
  | .pair left right => .pair (left.rename names) (right.rename names)
  | .project projection value => .project projection (value.rename names)

theorem eval_rename (env : Valuation) (names : (sort : Ty) → Nat → Nat)
    (term : Expr sort) :
    (term.rename names).eval env = term.eval (fun sort name => env sort (names sort name)) := by
  induction term <;> simp_all [Expr.rename, Expr.eval] <;> rfl

/-- Directed computation is kept distinct from symmetric equality. -/
inductive Step : Expr sort → Expr sort → Prop where
  | shape : Step (.project .shape (.object s c)) s
  | colour : Step (.project .colour (.object s c)) c
  | left : Step (.project .left (.pair l r)) l
  | right : Step (.project .right (.pair l r)) r
  | objectShape : Step s t → Step (.object s c) (.object t c)
  | objectColour : Step c d → Step (.object s c) (.object s d)
  | pairLeft : Step l k → Step (.pair l r) (.pair k r)
  | pairRight : Step r k → Step (.pair l r) (.pair l k)
  | project : Step x y → Step (.project p x) (.project p y)

theorem step_sound (env : Valuation) {source target : Expr sort}
    (step : Step source target) : source.eval env = target.eval env := by
  induction step <;> simp_all [Expr.eval, Projection.run] <;> rfl

def Expr.size : Expr sort → Nat
  | .var _ _ | .circle | .square | .black | .white => 1
  | .object shape colour => 1 + shape.size + colour.size
  | .pair left right => 1 + left.size + right.size
  | .project _ value => 1 + value.size

theorem step_decreases {source target : Expr sort} (step : Step source target) :
    target.size < source.size := by
  induction step <;> simp_all [Expr.size] <;> omega

theorem reduction_wellFounded (sort : Ty) :
    WellFounded (fun target source : Expr sort => Step source target) := by
  exact Subrelation.wf (fun step => step_decreases step) (measure Expr.size).wf

inductive Formula where
  | equal : Expr sort → Expr sort → Formula
  | conj : Formula → Formula → Formula

def Holds (env : Valuation) : Formula → Prop
  | .equal left right => left.eval env = right.eval env
  | .conj left right => Holds env left ∧ Holds env right

inductive Derives (context : List Formula) : Formula → Prop where
  | hypothesis : proposition ∈ context → Derives context proposition
  | refl (term : Expr sort) : Derives context (.equal term term)
  | symm : Derives context (.equal a b) → Derives context (.equal b a)
  | trans : Derives context (.equal a b) → Derives context (.equal b c) →
      Derives context (.equal a c)
  | conjunction : Derives context a → Derives context b → Derives context (.conj a b)
  | first : Derives context (.conj a b) → Derives context a
  | second : Derives context (.conj a b) → Derives context b
  | projection (p : Projection a b) : Derives context (.equal x y) →
      Derives context (.equal (.project p x) (.project p y))
  | objectExt : Derives context (.equal (.project .shape x) (.project .shape y)) →
      Derives context (.equal (.project .colour x) (.project .colour y)) →
      Derives context (.equal x y)
  | sceneExt : Derives context (.equal (.project .left x) (.project .left y)) →
      Derives context (.equal (.project .right x) (.project .right y)) →
      Derives context (.equal x y)
  | computation : Step x y → Derives context (.equal x y)

theorem derivation_sound {context : List Formula} {proposition : Formula}
    (proof : Derives context proposition) (env : Valuation)
    (assumptions : ∀ p ∈ context, Holds env p) : Holds env proposition := by
  induction proof with
  | hypothesis member => exact assumptions _ member
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | conjunction _ _ first second => exact ⟨first, second⟩
  | first _ ih => exact ih.1
  | second _ ih => exact ih.2
  | projection p _ ih => exact congrArg p.run ih
  | objectExt _ _ shape colour => exact Prod.ext shape colour
  | sceneExt _ _ left right => exact Prod.ext left right
  | computation step => exact step_sound env step

/-- The substitution of equal colour observations in stage III. -/
theorem same_colour_constraints (env : Valuation) (a b : Expr .colour) :
    Holds env (.conj (.equal a .white) (.equal b .white)) ↔
      Holds env (.conj (.equal a .white) (.equal b a)) := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨ha, hb.trans ha.symm⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, hb.trans ha⟩

def blackCircle : Expr .object := .object .circle .black
def whiteCircle : Expr .object := .object .circle .white
def whiteSquare : Expr .object := .object .square .white
def blackSquare : Expr .object := .object .square .black

def copyAttributes (shapeSource colourSource : Expr .object) : Expr .object :=
  .object (.project .shape shapeSource) (.project .colour colourSource)

theorem copy_attributes (env : Valuation) (shapeSource colourSource : Expr .object) :
    (copyAttributes shapeSource colourSource).eval env =
      ((shapeSource.eval env).1, (colourSource.eval env).2) := by
  rfl

theorem eighth_scene (env : Valuation) :
    (Expr.pair blackCircle (copyAttributes whiteSquare blackCircle)).eval env =
      (Expr.pair blackCircle blackSquare).eval env := by
  rfl

def defaultValuation : Valuation
  | .shape, _ => .circle
  | .colour, _ => .black
  | .object, _ => (.circle, .black)
  | .scene, _ => ((.circle, .black), (.circle, .black))

theorem black_is_not_white : ¬ Derives [] (.equal .black .white) := by
  intro proof
  have impossible := derivation_sound proof defaultValuation (by simp)
  cases impossible

theorem colour_alone_does_not_identify_object :
    Holds defaultValuation (.equal (.project .colour whiteCircle) (.project .colour whiteSquare)) ∧
      ¬ Holds defaultValuation (.equal whiteCircle whiteSquare) := by
  change Colour.white = Colour.white ∧
    ¬ (Shape.circle, Colour.white) = (Shape.square, Colour.white)
  decide

theorem reduction_is_not_symmetric :
    Step (.project .shape blackCircle) .circle ∧
      ¬ Step Expr.circle (.project .shape blackCircle) := by
  constructor
  · exact Step.shape
  · intro reverse
    cases reverse

end Mettapedia.Languages.FeatureScene
