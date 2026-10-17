import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.LiteralConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Synthesis
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.RigidHeads
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower

/-!
# A string literal and a user's constant over the tower

A theory over the cumulative tower declares the numbers with a successor, the
host sort `String` and a user's sort `Color` with a constant `red`; the
literal `banana` is declared at `String`, as the host says.  Swapping `String`
with `Color` and `banana` with `red` is a symmetry of the package
(`swap_symmetry`), so every judgment about the literal is derivable exactly
when the same judgment about the user's constant is
(`literal_iff_user_constant`; at the successor, `succ_literal_iff_succ_user_constant`).
Controls: the literal and the user's constant are typed at their sorts
(`banana_typed`, `red_typed`), and in the theory without the literal's
declaration the literal has no type (`banana_untyped_in_theory`).

Refutations.  No constant of the package computes, so the normalization model
applies with every constant rigid (`facts`) and the conversion algorithm is
complete (`complete`), and the kernel's generic refutations decide mismatches
of the literal: a literal is not a type (`banana_not_type`, by
`Synth.not_typed`), not a function (`banana_not_applicable`, by
`Synth.not_applicable`), and not a number: `succ banana` has no type
(`succ_banana_untyped`), since the literal's sort and `num` are distinct rigid
constants (`not_equal_of_distinct_rigid`).  The same refutations of the user's
constant follow from the literal's by the symmetry alone (`red_not_type`,
`red_not_applicable`, `succ_red_untyped`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

namespace TowerLiterals

open Mettapedia.TypeTheory.UniverseLevel

/-- The first universe of the tower. -/
abbrev universe0 : Tm Tower.Head 0 := .head (.sort Tower.zero)

def num : DeclName := `num
def succ : DeclName := `succ
/-- The host's sort of strings. -/
def String : DeclName := `String
/-- A user's sort. -/
def Color : DeclName := `Color
/-- A user's constant of the user's sort. -/
def red : DeclName := `red
/-- The literal `"banana"`, named apart from every symbol. -/
def banana : DeclName := .str (.str .anonymous "literal") "\"banana\""

/-- The theory: numbers with a successor, the host sort `String`, and a
user's sort `Color` with a constant `red`. -/
def theory : Rules Tower.Head :=
  ((((Tower.rules.addConstant num universe0).addConstant succ (.pi (.const num) (.const num))
    ).addConstant String universe0).addConstant Color universe0).addConstant red (.const Color)

/-- The theory with the literal `banana` declared at its host sort. -/
def withLiteral : Rules Tower.Head := theory.addConstant banana (.const String)

/-- Swap the host sort with the user's sort, and the literal with the user's
constant. -/
def swap (c : DeclName) : DeclName :=
  if c = String then Color else if c = Color then String
  else if c = banana then red else if c = red then banana else c

theorem swap_involution (c : DeclName) : swap (swap c) = c := by
  unfold swap
  by_cases h1 : c = String
  · subst h1; decide
  · by_cases h2 : c = Color
    · subst h2; decide
    · by_cases h3 : c = banana
      · subst h3; decide
      · by_cases h4 : c = red
        · subst h4; decide
        · simp only [h1, h2, h3, h4, if_false]

/-- Declared types, read through the swap: the swap sends each declaration of
the package to a declaration of the package. -/
theorem constantType_swap (name : DeclName) :
    withLiteral.constantType (swap name) =
      (withLiteral.constantType name).map (Tm.mapConst swap) := by
  by_cases h1 : name = String
  · subst h1; rfl
  by_cases h2 : name = Color
  · subst h2; rfl
  by_cases h3 : name = banana
  · subst h3; rfl
  by_cases h4 : name = red
  · subst h4; rfl
  have fixed : swap name = name := by simp only [swap, h1, h2, h3, h4, if_false]
  rw [fixed]
  by_cases h5 : name = succ
  · subst h5; rfl
  by_cases h6 : name = num
  · subst h6; rfl
  have none : withLiteral.constantType name = none := by
    simp only [withLiteral, theory, Rules.addConstant, beq_false_of_ne h1,
      beq_false_of_ne h2, beq_false_of_ne h3, beq_false_of_ne h4, beq_false_of_ne h5,
      beq_false_of_ne h6, cond_false]
    rfl
  rw [none]
  rfl

/-- **The swap is a symmetry of the package with the literal.** -/
theorem swap_symmetry : RulesRenaming withLiteral withLiteral swap where
  headTyping h := h
  isUniverse h := h
  join h := h
  cumulative h := h
  headEq h := h
  constantType := by
    intro name type declared
    rw [constantType_swap, declared]
    rfl
  computation step := False.elim step

/-- The literal has its host sort as a type. -/
theorem banana_typed : Typed withLiteral .nil (.const banana) (.const String) := by
  have declared : theory.constantType String = some universe0 := rfl
  have formed : Typed theory .nil universe0 (.head (.sort (.succ Tower.zero))) :=
    .headType (.sort Tower.zero)
  have sortTyped := Derivable.const (Γ := .nil) declared formed (.sort _)
  rw [Tm.liftClosed_at_zero] at sortTyped
  exact literal_typed (R := theory) rfl sortTyped (.sort _) .nil

/-- The user's constant has the user's sort as a type. -/
theorem red_typed : Typed withLiteral .nil (.const red) (.const Color) := by
  have declared : withLiteral.constantType red = some (.const Color) := rfl
  have colorDeclared : withLiteral.constantType Color = some universe0 := rfl
  have formed : Typed withLiteral .nil universe0 (.head (.sort (.succ Tower.zero))) :=
    .headType (.sort Tower.zero)
  have colorTyped := Derivable.const (Γ := .nil) colorDeclared formed (.sort _)
  rw [Tm.liftClosed_at_zero] at colorTyped
  have typedConst := Derivable.const (Γ := .nil) declared colorTyped (.sort _)
  rw [Tm.liftClosed_at_zero] at typedConst
  exact typedConst

/-- Without its declaration the literal has no type: in the theory alone, where
the elaborator has given it none, there is nothing to establish or refute. -/
theorem banana_untyped_in_theory {n : Nat} {Γ : Ctx Tower.Head n} {T : Tm Tower.Head n} :
    ¬ Typed theory Γ (.const banana) T :=
  undeclared_untyped rfl

/-- **Every judgment about the literal is derivable exactly when its image
about the user's constant is.** -/
theorem literal_iff_user_constant (st : Statement Tower.Head) :
    Derivable withLiteral st ↔ Derivable withLiteral (st.mapConst swap) :=
  literal_verdict_sort_blind swap_symmetry swap_involution st

/-- The successor applied to the literal is typed at a type exactly when the
successor applied to the user's constant is, at every context and type that
mention neither sort nor either constant.  So a refutation of the one is a
refutation of the other. -/
theorem succ_literal_iff_succ_user_constant {n : Nat} {Γ : Ctx Tower.Head n}
    {T : Tm Tower.Head n} (contextFixed : Γ.mapConst swap = Γ)
    (typeFixed : T.mapConst swap = T) :
    Typed withLiteral Γ (.app (.const succ) (.const banana)) T ↔
      Typed withLiteral Γ (.app (.const succ) (.const red)) T := by
  have blind := literal_iff_user_constant (.typing Γ (.app (.const succ) (.const banana)) T)
  have image : (Tm.app (.const succ) (.const banana) : Tm Tower.Head n).mapConst swap =
      .app (.const succ) (.const red) := rfl
  simp only [Statement.mapConst, contextFixed, typeFixed, image] at blind
  exact blind

/-- At the numbers in particular. -/
theorem succ_literal_at_num_iff :
    Typed withLiteral .nil (.app (.const succ) (.const banana)) (.const num) ↔
      Typed withLiteral .nil (.app (.const succ) (.const red)) (.const num) :=
  succ_literal_iff_succ_user_constant rfl rfl

/-! ## Refutations by the kernel's generic rules -/

open Normalization

/-- No constant of the package computes: every one is rigid. -/
def roles : Roles Tower.Head := fun _ => .rigid

theorem shape : RootShape withLiteral roles where
  spine := fun step => False.elim step
  deterministic := fun step => False.elim step

/-- The tower's levels: the package adds constants and no universe. -/
def levels (valuation : Nat → Nat) : LevelModel withLiteral Nat :=
  { TowerModel.levels (L := Nat) valuation with }

/-- The normalization setting of the package under a valuation. -/
def setting (valuation : Nat → Nat) : Setting Tower.Head Nat where
  R := withLiteral
  roles := roles
  E := declarative withLiteral
  levels := levels valuation
  shape := shape
  constructors := .of_no_inductive fun _ _ role => by cases role

theorem laws (valuation : Nat → Nat) :
    (setting valuation).E.Laws (setting valuation).R (setting valuation).roles :=
  declarative_laws roles (levels valuation)

theorem constants (valuation : Nat → Nat) : SemanticConstants (setting valuation) :=
  SemanticConstants.of_rigid (laws valuation) fun _ => rfl

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which every declared constant is rigid and semantic. -/
theorem facts : FormFacts withLiteral roles :=
  .ofSemantic (S := setting fun _ => 0) (laws _) (constants _)

theorem algebra : CumulativeAlgebra withLiteral :=
  { TowerModel.algebra (L := Nat) with }

theorem headsTyped {h u u' : Tower.Head} (first : withLiteral.headTyping h u)
    (second : withLiteral.headTyping h u') : u = u' := by
  change LevelTower.HeadTyping h u at first
  change LevelTower.HeadTyping h u' at second
  cases first <;> cases second <;> rfl

/-- The host sort is a type of the first universe. -/
theorem string_typed :
    Typed withLiteral .nil (.const String) (.head (.sort Tower.zero)) := by
  have declared : withLiteral.constantType String = some universe0 := rfl
  have formed : Typed withLiteral .nil universe0 (.head (.sort (.succ Tower.zero))) :=
    .headType (.sort Tower.zero)
  have typedConst := Derivable.const (Γ := .nil) declared formed (.sort _)
  rw [Tm.liftClosed_at_zero] at typedConst
  exact typedConst

/-- The kernel synthesizes the literal's sort, by the rule for a declared
constant. -/
theorem banana_synth : Synth withLiteral roles .nil (.const banana) (.const String) := by
  have declared : withLiteral.constantType banana = some (.const String) := rfl
  exact KernelTyping.const declared string_typed (.sort _)

/-- The literal's sort is rigid: a neutral type. -/
theorem string_neutral : Neutral roles (.const String : Tm Tower.Head 0) :=
  Neutral.rigid [] rfl

/-- **A literal is not a type**: no universe types `banana`, by the generic
refutation of a term whose synthesized type is not below the expected one. -/
theorem banana_not_type (u : Tower.Head) :
    ¬ Typed withLiteral .nil (.const banana) (.head u) := by
  have notBelow : ¬ Below withLiteral .nil (.const String) (.head u) := by
    intro below
    have equal := RigidShape.rigid (S := setting fun _ => 0) facts
      (.neutral string_neutral) .nil below
    exact (TypeEq.neutral_form facts equal .nil string_neutral (.inl ⟨u, rfl⟩)).not_former.1
      u rfl
  exact Synth.not_typed (S := setting fun _ => 0) facts algebra headsTyped banana_synth .nil
    notBelow

/-- **A literal is not a function**: `banana` applied to anything has no type,
by the generic refutation of an application whose function's synthesized type
is not a dependent function type. -/
theorem banana_not_applicable (a X : Tm Tower.Head 0) :
    ¬ Typed withLiteral .nil (.app (.const banana) a) X :=
  Synth.not_applicable (S := setting fun _ => 0) facts algebra headsTyped banana_synth .nil
    (RedTy.refl ⟨_, .sort _, string_typed⟩)
    (.inr (.inr (.inr (.inr (.inl string_neutral))))) (fun _ _ same => by cases same)

/-- The same refutation of the user's constant, read off the literal's through
the symmetry: the verdict did not depend on the literal or on its sort. -/
theorem red_not_type (u : Tower.Head) :
    ¬ Typed withLiteral .nil (.const red) (.head u) := fun typed =>
  banana_not_type u ((literal_iff_user_constant (.typing .nil (.const banana) (.head u))).mpr typed)

theorem red_not_applicable (a X : Tm Tower.Head 0)
    (aFixed : a.mapConst swap = a) (XFixed : X.mapConst swap = X) :
    ¬ Typed withLiteral .nil (.app (.const red) a) X := by
  intro typed
  have image : (Statement.typing (.nil : Ctx Tower.Head 0) (.app (.const banana) a) X).mapConst
      swap = .typing .nil (.app (.const red) a) X := by
    simp only [Statement.mapConst, Ctx.mapConst, Tm.mapConst, aFixed, XFixed]
    rfl
  have back := (literal_iff_user_constant (.typing .nil (.app (.const banana) a) X)).mpr
  rw [image] at back
  exact banana_not_applicable a X (back typed)

/-! ## The literal at the numbers -/

theorem heads : HeadPreserving withLiteral := by
  intro n Γ h h' A same typing
  obtain ⟨u, headTyping, le⟩ := Typed.generation typing
  change LevelTower.HeadTyping h u at headTyping
  change LevelTower.HeadEq h h' at same
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : withLiteral.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show UniverseLevel.LevelOrder.succ (LevelExpr.eval ν r) ≤
              UniverseLevel.LevelOrder.succ (LevelExpr.eval ν l)
            exact UniverseLevel.LevelOrder.succ_le_succ (le_of_eq (same ν).symm)
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem roots : RootPreserving withLiteral := by
  intro n Γ l r A _ step
  exact False.elim step

/-- The constants are semantic for the algorithmic equality too: they are rigid. -/
theorem algorithmicConstants :
    SemanticConstants (algorithmicSetting (setting fun _ => 0)) :=
  SemanticConstants.of_rigid
    (algorithmicSetting_laws (S := setting fun _ => 0) (laws _) (constants _) roots heads
      algebra)
    fun _ => rfl

/-- **The conversion algorithm is complete for the package**, by the
normalization model over the algorithmic equality. -/
theorem complete : AlgorithmicComplete withLiteral roles :=
  AlgorithmicComplete.ofSemantic (S := setting fun _ => 0) (laws _) (constants _) roots heads
    algebra algorithmicConstants

theorem num_typed {n : Nat} (Γ : Ctx Tower.Head n) :
    Typed withLiteral Γ (.const num) (.head (.sort Tower.zero)) := by
  have declared : withLiteral.constantType num = some universe0 := rfl
  have formed : Typed withLiteral .nil universe0 (.head (.sort (.succ Tower.zero))) :=
    .headType (.sort Tower.zero)
  exact Derivable.const (Γ := Γ) declared formed (.sort _)

theorem succ_type_typed :
    Typed withLiteral .nil (.pi (.const num) (.const num))
      (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (num_typed .nil) (.sort _) (num_typed _) (.sort _) (.sorts _ _)

/-- The kernel synthesizes the successor's declared type. -/
theorem succ_synth :
    Synth withLiteral roles .nil (.const succ) (.pi (.const num) (.const num)) := by
  have declared : withLiteral.constantType succ = some (.pi (.const num) (.const num)) := rfl
  exact KernelTyping.const declared succ_type_typed (.sort _)

/-- **The literal is not a number**: `succ banana` has no type.  The successor's
domain is `num`; the literal's synthesized type is its sort `String`, a rigid
type, which is below `num` only if equal to it; and two distinct rigid
constants are equal at no type.  Each step is a generic rule: no step reads
that `banana` is a literal or that `String` is the host's sort. -/
theorem succ_banana_untyped (X : Tm Tower.Head 0) :
    ¬ Typed withLiteral .nil (.app (.const succ) (.const banana)) X := by
  intro typed
  obtain ⟨A, B, tSucc, tBanana, _⟩ := Typed.generation typed
  have principalSucc :=
    (Synth.principal (S := setting fun _ => 0) facts algebra @headsTyped succ_synth .nil).2 tSucc
  have typePi := Typed.isType (S := setting fun _ => 0) tSucc .nil
  have below := TypeLe.toBelow principalSucc typePi
  obtain ⟨A₀, B₀, eX, eA, _⟩ :=
    Below.pi_inv (S := setting fun _ => 0) facts below .nil (IsType.refl typePi)
  obtain ⟨eNum, _⟩ := TypeEq.pi_injective facts eX .nil
  have eNumA : TypeEq withLiteral .nil (.const num) A :=
    TypeEq.trans (levels fun _ => 0) eNum eA
  have tBananaNum := Typed.convType tBanana eNumA.symm
  have principalBanana :=
    (Synth.principal (S := setting fun _ => 0) facts algebra @headsTyped banana_synth .nil).2
      tBananaNum
  have belowNum := TypeLe.toBelow principalBanana ⟨_, .sort _, num_typed .nil⟩
  obtain ⟨u, _, equal⟩ := RigidShape.rigid (S := setting fun _ => 0) facts
    (.neutral string_neutral) .nil belowNum
  exact not_equal_of_distinct_rigid (S := setting fun _ => 0) complete .nil
    (by decide : String ≠ num) rfl rfl equal

/-- The same refutation of the user's constant, read off the literal's through
the symmetry. -/
theorem succ_red_untyped (X : Tm Tower.Head 0) (XFixed : X.mapConst swap = X) :
    ¬ Typed withLiteral .nil (.app (.const succ) (.const red)) X := by
  intro typed
  exact succ_banana_untyped X
    ((succ_literal_iff_succ_user_constant (Γ := .nil) rfl XFixed).mpr typed)

end TowerLiterals

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
