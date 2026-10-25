import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.StructuralModal.Formula
import Mettapedia.OSLF.Formula

/-!
# Embedding the syntactic formula languages

Two formula languages read terms as written, over a step relation: the structural-modal formulas and
the original OSLF formulas. Both embed into the generated formulas, interpreted in the syntactic
structure of the step relation (`syntactic`). There the steps are the given ones, a term is built by its
head constructor from its arguments, the empty collection is the empty collection, and a collection
splits positionally. These are the reference structure's readings, with equality in place of
equivalence.

- **Structural-modal formulas** embed exactly (`sat_ofStructuralModal`). Their box is the past box.
- **OSLF formulas** have implication and least fixed points. The embedding tracks polarity: an
  implication's premise is translated at the opposite polarity, and a least fixed point at negative
  polarity becomes a greatest one. Atoms become pairs of free variables, one holding where the atom
  holds and one where it fails, above the scope variables. The embedding is exact for formulas whose
  scope variables occur at the polarity of their binders (`sat_ofOSLF`), the usual positivity of
  fixed-point bodies. Without that condition the two readings differ, since the generated logic has
  no negated variables.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The syntactic structure of a step relation**: terms as written, with the given steps, all labelled
`any`. Shapes are read as in the reference structure, with equality in place of equivalence. -/
def syntactic (step : Pattern → Pattern → Prop) : NativeStructure Pattern where
  step source label target := label = .any ∧ step source target
  built element constructor parts := element = .apply constructor parts
  split element kind first second := ∃ left right,
    element = .collection kind (left ++ right) none ∧ first = .collection kind left none ∧
      second = .collection kind right none
  empty element kind := element = .collection kind [] none
  single element kind member := element = .collection kind [member] none
  body element inner := ∃ name, element = .lambda name inner
  multiBody element arity inner := ∃ names, element = .multiLambda arity names inner
  bound element index := element = .bvar index
  typed _ _ := False
  named element term := element = term
  same first second := first = second
  apply inner value := Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar value inner

/-! ## Structural-modal formulas -/

section StructuralModal

open Mettapedia.OSLF.StructuralModal (satisfiesOver satisfiesAllOver)
open Mettapedia.OSLF.Framework.DerivedModalities (ReductionSpan derivedDiamond derivedBox di ui pb)

universe e

mutual
/-- **A structural-modal formula as a generated formula.** -/
def ofStructuralModal : Mettapedia.OSLF.StructuralModal.Formula → Formula 0
  | .top => .top
  | .bot => .bot
  | .and left right => .and (ofStructuralModal left) (ofStructuralModal right)
  | .or left right => .or (ofStructuralModal left) (ofStructuralModal right)
  | .headed constructor arguments => .built constructor (ofStructuralModalList arguments)
  | .diamond inner => .possibly .any (ofStructuralModal inner)
  | .box inner => .alwaysBefore .any (ofStructuralModal inner)
  | .emptyColl kind => .empty kind
  | .cut kind left right => .split kind (ofStructuralModal left) (ofStructuralModal right)

/-- The arguments of a structural-modal constructor former. -/
def ofStructuralModalList : List Mettapedia.OSLF.StructuralModal.Formula → Formulas 0
  | [] => .nil
  | argument :: arguments => .cons (ofStructuralModal argument) (ofStructuralModalList arguments)
end

/-- The steps of a span. -/
def spanStep (span : ReductionSpan.{0, e} Pattern) (source target : Pattern) : Prop :=
  ∃ edge, span.source edge = source ∧ span.target edge = target

mutual
/-- **Structural-modal formulas embed exactly.** -/
theorem sat_ofStructuralModal (span : ReductionSpan.{0, e} Pattern) :
    ∀ (formula : Mettapedia.OSLF.StructuralModal.Formula) (pattern : Pattern),
      (syntactic (spanStep span)).sat Env.closed (ofStructuralModal formula) pattern ↔
        satisfiesOver span formula pattern
  | .top, _ => Iff.rfl
  | .bot, _ => Iff.rfl
  | .and left right, pattern =>
    and_congr (sat_ofStructuralModal span left pattern) (sat_ofStructuralModal span right pattern)
  | .or left right, pattern =>
    or_congr (sat_ofStructuralModal span left pattern) (sat_ofStructuralModal span right pattern)
  | .headed _ arguments, _ =>
    exists_congr fun parts => and_congr Iff.rfl (satAll_ofStructuralModalList span arguments parts)
  | .diamond inner, pattern => by
    change (∃ next, (StepLabel.any = .any ∧ spanStep span pattern next) ∧
      (syntactic (spanStep span)).sat Env.closed (ofStructuralModal inner) next) ↔
        derivedDiamond span (satisfiesOver span inner) pattern
    simp only [derivedDiamond, di, pb, Function.comp, spanStep, true_and]
    constructor
    · rintro ⟨next, ⟨edge, starts, ends⟩, holds⟩
      exact ⟨edge, starts, ends ▸ (sat_ofStructuralModal span inner next).mp holds⟩
    · rintro ⟨edge, starts, holds⟩
      exact ⟨span.target edge, ⟨edge, starts, rfl⟩, (sat_ofStructuralModal span inner _).mpr holds⟩
  | .box inner, pattern => by
    change (∀ previous, (StepLabel.any = .any ∧ spanStep span previous pattern) →
      (syntactic (spanStep span)).sat Env.closed (ofStructuralModal inner) previous) ↔
        derivedBox span (satisfiesOver span inner) pattern
    simp only [derivedBox, ui, pb, Function.comp, spanStep, true_and]
    constructor
    · intro holds edge ends
      exact (sat_ofStructuralModal span inner _).mp (holds _ ⟨edge, rfl, ends⟩)
    · rintro holds previous ⟨edge, starts, ends⟩
      exact starts ▸ (sat_ofStructuralModal span inner _).mpr (holds edge ends)
  | .emptyColl _, _ => Iff.rfl
  | .cut _ left right, _ => by
    constructor
    · rintro ⟨first, second, ⟨leftElements, rightElements, whole, rfl, rfl⟩, inLeft, inRight⟩
      exact ⟨leftElements, rightElements, whole, (sat_ofStructuralModal span left _).mp inLeft,
        (sat_ofStructuralModal span right _).mp inRight⟩
    · rintro ⟨leftElements, rightElements, whole, inLeft, inRight⟩
      exact ⟨_, _, ⟨leftElements, rightElements, whole, rfl, rfl⟩, (sat_ofStructuralModal span left _).mpr inLeft,
        (sat_ofStructuralModal span right _).mpr inRight⟩

/-- Argument lists embed exactly. -/
theorem satAll_ofStructuralModalList (span : ReductionSpan.{0, e} Pattern) :
    ∀ (arguments : List Mettapedia.OSLF.StructuralModal.Formula) (children : List Pattern),
      (syntactic (spanStep span)).satAll Env.closed (ofStructuralModalList arguments) children ↔
        satisfiesAllOver span arguments children
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | argument :: arguments, child :: children =>
    and_congr (sat_ofStructuralModal span argument child) (satAll_ofStructuralModalList span arguments children)
end

end StructuralModal

/-! ## OSLF formulas -/

section OSLF

open Mettapedia.OSLF.Formula (OSLFFormula AtomSem ScopeEnv semEnv fullFrame)

variable {m : ℕ} (positive negative : String → Fin m)

/-- The variable of an atom slot, above `depth` scope variables. -/
def atomSlot (depth : ℕ) (slot : Fin m) : Fin (m + depth) :=
  ⟨slot + depth, by omega⟩

/-- **An OSLF formula as a generated formula**, at a polarity: the formula itself at `true`, its negation
at `false`. -/
def ofOSLF : (depth : ℕ) → Bool → OSLFFormula → Formula (m + depth)
  | _, true, .top => .top
  | _, false, .top => .bot
  | _, true, .bot => .bot
  | _, false, .bot => .top
  | depth, true, .atom atom => .var (atomSlot depth (positive atom))
  | depth, false, .atom atom => .var (atomSlot depth (negative atom))
  | depth, true, .and left right => .and (ofOSLF depth true left) (ofOSLF depth true right)
  | depth, false, .and left right => .or (ofOSLF depth false left) (ofOSLF depth false right)
  | depth, true, .or left right => .or (ofOSLF depth true left) (ofOSLF depth true right)
  | depth, false, .or left right => .and (ofOSLF depth false left) (ofOSLF depth false right)
  | depth, true, .imp premise conclusion => .or (ofOSLF depth false premise) (ofOSLF depth true conclusion)
  | depth, false, .imp premise conclusion => .and (ofOSLF depth true premise) (ofOSLF depth false conclusion)
  | depth, true, .dia inner => .possibly .any (ofOSLF depth true inner)
  | depth, false, .dia inner => .necessarily .any (ofOSLF depth false inner)
  | depth, true, .box inner => .alwaysBefore .any (ofOSLF depth true inner)
  | depth, false, .box inner => .sometimeBefore .any (ofOSLF depth false inner)
  | depth, _, .var index => if bounded : index < depth then .var ⟨index, by omega⟩ else .bot
  | depth, true, .mu body => .mu (ofOSLF (depth + 1) true body)
  | depth, false, .mu body => .nu (ofOSLF (depth + 1) false body)
  | _, true, .emptyColl kind => .empty kind
  | _, false, .emptyColl kind => .nonEmpty kind
  | depth, true, .cut kind left right => .split kind (ofOSLF depth true left) (ofOSLF depth true right)
  | depth, false, .cut kind left right => .everySplit kind (ofOSLF depth false left) (ofOSLF depth false right)
  | depth, true, .headed label inner => .built label (.cons (ofOSLF depth true inner) .nil)
  | depth, false, .headed label inner => .everyBuilt label (.cons (ofOSLF depth false inner) .nil)

/-- The polarity of a new innermost scope variable. -/
def pushSign (sign : Bool) (signs : ℕ → Bool) : ℕ → Bool
  | 0 => sign
  | index + 1 => signs index

/-- **Every scope variable occurs at the polarity of its binder.** `signs` gives the polarities of the
free ones; an implication's premise flips the polarity. -/
def consistent : (ℕ → Bool) → Bool → OSLFFormula → Bool
  | _, _, .top | _, _, .bot | _, _, .atom _ | _, _, .emptyColl _ => true
  | signs, polarity, .var index => signs index == polarity
  | signs, polarity, .and left right | signs, polarity, .or left right | signs, polarity, .cut _ left right =>
    consistent signs polarity left && consistent signs polarity right
  | signs, polarity, .imp premise conclusion =>
    consistent signs (!polarity) premise && consistent signs polarity conclusion
  | signs, polarity, .dia inner | signs, polarity, .box inner | signs, polarity, .headed _ inner =>
    consistent signs polarity inner
  | signs, polarity, .mu body => consistent (pushSign polarity signs) polarity body

/-- A proposition at a polarity: itself at `true`, its negation at `false`. -/
abbrev signed (polarity : Bool) (proposition : Prop) : Prop := cond polarity proposition (¬ proposition)

/-- **A generated environment that agrees with the atoms and the signed scope variables.** -/
structure Agrees (atoms : AtomSem) (scope : ScopeEnv) (signs : ℕ → Bool) (depth : ℕ)
    (env : Env Pattern (m + depth)) : Prop where
  positive_atom : ∀ atom term, term ∈ env (atomSlot depth (positive atom)) ↔ atoms atom term
  negative_atom : ∀ atom term, term ∈ env (atomSlot depth (negative atom)) ↔ ¬ atoms atom term
  scope_variable : ∀ (index : ℕ) (bounded : index < depth) (term : Pattern),
    term ∈ env ⟨index, by omega⟩ ↔ signed (signs index) (scope index term)

variable {positive negative}

theorem Agrees.extend {atoms : AtomSem} {scope : ScopeEnv} {signs : ℕ → Bool} {depth : ℕ}
    {env : Env Pattern (m + depth)} (agrees : Agrees positive negative atoms scope signs depth env)
    (sign : Bool) (candidate : Pattern → Prop) (set : Set Pattern)
    (same : ∀ term, term ∈ set ↔ signed sign (candidate term)) :
    Agrees positive negative atoms (ScopeEnv.push candidate scope) (pushSign sign signs) (depth + 1)
      (env.extend set) where
  positive_atom atom term := agrees.positive_atom atom term
  negative_atom atom term := agrees.negative_atom atom term
  scope_variable index bounded term := by
    cases index with
    | zero => exact same term
    | succ index => exact agrees.scope_variable index (by omega) term

theorem consistent_and {signs : ℕ → Bool} {polarity : Bool} {left right : OSLFFormula} :
    consistent signs polarity (.and left right) = true ↔
      consistent signs polarity left = true ∧ consistent signs polarity right = true := by
  simp [consistent]

/-- **OSLF formulas embed exactly**, at both polarities, when their scope variables occur at the
polarity of their binders. -/
theorem sat_ofOSLF (step : Pattern → Pattern → Prop) (atoms : AtomSem) :
    ∀ (formula : OSLFFormula) {depth : ℕ} {polarity : Bool} {scope : ScopeEnv} {signs : ℕ → Bool}
      {env : Env Pattern (m + depth)},
      OSLFFormula.closedAt depth formula = true → consistent signs polarity formula = true →
      Agrees positive negative atoms scope signs depth env → ∀ term,
        ((syntactic step).sat env (ofOSLF positive negative depth polarity formula) term ↔
          signed polarity (semEnv step fullFrame atoms scope formula term))
  | .top, _, polarity, _, _, _, _, _, _, _ => by cases polarity <;> simp [ofOSLF, NativeStructure.sat, semEnv]
  | .bot, _, polarity, _, _, _, _, _, _, _ => by cases polarity <;> simp [ofOSLF, NativeStructure.sat, semEnv]
  | .atom atom, _, polarity, _, _, _, _, _, agrees, term => by
    cases polarity
    · exact agrees.negative_atom atom term
    · exact agrees.positive_atom atom term
  | .and left right, _, polarity, _, _, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt, Bool.and_eq_true] at closed
    simp only [consistent, Bool.and_eq_true] at coherent
    have first := sat_ofOSLF step atoms left closed.1 coherent.1 agrees term
    have second := sat_ofOSLF step atoms right closed.2 coherent.2 agrees term
    cases polarity
    · simp only [ofOSLF, NativeStructure.sat, signed, cond] at first second ⊢
      rw [first, second, semEnv, not_and_or]
    · simp only [ofOSLF, NativeStructure.sat, signed, cond] at first second ⊢
      rw [first, second, semEnv]
  | .or left right, _, polarity, _, _, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt, Bool.and_eq_true] at closed
    simp only [consistent, Bool.and_eq_true] at coherent
    have first := sat_ofOSLF step atoms left closed.1 coherent.1 agrees term
    have second := sat_ofOSLF step atoms right closed.2 coherent.2 agrees term
    cases polarity
    · simp only [ofOSLF, NativeStructure.sat, signed, cond] at first second ⊢
      rw [first, second, semEnv, not_or]
    · simp only [ofOSLF, NativeStructure.sat, signed, cond] at first second ⊢
      rw [first, second, semEnv]
  | .imp premise conclusion, _, polarity, _, _, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt, Bool.and_eq_true] at closed
    simp only [consistent, Bool.and_eq_true] at coherent
    cases polarity
    · have first := sat_ofOSLF step atoms premise closed.1 coherent.1 agrees term
      have second := sat_ofOSLF step atoms conclusion closed.2 coherent.2 agrees term
      simp only [ofOSLF, NativeStructure.sat, signed, cond, Bool.not_false] at first second ⊢
      rw [first, second, semEnv, Classical.not_imp]
    · have first := sat_ofOSLF step atoms premise closed.1 coherent.1 agrees term
      have second := sat_ofOSLF step atoms conclusion closed.2 coherent.2 agrees term
      simp only [ofOSLF, NativeStructure.sat, signed, cond, Bool.not_true] at first second ⊢
      rw [first, second, semEnv, imp_iff_not_or]
  | .dia inner, _, polarity, _, _, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt] at closed
    simp only [consistent] at coherent
    have holds := fun next => sat_ofOSLF step atoms inner closed coherent agrees next
    cases polarity
    · simp only [ofOSLF, NativeStructure.sat, syntactic, signed, cond, true_and, semEnv, not_exists, not_and] at holds ⊢
      exact forall_congr' fun next => imp_congr_right fun _ => holds next
    · simp only [ofOSLF, NativeStructure.sat, syntactic, signed, cond, true_and, semEnv] at holds ⊢
      exact exists_congr fun next => and_congr_right fun _ => holds next
  | .box inner, _, polarity, _, _, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt] at closed
    simp only [consistent] at coherent
    have holds := fun previous => sat_ofOSLF step atoms inner closed coherent agrees previous
    cases polarity
    · simp only [ofOSLF, NativeStructure.sat, syntactic, signed, cond, true_and, semEnv, not_forall, exists_prop]
        at holds ⊢
      exact exists_congr fun previous => and_congr_right fun _ => holds previous
    · simp only [ofOSLF, NativeStructure.sat, syntactic, signed, cond, true_and, semEnv] at holds ⊢
      exact forall_congr' fun previous => imp_congr_right fun _ => holds previous
  | .var index, depth, polarity, _, signs, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt, decide_eq_true_eq] at closed
    simp only [consistent, beq_iff_eq] at coherent
    have := agrees.scope_variable index closed term
    rw [coherent] at this
    simpa [ofOSLF, closed, NativeStructure.sat, semEnv] using this
  | .mu body, depth, polarity, scope, signs, env, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt] at closed
    simp only [consistent] at coherent
    cases polarity
    · change (∃ invariant : Set Pattern, term ∈ invariant ∧ ∀ other ∈ invariant,
          (syntactic step).sat (env.extend invariant) (ofOSLF positive negative (depth + 1) false body) other) ↔
        ¬ (∀ candidate : Pattern → Prop, True →
          (∀ other, semEnv step fullFrame atoms (ScopeEnv.push candidate scope) body other → candidate other) →
            candidate term)
      constructor
      · rintro ⟨invariant, inside, preserved⟩ least
        have closedUnder : ∀ other, semEnv step fullFrame atoms (ScopeEnv.push (fun other => other ∉ invariant) scope)
            body other → other ∉ invariant := by
          intro other holds member
          have := (sat_ofOSLF step atoms body closed coherent
            (agrees.extend false (fun other => other ∉ invariant) invariant fun _ => by simp [signed]) other).mp
              (preserved other member)
          exact this holds
        exact least _ trivial closedUnder inside
      · intro notLeast
        simp only [not_forall, exists_prop] at notLeast
        obtain ⟨candidate, -, closedUnder, outside⟩ := notLeast
        refine ⟨{other | ¬ candidate other}, outside, fun other member => ?_⟩
        exact (sat_ofOSLF step atoms body closed coherent
          (agrees.extend false candidate _ fun _ => Iff.rfl) other).mpr fun holds => member (closedUnder other holds)
    · change (∀ closedSet : Set Pattern, (∀ other,
          (syntactic step).sat (env.extend closedSet) (ofOSLF positive negative (depth + 1) true body) other →
            other ∈ closedSet) → term ∈ closedSet) ↔
        (∀ candidate : Pattern → Prop, True →
          (∀ other, semEnv step fullFrame atoms (ScopeEnv.push candidate scope) body other → candidate other) →
            candidate term)
      constructor
      · intro least candidate _ closedUnder
        exact least {other | candidate other} fun other holds =>
          closedUnder other ((sat_ofOSLF step atoms body closed coherent
            (agrees.extend true candidate _ fun _ => Iff.rfl) other).mp holds)
      · intro least closedSet closedUnder
        exact least (fun other => other ∈ closedSet) trivial fun other holds =>
          closedUnder other ((sat_ofOSLF step atoms body closed coherent
            (agrees.extend true (fun other => other ∈ closedSet) closedSet fun _ => Iff.rfl) other).mpr holds)
  | .emptyColl _, _, polarity, _, _, _, _, _, _, _ => by cases polarity <;> rfl
  | .cut kind left right, _, polarity, scope, _, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt, Bool.and_eq_true] at closed
    simp only [consistent, Bool.and_eq_true] at coherent
    have first := fun part => sat_ofOSLF step atoms left closed.1 coherent.1 agrees part
    have second := fun part => sat_ofOSLF step atoms right closed.2 coherent.2 agrees part
    cases polarity
    · change (∀ firstPart secondPart, (∃ leftElements rightElements,
          term = .collection kind (leftElements ++ rightElements) none ∧ firstPart = .collection kind leftElements none ∧
            secondPart = .collection kind rightElements none) →
          (syntactic step).sat _ (ofOSLF positive negative _ false left) firstPart ∨
            (syntactic step).sat _ (ofOSLF positive negative _ false right) secondPart) ↔
        ¬ ∃ leftElements rightElements : List Pattern, term = .collection kind (leftElements ++ rightElements) none ∧
          semEnv step fullFrame atoms _ left (.collection kind leftElements none) ∧
            semEnv step fullFrame atoms _ right (.collection kind rightElements none)
      constructor
      · rintro every ⟨leftElements, rightElements, whole, inLeft, inRight⟩
        rcases every _ _ ⟨leftElements, rightElements, whole, rfl, rfl⟩ with failsLeft | failsRight
        · exact ((first _).mp failsLeft) inLeft
        · exact ((second _).mp failsRight) inRight
      · rintro absent _ _ ⟨leftElements, rightElements, whole, rfl, rfl⟩
        by_cases inLeft : semEnv step fullFrame atoms scope left (.collection kind leftElements none)
        · exact Or.inr ((second _).mpr fun inRight => absent ⟨leftElements, rightElements, whole, inLeft, inRight⟩)
        · exact Or.inl ((first _).mpr inLeft)
    · change (∃ firstPart secondPart, (∃ leftElements rightElements,
          term = .collection kind (leftElements ++ rightElements) none ∧ firstPart = .collection kind leftElements none ∧
            secondPart = .collection kind rightElements none) ∧
          (syntactic step).sat _ (ofOSLF positive negative _ true left) firstPart ∧
            (syntactic step).sat _ (ofOSLF positive negative _ true right) secondPart) ↔
        ∃ leftElements rightElements : List Pattern, term = .collection kind (leftElements ++ rightElements) none ∧
          semEnv step fullFrame atoms _ left (.collection kind leftElements none) ∧
            semEnv step fullFrame atoms _ right (.collection kind rightElements none)
      constructor
      · rintro ⟨_, _, ⟨leftElements, rightElements, whole, rfl, rfl⟩, inLeft, inRight⟩
        exact ⟨leftElements, rightElements, whole, (first _).mp inLeft, (second _).mp inRight⟩
      · rintro ⟨leftElements, rightElements, whole, inLeft, inRight⟩
        exact ⟨_, _, ⟨leftElements, rightElements, whole, rfl, rfl⟩, (first _).mpr inLeft, (second _).mpr inRight⟩
  | .headed label inner, _, polarity, _, _, _, closed, coherent, agrees, term => by
    simp only [OSLFFormula.closedAt] at closed
    simp only [consistent] at coherent
    have holds := fun part => sat_ofOSLF step atoms inner closed coherent agrees part
    cases polarity
    · change (∀ parts, term = .apply label parts →
          (syntactic step).satSome _ (.cons (ofOSLF positive negative _ false inner) .nil) parts) ↔
        ¬ ∃ part, term = .apply label [part] ∧ semEnv step fullFrame atoms _ inner part
      constructor
      · rintro every ⟨part, rfl, inside⟩
        rcases every [part] rfl with fails | impossible
        · exact ((holds part).mp fails) inside
        · exact impossible
      · rintro absent parts rfl
        match parts with
        | [] => trivial
        | [part] => exact Or.inl ((holds part).mpr fun inside => absent ⟨part, rfl, inside⟩)
        | _ :: _ :: _ => exact Or.inr trivial
    · change (∃ parts, term = .apply label parts ∧
          (syntactic step).satAll _ (.cons (ofOSLF positive negative _ true inner) .nil) parts) ↔
        ∃ part, term = .apply label [part] ∧ semEnv step fullFrame atoms _ inner part
      constructor
      · rintro ⟨parts, rfl, inside⟩
        match parts, inside with
        | [part], ⟨inside, _⟩ => exact ⟨part, rfl, (holds part).mp inside⟩
      · rintro ⟨part, rfl, inside⟩
        exact ⟨[part], rfl, (holds part).mpr inside, trivial⟩

end OSLF

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings
