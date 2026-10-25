import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLInterface
import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation

/-!
# A formed DTT signature for higher-order set operations

One explicit cumulative Pi/Sigma/identity declaration profile carries the
common material HOL signature: membership, empty set, union, powerset,
separation and replacement. Implication, quantification and equality use the
existing formation-sensitive logical interface at every simple type.

These declarations name operations; they add no foundation, choice, infinity
or universe-existence axiom. The same native terms can therefore receive the
well-founded, hyperset and coded-hyperset interpretations. This is a named
profile within the explored DTT space, not a selection of that whole space.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationSignature

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic
open HOL.Embedding.ZFSetHenkinInterpretation

def baseName (_ : Unit) : DeclName := `SetOperationHOL.set

/-- The proof readings extend this declaration namespace at a fresh name. -/
def proofName : DeclName := `SetOperationHOL.proof

def types : TypeInterpretation Unit where
  proposition := .const `SetOperationHOL.prop
  base := fun sort => .const (baseName sort)

def universalType : Tower.Tm 0 :=
  .pi (sortTm Tower.zero)
    (.pi (.pi (.var 0) (.const `SetOperationHOL.prop)) (.const `SetOperationHOL.prop))

def symbolName : {type : HOL.Ty Unit} → Symbol type → DeclName
  | _, .member => `SetOperationHOL.member
  | _, .empty => `SetOperationHOL.empty
  | _, .union => `SetOperationHOL.union
  | _, .power => `SetOperationHOL.power
  | _, .separate => `SetOperationHOL.separate
  | _, .replace => `SetOperationHOL.replace

/-- All constants are opaque, typed operations of the common HOL signature. -/
def declarations : Signature Tower.Head := Signature.ofList
  [(`SetOperationHOL.prop, ⟨sortTm Tower.zero, none⟩),
   (`SetOperationHOL.set, ⟨sortTm Tower.zero, none⟩),
   (`SetOperationHOL.implication, ⟨typeAt types 0 (.arr .prop (.arr .prop .prop)), none⟩),
   (`SetOperationHOL.universal, ⟨universalType, none⟩),
   (`SetOperationHOL.equality, ⟨equalityDeclarationType types.proposition, none⟩),
   (`SetOperationHOL.member, ⟨typeAt types 0 (.arr set (.arr set .prop)), none⟩),
   (`SetOperationHOL.empty, ⟨typeAt types 0 set, none⟩),
   (`SetOperationHOL.union, ⟨typeAt types 0 mapping, none⟩),
   (`SetOperationHOL.power, ⟨typeAt types 0 mapping, none⟩),
   (`SetOperationHOL.separate, ⟨typeAt types 0 (.arr set (.arr predicate set)), none⟩),
   (`SetOperationHOL.replace, ⟨typeAt types 0 (.arr set (.arr mapping set)), none⟩)]

def rules : Rules Tower.Head := extendRules Tower.rules declarations

private theorem proposition_lookup :
    rules.constantType `SetOperationHOL.prop = some (sortTm Tower.zero) := by decide

private theorem base_lookup (sort : Unit) :
    rules.constantType (baseName sort) = some (sortTm Tower.zero) := by
  cases sort; decide

private theorem implication_lookup : rules.constantType `SetOperationHOL.implication =
    some (typeAt types 0 (.arr .prop (.arr .prop .prop))) := by decide

private theorem universal_lookup :
    rules.constantType `SetOperationHOL.universal = some universalType := by decide

private theorem equality_lookup :
    rules.constantType `SetOperationHOL.equality =
      some (equalityDeclarationType types.proposition) := by decide

private theorem symbol_lookup {type : HOL.Ty Unit} (symbol : Symbol type) :
    rules.constantType (symbolName symbol) = some (typeAt types 0 type) := by
  cases symbol <;> decide

theorem proposition_formed {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (.const `SetOperationHOL.prop) (sortTm Tower.zero) :=
  .const proposition_lookup (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem base_formed (sort : Unit) :
    Typing rules .nil (types.base sort) (sortTm Tower.zero) :=
  .const (base_lookup sort) (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem simple_type_formed (type : HOL.Ty Unit) {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (typeAt types n type) (sortTm Tower.zero) :=
  typeAt_formed_of_atoms declarations types (proposition_formed .nil) base_formed type gamma

private theorem pi_zero {n : Nat} {gamma : Tower.Ctx n}
    {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (domain : Typing rules gamma a (sortTm Tower.zero))
    (codomain : Typing rules (.snoc gamma a) b (sortTm Tower.zero)) :
    Typing rules gamma (.pi a b) (sortTm Tower.zero) := by
  apply Typing.cumul (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero)
    (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, LevelTower.zero]

theorem universal_type_formed : Typing rules .nil universalType
    (sortTm (.max (.succ Tower.zero) Tower.zero)) := by
  refine Typing.piForm (R := rules) (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    ?_ (.sort Tower.zero) (.sorts (.succ Tower.zero) Tower.zero)
  exact pi_zero (pi_zero (.var 0) (proposition_formed _)) (proposition_formed _)

def universal (type : HOL.Ty Unit) : Tower.Tm 0 :=
  .app (.const `SetOperationHOL.universal) (typeAt types 0 type)

theorem universal_typed (type : HOL.Ty Unit) :
    Typing rules .nil (universal type) (typeAt types 0 (.arr (.arr type .prop) .prop)) := by
  have symbol : Typing rules .nil (.const `SetOperationHOL.universal) universalType :=
    .const universal_lookup universal_type_formed (.sort (.max (.succ Tower.zero) Tower.zero))
  have applied := Typing.appElim symbol (simple_type_formed type .nil)
  simpa only [universal, universalType, typeAt, types, liftClosed, Presentation.rename,
    inst0, Presentation.subst, subst0, consSub, liftSub, Fin.cases_zero] using applied

def equality (type : HOL.Ty Unit) : Tower.Tm 0 :=
  .app (.const `SetOperationHOL.equality) (typeAt types 0 type)

theorem equality_typed (type : HOL.Ty Unit) :
    Typing rules .nil (equality type) (typeAt types 0 (.arr type (.arr type .prop))) := by
  have symbol : Typing rules .nil (.const `SetOperationHOL.equality)
      (equalityDeclarationType types.proposition) :=
    .const equality_lookup
      (equalityDeclarationType_formed declarations types.proposition (proposition_formed .nil))
      (.sort (.max (.succ Tower.zero) Tower.zero))
  have applied := Typing.appElim symbol (simple_type_formed type .nil)
  simpa only [equality, equalityDeclarationType, typeAt, types, liftClosed, Presentation.rename,
    inst0, Presentation.subst, subst0, consSub, liftSub, Fin.cases_zero, Fin.cases_succ,
    typeAt_rename] using applied

def signature : LogicalSignature Unit Symbol where
  declarations := declarations
  types := types
  proposition_formed := proposition_formed .nil
  base_formed := base_formed
  constant := fun symbol => .const (symbolName symbol)
  constant_typed := by
    intro type symbol
    simpa only [rules, liftClosed, typeAt_rename] using
      Typing.const (Γ := .nil) (symbol_lookup symbol)
        (simple_type_formed type .nil) (.sort Tower.zero)
  implication := .const `SetOperationHOL.implication
  implication_typed := .const implication_lookup
    (simple_type_formed (.arr .prop (.arr .prop .prop)) .nil) (.sort Tower.zero)
  universal := universal
  universal_typed := universal_typed
  equality := equality
  equality_typed := equality_typed


end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationSignature
