import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.DeclarationLevelInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveHeadMap
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PatternTelescopes

/-!
# Natural addition and vector append using the declared eliminators

The source signature has independent element and motive universe parameters.
This instance chooses the motive universe to be their maximum, so vector-valued
motives are legal at every element universe. The established level-instantiation
morphism transports the original declaration rules; no eliminator is derived
again and no semantic equality is added to conversion.

The programs use the existing scoped core. Textual authoring, constructor-case
elaboration and native backend realization retain their separate interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration RussellTarski
open TypedEquality.Normalization
open Mettapedia.TypeTheory.UniverseLevel

variable {n : Nat}

/-- Elimination may target the element universe or a larger motive universe.
The original two parameters are retained in this declared instance. -/
def levels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 1 then .max (.param 0) (.param 1) else .param parameter

/-- Iota roots mention universe heads only through their arguments. -/
def mapIota (map : Tower.Head → Tower.Head) {n : Nat} {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) : IotaEvidence n (left.mapHead map) (right.mapHead map) := by
  cases evidence with
  | natZero motive zeroCase succCase =>
      exact .natZero (motive.mapHead map) (right.mapHead map) (succCase.mapHead map)
  | natSucc motive zeroCase succCase number =>
      exact .natSucc (motive.mapHead map) (zeroCase.mapHead map) (succCase.mapHead map)
        (number.mapHead map)
  | vecNil element motive nilCase consCase =>
      exact .vecNil (element.mapHead map) (motive.mapHead map) (right.mapHead map)
        (consCase.mapHead map)
  | vecCons element motive nilCase consCase length head tail =>
      exact .vecCons (element.mapHead map) (motive.mapHead map) (nilCase.mapHead map)
        (consCase.mapHead map) (length.mapHead map) (head.mapHead map) (tail.mapHead map)

def levelInstance : LevelInstance rawSignature levels where
  computation := iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨mapIota (substLevelsHead levels) evidence⟩

abbrev signature := levelInstance.signature
abbrev rules := levelInstance.rules

theorem signature_formed : signature.Formed Tower.rules :=
  levelInstance.formed rawSignature_formed

/-- Existing full formed derivations transport through the selected universe
instance. This forward map is not reflection of arbitrary instantiations. -/
theorem judgment_map {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (derived : FormationSensitive.Judgment NativeNaturalVectorFamilies.rules context term type) :
    FormationSensitive.Judgment rules (substLevelsCtx levels context)
      (substLevelsTm levels term) (substLevelsTm levels type) := by
  exact derived.mapHead levelInstance.morphism

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl) Checking.iotaDecoder

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

/-- Search proposes original schema ordinals; replay still checks the root
against the original independent iota decoder. -/
def searchRows (term : Tower.Tm n) : List (Fin Checking.table.length) →
    Option (SchemaTableConversionCode.Code Tower.Head n)
  | [] => none
  | index :: rest =>
      match ExecutableSchemaMatching.reconstruct (Checking.table.get index).2.1 term with
      | none => searchRows term rest
      | some assignment => some (SchemaTableConversionCode.encode Checking.table index assignment)

def searchRoot (term : Tower.Tm n) : Option (decoder.Code n) :=
  (searchRows term (List.finRange Checking.table.length)).map .declared

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (rules.cumulative first second)
  normalize := fun fuel term =>
    match StructuralConversionSearch.normalize decoder searchRoot (headEq := rules.headEq) fuel term with
    | none => term
    | some candidate => candidate.term
  conversion := fun fuel left right =>
    StructuralConversionSearch.compare decoder searchRoot (headEq := rules.headEq) fuel left right

/-- Recursion on the first argument, using the existing natural eliminator. -/
def add (first second : Tower.Tm n) : Tower.Tm n :=
  natEliminateApp (.lam natTm) second (.lam (.lam (succApp (.var 0)))) first

/-- The vector motive retains its length argument; the vector itself is
available to dependent motives even though append does not inspect it here. -/
def appendMotive (element secondLength : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (vecApp (rename (wkN 2) element)
    (add (.var 1) (rename (wkN 2) secondLength))))

/-- Constructor methods receive length, head, tail and the recursive result
in the order specified by the existing vector eliminator. -/
def appendCons (element secondLength : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.lam
    (vconsApp (rename (wkN 4) element)
      (add (.var 3) (rename (wkN 4) secondLength)) (.var 2) (.var 0)))))

def append (element firstLength secondLength left right : Tower.Tm n) : Tower.Tm n :=
  vecEliminateApp element (appendMotive element secondLength) right
    (appendCons element secondLength) firstLength left

def appendContext : Tower.Ctx 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil (.head (.sort elementLevel))) natTm) natTm)
    (vecApp (.var 2) (.var 1))) (vecApp (.var 3) (.var 1))

def appendBody : Tower.Tm 5 := append (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)
def appendResult : Tower.Tm 5 := vecApp (.var 4) (add (.var 3) (.var 2))

def appendTerm : Tower.Tm 0 := TelescopeAbstraction.closeTerm appendContext appendBody
def appendType : Tower.Tm 0 := TelescopeAbstraction.closeType appendContext appendResult

def appendSubmission :=
  FormationSensitiveElaboration.elaborate rules decoder choices 96 (.nil : Tower.Ctx 0)
    appendTerm appendType

end Programs
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
