import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeCertificates

/-!
# Independent cube formation witnesses in the common native grammar

The free code syntax and its independently specified kind derivations compile
to ordinary native terms and complete native evidence trees. No predicate
oracle interprets kinding, and no new checker substitutes for native rules.
Operational injections have their separate source-preserving declaration join.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindEncoding

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature}

abbrev PureCode (carrier : D.Carrier) := CubeEnrichment.Code D (fun _ => Empty) carrier

def encode {n : Nat} : {carrier : D.Carrier} → PureCode carrier → TermExpr (symbols D) n
  | _, .operational impossible => nomatch impossible
  | carrier, .sort sort => sortCode carrier sort n
  | _, .former declaration arguments => .primitive (.former declaration) (fun position => encode (arguments position))

variable (vertex : Vertex D)

/-- The whole free code family has actual native term formation trees. -/
def encodeFormation {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context)) :
    {carrier : D.Carrier} → (code : PureCode carrier) →
    Derivation (signature vertex) (.term context (encode code) (codeType carrier n))
  | _, .operational impossible => nomatch impossible
  | carrier, .sort sort => sortFormed vertex carrier sort formed
  | _, .former declaration values => by
      let arguments := fun position => encode (n := n) (values position)
      let parameters := vectorArguments vertex formed
        (fun position => codeType (D.input declaration position) 0)
        (by intro position m gamma tree; exact
          (congrArg (Judgment.type gamma) (codeType_rename _ (Fin.elim0 : Renaming 0 m))).symm ▸
            codeFormed vertex _ tree)
        arguments (fun position =>
          (congrArg (Judgment.term context (arguments position))
            (codeType_rename _ (Fin.elim0 : Renaming 0 n))).symm ▸
              encodeFormation formed (values position))
      have tree := deriveList (D := signature vertex) (.primitive context (.former declaration) arguments)
        (.cons formed (.cons (parametersFormed vertex declaration)
          (.cons (formerResultFormed vertex declaration) (.cons parameters .nil))))
      have equal : (RuleCode.primitive (D := signature vertex) context (.former declaration) arguments).conclusion =
          .term context (encode (.former declaration values)) (codeType (D.output declaration) n) := by
        simp only [RuleCode.conclusion, signature, codeType_substitute, encode, arguments]
      exact equal ▸ tree

@[simp] theorem sortCode_substitute (carrier : D.Carrier) (sort : HSort) {n m : Nat}
    (mapping : Substitution (symbols D) n m) :
    (sortCode carrier sort n).substitute mapping = sortCode carrier sort m := by
  apply congrArg (TermExpr.primitive (S := symbols D) (.sort carrier sort))
  funext position
  exact Fin.elim0 position

@[simp] theorem typingType_substitute (carrier : D.Carrier) {n m : Nat}
    (first second : TermExpr (symbols D) n) (mapping : Substitution (symbols D) n m) :
    (typingType carrier first second).substitute mapping =
      typingType carrier (first.substitute mapping) (second.substitute mapping) := by
  apply congrArg (TypeExpr.family (S := symbols D) (.typing carrier))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ _ => rfl

@[simp] theorem typingBody_instantiate (carrier : D.Carrier) (sort : HSort) {n : Nat}
    (value : TermExpr (symbols D) n) :
    (typingType carrier (.var 0) (sortCode carrier sort (n+1))).substitute (instantiate value) =
      typingType carrier value (sortCode carrier sort n) := by
  rw [typingType_substitute, sortCode_substitute]
  rfl

/-- Kind evidence is an ordinary primitive witness at the selected result
family. Each input keeps its code and its complete recursively generated tree. -/
def witness {n : Nat} : {carrier : D.Carrier} → {code : PureCode carrier} → {kind : HSort} →
    Kinded vertex code kind → TermExpr (symbols D) n
  | carrier, _, _, .star => .primitive (.starBox carrier) Fin.elim0
  | _, _, _, .former declaration arguments premises =>
      .primitive (.formation declaration) (fun position =>
        .pair (codeType (D.input declaration position) n)
          (typingType (D.input declaration position) (.var 0)
            (sortCode (D.input declaration position) (inputSort D vertex declaration position) (n+1)))
          (encode (arguments position)) (witness (premises position)))

/-- Independent equality witnesses for every ordered code parameter lift
through the actual generated native substitution rules. -/
def codeVectorEquality {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context)) :
    {m : Nat} → (carriers : Fin m → D.Carrier) →
    (first second : Substitution (symbols D) m n) →
    (∀ position, Derivation (signature vertex)
      (.termEq context (first position) (second position) (codeType (carriers position) n))) →
    (∀ position, Derivation (signature vertex)
      (.term context (second position) (codeType (carriers position) n))) →
    Derivation (signature vertex)
      (.substitutionEq context (vectorTelescope (fun position => codeType (carriers position) 0)) first second)
  | 0, _, first, second, _, _ => by
      have left : first = Fin.elim0 := by funext impossible; exact Fin.elim0 impossible
      have right : second = Fin.elim0 := by funext impossible; exact Fin.elim0 impossible
      cases left
      cases right
      exact deriveList (.substitutionReflexivity context .nil Fin.elim0)
        (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)
  | m+1, carriers, first, second, equal, typed => by
      let left := fun position : Fin m => first position.succ
      let right := fun position : Fin m => second position.succ
      let tailCarriers := fun position : Fin m => carriers position.succ
      let tailContext := vectorTelescope (fun position => codeType (tailCarriers position) 0)
      let contextTree := vectorFormed vertex (fun position => codeType (tailCarriers position) 0)
        (by intro position length gamma tree; exact
          (congrArg (Judgment.type gamma) (codeType_rename _ (Fin.elim0 : Renaming 0 length))).symm ▸
            codeFormed vertex _ tree)
      let previous := codeVectorEquality formed tailCarriers left right
        (fun position => equal position.succ) (fun position => typed position.succ)
      have typeSame : (codeType (carriers 0) m).substitute left = codeType (carriers 0) n :=
        codeType_substitute _ left
      have otherSame : (codeType (carriers 0) m).substitute right = codeType (carriers 0) n :=
        codeType_substitute _ right
      let equation := (congrArg (Judgment.termEq context (first 0) (second 0)) typeSame).symm ▸ equal 0
      let value := (congrArg (Judgment.term context (second 0)) otherSame).symm ▸ typed 0
      have tree := deriveList (.substitutionExtendEquality context tailContext (codeType (carriers 0) m)
        left right (first 0) (second 0))
        (.cons previous (.cons (codeFormed vertex _ contextTree) (.cons equation (.cons value .nil))))
      have targetSame : ContextExpr.snoc tailContext (codeType (carriers 0) m) =
          vectorTelescope (fun position => codeType (carriers position) 0) := by
        simp only [vectorTelescope, tailContext, tailCarriers, codeType_rename]
      have leftSame : extendSubstitution left (first 0) = first := by
        funext position; cases position using Fin.cases <;> rfl
      have rightSame : extendSubstitution right (second 0) = second := by
        funext position; cases position using Fin.cases <;> rfl
      have same : (RuleCode.substitutionExtendEquality (D := signature vertex) context tailContext
          (codeType (carriers 0) m) left right (first 0) (second 0)).conclusion =
          .substitutionEq context (vectorTelescope (fun position => codeType (carriers position) 0)) first second := by
        simp only [RuleCode.conclusion, targetSame, leftSame, rightSame]
      exact same ▸ tree

def witnessFormation {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context)) :
    {carrier : D.Carrier} → {code : PureCode carrier} → {kind : HSort} →
    (evidence : Kinded vertex code kind) →
    Derivation (signature vertex)
      (.term context (witness vertex evidence) (typingType carrier (encode code) (sortCode carrier kind n)))
  | carrier, _, _, .star => by
      let result := (headers vertex).termResult (.starBox carrier)
      have tree := deriveList (D := signature vertex) (.primitive context (.starBox carrier) Fin.elim0)
        (.cons formed (.cons (emptyFormed vertex)
          (.cons result (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil))))
      have equal : (RuleCode.primitive (D := signature vertex) context (.starBox carrier) Fin.elim0).conclusion =
          .term context (witness vertex (.star (carrier := carrier)))
            (typingType carrier (encode (CubeEnrichment.Code.sort .star : PureCode carrier)) (sortCode carrier .box n)) := by
        simp only [RuleCode.conclusion, signature, witness, encode, typingType_substitute, sortCode_substitute]
      exact equal ▸ tree
  | _, _, _, .former declaration arguments premises => by
      let actual := fun position =>
        TermExpr.pair (codeType (D.input declaration position) n)
          (typingType (D.input declaration position) (.var 0)
            (sortCode (D.input declaration position) (inputSort D vertex declaration position) (n+1)))
          (encode (arguments position)) (witness vertex (premises position))
      have actualFormed (position : Fin (D.arity declaration)) :
          Derivation (signature vertex) (.term context (actual position)
            (certifiedCode (D.input declaration position) (inputSort D vertex declaration position) n)) := by
        let carrier := D.input declaration position
        let kind := inputSort D vertex declaration position
        let codeTree := codeFormed vertex carrier formed
        let extended := extendFormed vertex formed codeTree
        let body := typingFormed vertex carrier extended (.var 0) (sortCode carrier kind (n+1))
          (codeVariable vertex carrier formed) (sortFormed vertex carrier kind extended)
        have adjusted : Derivation (signature vertex)
            (.term context (witness vertex (premises position))
              ((typingType carrier (.var 0) (sortCode carrier kind (n+1))).substitute
                (instantiate (encode (arguments position))))) :=
          (congrArg (Judgment.term context (witness vertex (premises position)))
            (typingBody_instantiate carrier kind (encode (arguments position)))).symm ▸
              witnessFormation formed (premises position)
        exact deriveList (.pairIntroduction context (codeType carrier n)
          (typingType carrier (.var 0) (sortCode carrier kind (n+1)))
          (encode (arguments position)) (witness vertex (premises position)))
          (.cons codeTree (.cons body
            (.cons (encodeFormation vertex formed (arguments position)) (.cons adjusted .nil))))
      let parameters := vectorArguments vertex formed
        (fun position => certifiedCode (D.input declaration position) (inputSort D vertex declaration position) 0)
        (by intro position m gamma tree; exact
          (congrArg (Judgment.type gamma) (certifiedCode_rename _ _ (Fin.elim0 : Renaming 0 m))).symm ▸
            certifiedFormed vertex _ _ tree)
        actual (fun position =>
          (congrArg (Judgment.term context (actual position))
            (certifiedCode_rename _ _ (Fin.elim0 : Renaming 0 n))).symm ▸ actualFormed position)
      have tree := deriveList (D := signature vertex) (.primitive context (.formation declaration) actual)
        (.cons formed (.cons (formationParametersFormed vertex declaration)
          (.cons (formationResultFormed vertex declaration) (.cons parameters .nil))))
      let projected := fun position => (codeArguments vertex declaration position).substitute actual
      have projectionEqual (position : Fin (D.arity declaration)) :
          Derivation (signature vertex) (.termEq context (projected position)
            (encode (arguments position)) (codeType (D.input declaration position) n)) := by
        let carrier := D.input declaration position
        let kind := inputSort D vertex declaration position
        let codeTree := codeFormed vertex carrier formed
        let extended := extendFormed vertex formed codeTree
        let body := typingFormed vertex carrier extended (.var 0) (sortCode carrier kind (n+1))
          (codeVariable vertex carrier formed) (sortFormed vertex carrier kind extended)
        have adjusted : Derivation (signature vertex)
            (.term context (witness vertex (premises position))
              ((typingType carrier (.var 0) (sortCode carrier kind (n+1))).substitute
                (instantiate (encode (arguments position))))) :=
          (congrArg (Judgment.term context (witness vertex (premises position)))
            (typingBody_instantiate carrier kind (encode (arguments position)))).symm ▸
              witnessFormation formed (premises position)
        have beta := deriveList (.sigmaFirstBeta context (codeType carrier n)
          (typingType carrier (.var 0) (sortCode carrier kind (n+1)))
          (encode (arguments position)) (witness vertex (premises position)))
          (.cons codeTree (.cons body
            (.cons (encodeFormation vertex formed (arguments position)) (.cons adjusted .nil))))
        have same : (RuleCode.sigmaFirstBeta (D := signature vertex) context (codeType carrier n)
            (typingType carrier (.var 0) (sortCode carrier kind (n+1)))
            (encode (arguments position)) (witness vertex (premises position))).conclusion =
            .termEq context (projected position) (encode (arguments position)) (codeType carrier n) := by
          simp only [RuleCode.conclusion, projected, codeArguments, TermExpr.substitute,
            codeType_substitute, typingType_substitute, sortCode_substitute, liftSubstitution_zero, actual, carrier, kind]
        exact same ▸ beta
      let sourceCode : TermExpr (symbols D) n := .primitive (.former declaration) projected
      let targetCode : TermExpr (symbols D) n := encode (.former declaration arguments)
      let parameterEquality := codeVectorEquality vertex formed (D.input declaration) projected
        (fun position => encode (arguments position)) projectionEqual
        (fun position => encodeFormation vertex formed (arguments position))
      have codeEquality : Derivation (signature vertex)
          (.termEq context sourceCode targetCode (codeType (D.output declaration) n)) := by
        have congruent := deriveList (.primitiveCongruence context (.former declaration) projected
          (fun position => encode (arguments position)))
          (.cons (formerResultFormed vertex declaration) (.cons parameterEquality .nil))
        have same : (RuleCode.primitiveCongruence (D := signature vertex) context (.former declaration)
            projected (fun position => encode (arguments position))).conclusion =
            .termEq context sourceCode targetCode (codeType (D.output declaration) n) := by
          simp only [RuleCode.conclusion, signature, codeType_substitute, sourceCode, targetCode, encode]
        exact same ▸ congruent
      let finalSort := sortCode (D.output declaration) (outputSort D vertex declaration) n
      let first := (Fin.cases sourceCode (fun _ => finalSort) : Substitution (symbols D) 2 n)
      let second := (Fin.cases targetCode (fun _ => finalSort) : Substitution (symbols D) 2 n)
      have equalArguments (position : Fin 2) : Derivation (signature vertex)
          (.termEq context (first position) (second position) (codeType (D.output declaration) n)) := by
        cases position using Fin.cases with
        | zero => exact codeEquality
        | succ previous => cases previous using Fin.cases with
          | zero =>
              exact deriveList (.termReflexivity context finalSort (codeType (D.output declaration) n))
                (.cons (sortFormed vertex _ _ formed) .nil)
          | succ impossible => exact Fin.elim0 impossible
      have rightArguments (position : Fin 2) : Derivation (signature vertex)
          (.term context (second position) (codeType (D.output declaration) n)) := by
        cases position using Fin.cases with
        | zero => exact encodeFormation vertex formed (.former declaration arguments)
        | succ previous => cases previous using Fin.cases with
          | zero => exact sortFormed vertex _ _ formed
          | succ impossible => exact Fin.elim0 impossible
      have equationArguments : Derivation (signature vertex)
          (.substitutionEq context (typingContext (D.output declaration)) first second) := by
        have equality := codeVectorEquality vertex formed (fun _ : Fin 2 => D.output declaration)
          first second equalArguments rightArguments
        have same : vectorTelescope (fun _ : Fin 2 => codeType (D.output declaration) 0) =
            typingContext (D.output declaration) := by
          simp only [vectorTelescope, codeType_rename, typingContext]
        exact (congrArg (fun gamma => Judgment.substitutionEq context gamma first second) same) ▸ equality
      have resultEquality : Derivation (signature vertex)
          (.typeEq context (((signature vertex).termResult (.formation declaration)).substitute actual)
            (typingType (D.output declaration) targetCode finalSort)) := by
        have equality := deriveList (.familyCongruence context (.typing (D.output declaration)) first second)
          (.cons (typingContextFormed vertex _) (.cons equationArguments .nil))
        have same : (RuleCode.familyCongruence (D := signature vertex) context (.typing (D.output declaration))
            first second).conclusion =
            .typeEq context (((signature vertex).termResult (.formation declaration)).substitute actual)
              (typingType (D.output declaration) targetCode finalSort) := by
          change Judgment.typeEq context (typingType (D.output declaration) sourceCode finalSort)
              (typingType (D.output declaration) targetCode finalSort) =
            Judgment.typeEq context
              ((typingType (D.output declaration) (formedCode vertex declaration)
                (sortCode (D.output declaration) (outputSort D vertex declaration) (D.arity declaration))).substitute actual)
              (typingType (D.output declaration) targetCode finalSort)
          rw [typingType_substitute, sortCode_substitute]
          rfl
        exact same ▸ equality
      exact deriveList (.termConversion context (witness vertex (.former declaration arguments premises))
        (((signature vertex).termResult (.formation declaration)).substitute actual)
        (typingType (D.output declaration) targetCode finalSort)) (.cons tree (.cons resultEquality .nil))

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindEncoding
