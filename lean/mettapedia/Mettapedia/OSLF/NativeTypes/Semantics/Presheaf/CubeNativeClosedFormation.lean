import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeCertificates

/-!
# Cube formation from closed declaration types

Closed parameter types are formed in the empty context and carried by the
ordinary substitution rules into each telescope. Dependent result formation
still checks the actual ordered code projections and primitive arguments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeClosedFormation

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates
open CubeNativeDeclarations CubeEnrichment

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

/-- Empty-context formation is transported by an actual native substitution
tree, rather than rebuilt under the growing source context. -/
def closedFormation {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context))
    (type : TypeExpr (symbols D) 0)
    (closed : Derivation (signature vertex) (.type .nil type)) :
    Derivation (signature vertex) (.type context (type.rename Fin.elim0)) := by
  have mapping : (Fin.elim0 : Substitution (symbols D) 0 n) =
      (fun position => TermExpr.var (Fin.elim0 position)) := by
    funext position
    exact Fin.elim0 position
  have equal : type.substitute (Fin.elim0 : Substitution (symbols D) 0 n) =
      type.rename Fin.elim0 := by
    rw [mapping, TypeExpr.substitute_variables]
  exact (congrArg (Judgment.type context) equal) ▸
    deriveList (.substituteType context .nil Fin.elim0 type)
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
        (.cons closed .nil))

def codeFormation (carrier : D.Carrier) {n : Nat}
    {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context)) :
    Derivation (signature vertex) (.type context (codeType carrier n)) := by
  exact (congrArg (Judgment.type context) (codeType_rename carrier Fin.elim0)) ▸
    closedFormation vertex formed (codeType carrier 0)
      (codeFormed vertex carrier (emptyFormed vertex))

def certifiedFormation (carrier : D.Carrier)
    (sort : Mettapedia.OSLF.Framework.ModalHypercube.HSort) {n : Nat}
    {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context)) :
    Derivation (signature vertex) (.type context (certifiedCode carrier sort n)) := by
  exact (congrArg (Judgment.type context) (certifiedCode_rename carrier sort Fin.elim0)) ▸
    closedFormation vertex formed (certifiedCode carrier sort 0)
      (certifiedFormed vertex carrier sort (emptyFormed vertex))

def vectorFormation : {n : Nat} → (types : Fin n → TypeExpr (symbols D) 0) →
    (∀ position, Derivation (signature vertex) (.type .nil (types position))) →
    Derivation (signature vertex) (.context (vectorTelescope types))
  | 0, _, _ => emptyFormed vertex
  | n + 1, types, closed =>
      let prior := vectorFormation (fun position : Fin n => types position.succ)
        (fun position => closed position.succ)
      extendFormed vertex prior (closedFormation vertex prior (types 0) (closed 0))

def parametersFormation (declaration : D.Former) :
    Derivation (signature vertex) (.context (parameterContext declaration)) :=
  vectorFormation vertex _ (fun position =>
    codeFormed vertex (D.input declaration position) (emptyFormed vertex))

def formationParametersFormation (declaration : D.Former) :
    Derivation (signature vertex) (.context (formationContext vertex declaration)) :=
  vectorFormation vertex _ (fun position => certifiedFormed vertex
    (D.input declaration position) (inputSort D vertex declaration position) (emptyFormed vertex))

def vectorSubstitution {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context)) :
    {m : Nat} → (types : Fin m → TypeExpr (symbols D) 0) →
    (∀ position, Derivation (signature vertex) (.type .nil (types position))) →
    (mapping : Substitution (symbols D) m n) →
    (∀ position, Derivation (signature vertex) (.term context (mapping position)
      ((types position).rename Fin.elim0))) →
    Derivation (signature vertex) (.substitution context (vectorTelescope types) mapping)
  | 0, _, _, mapping, _ => by
      have equal : mapping = Fin.elim0 := by funext position; exact Fin.elim0 position
      exact (congrArg (Judgment.substitution context .nil) equal).symm ▸
        deriveList (.substitutionNil context) (.cons formed .nil)
  | m + 1, types, closed, mapping, typed => by
      let tail := fun position : Fin m => mapping position.succ
      let tailTypes := fun position : Fin m => types position.succ
      let prior := vectorSubstitution formed tailTypes (fun position => closed position.succ)
        tail (fun position => typed position.succ)
      let tailFormed := vectorFormation vertex tailTypes (fun position => closed position.succ)
      have adjusted : Derivation (signature vertex) (.term context (mapping 0)
          (((types 0).rename (Fin.elim0 : Renaming 0 m)).substitute tail)) :=
        (congrArg (Judgment.term context (mapping 0))
          (closed_substitute (types 0) tail)).symm ▸ typed 0
      have tree := deriveList (.substitutionExtend context (vectorTelescope tailTypes)
        ((types 0).rename Fin.elim0) tail (mapping 0))
        (.cons prior (.cons (closedFormation vertex tailFormed (types 0) (closed 0))
          (.cons adjusted .nil)))
      have equal : extendSubstitution tail (mapping 0) = mapping := by
        funext position
        cases position using Fin.cases <;> rfl
      exact (congrArg (Judgment.substitution context (vectorTelescope types)) equal) ▸ tree

/-- The dependent typing body needs only its displayed code variable. Its
formation is transported from that single-variable context. -/
def typingBodyFormation (carrier : D.Carrier)
    (sort : Mettapedia.OSLF.Framework.ModalHypercube.HSort) {n : Nat}
    {context : ContextExpr (symbols D) n}
    (formed : Derivation (signature vertex) (.context context)) :
    Derivation (signature vertex) (.type (.snoc context (codeType carrier n))
      (typingType carrier (.var 0) (sortCode carrier sort (n + 1)))) := by
  let closedContext := extendFormed vertex (emptyFormed vertex)
    (codeFormed vertex carrier (emptyFormed vertex))
  let closedBody := typingFormed vertex carrier closedContext (.var 0) (sortCode carrier sort 1)
    (codeVariable vertex carrier (emptyFormed vertex)) (sortFormed vertex carrier sort closedContext)
  let extended := extendFormed vertex formed (codeFormation vertex carrier formed)
  have genericCode : Derivation (signature vertex)
      (.term (.snoc context (codeType carrier n)) (.var 0) (codeType carrier (n + 1))) := by
    have equal : (ContextExpr.snoc context (codeType carrier n)).lookup 0 = codeType carrier (n + 1) := by
      simp only [ContextExpr.lookup_zero, codeType_rename]
    exact (congrArg (Judgment.term (.snoc context (codeType carrier n)) (.var 0)) equal) ▸
      deriveList (.variable (.snoc context (codeType carrier n)) 0) (.cons extended .nil)
  let mapping : Substitution (symbols D) 1 (n + 1) := extendSubstitution Fin.elim0 (.var 0)
  let arguments := codeArgument vertex carrier
    (deriveList (.substitutionNil (.snoc context (codeType carrier n))) (.cons extended .nil))
    (codeFormed vertex carrier (emptyFormed vertex)) genericCode
  have equal : (typingType carrier (.var 0) (sortCode carrier sort 1)).substitute mapping =
      typingType carrier (.var 0) (sortCode carrier sort (n + 1)) := by
    unfold typingType
    simp only [TypeExpr.substitute]
    apply congrArg (TypeExpr.family (S := symbols D) (.typing carrier))
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ previous =>
      change (sortCode carrier sort 1).substitute mapping = sortCode carrier sort (n + 1)
      apply congrArg (TermExpr.primitive (S := symbols D) (.sort carrier sort))
      funext position
      exact Fin.elim0 position
  exact (congrArg (Judgment.type (.snoc context (codeType carrier n))) equal) ▸
    deriveList (.substituteType (.snoc context (codeType carrier n))
      (.snoc .nil (codeType carrier 0)) mapping
      (typingType carrier (.var 0) (sortCode carrier sort 1)))
      (.cons arguments (.cons closedBody .nil))

def projectedFormation (declaration : D.Former) (position : Fin (D.arity declaration)) :
    Derivation (signature vertex) (.term (formationContext vertex declaration)
      (codeArguments vertex declaration position) (codeType (D.input declaration position) _)) := by
  let formed := formationParametersFormation vertex declaration
  let carrier := D.input declaration position
  let sort := inputSort D vertex declaration position
  let domain := codeFormation vertex carrier formed
  let body := typingBodyFormation vertex carrier sort formed
  have parameter : Derivation (signature vertex)
      (.term (formationContext vertex declaration) (.var position) (certifiedCode carrier sort _)) :=
    (congrArg (Judgment.term (formationContext vertex declaration) (.var position))
      (certifiedCode_rename carrier sort (Fin.elim0 : Renaming 0 (D.arity declaration)))) ▸
        vectorVariable vertex _ formed position
  exact deriveList (.firstProjection (formationContext vertex declaration) (codeType carrier _)
    (typingType carrier (.var 0) (sortCode carrier sort _)) (.var position))
    (.cons domain (.cons body (.cons parameter .nil)))

def formerResultFormation (declaration : D.Former) :
    Derivation (signature vertex) (.type (parameterContext declaration)
      (codeType (D.output declaration) _)) :=
  codeFormation vertex _ (parametersFormation vertex declaration)

def formedCodeFormation (declaration : D.Former) :
    Derivation (signature vertex) (.term (formationContext vertex declaration)
      (formedCode vertex declaration) (codeType (D.output declaration) _)) := by
  let formed := formationParametersFormation vertex declaration
  let arguments := vectorSubstitution vertex formed
    (fun position => codeType (D.input declaration position) 0)
    (fun position => codeFormed vertex (D.input declaration position) (emptyFormed vertex))
    (codeArguments vertex declaration)
    (fun position => (congrArg (Judgment.term (formationContext vertex declaration)
      (codeArguments vertex declaration position))
        (codeType_rename _ (Fin.elim0 : Renaming 0 (D.arity declaration)))).symm ▸
          projectedFormation vertex declaration position)
  have tree := deriveList (.primitive (formationContext vertex declaration) (.former declaration)
    (codeArguments vertex declaration))
    (.cons formed (.cons (parametersFormation vertex declaration)
      (.cons (formerResultFormation vertex declaration) (.cons arguments .nil))))
  have equal : (RuleCode.primitive (D := signature vertex) (formationContext vertex declaration)
      (.former declaration) (codeArguments vertex declaration)).conclusion =
      .term (formationContext vertex declaration) (formedCode vertex declaration)
        (codeType (D.output declaration) (D.arity declaration)) := by
    simp only [RuleCode.conclusion, signature, codeType_substitute, formedCode]
  exact equal ▸ tree

def formationResultFormation (declaration : D.Former) :
    Derivation (signature vertex) (.type (formationContext vertex declaration)
      (formationResult vertex declaration)) :=
  typingFormed vertex (D.output declaration) (formationParametersFormation vertex declaration)
    (formedCode vertex declaration) (sortCode (D.output declaration) (outputSort D vertex declaration) _)
    (formedCodeFormation vertex declaration)
    (sortFormed vertex _ _ (formationParametersFormation vertex declaration))

def parameterFormation (symbol : TermSymbol D) :
    Derivation (signature vertex) (.context ((signature vertex).termParameters symbol)) :=
  match symbol with
  | .sort _ _ | .starBox _ => emptyFormed vertex
  | .former declaration => parametersFormation vertex declaration
  | .formation declaration => formationParametersFormation vertex declaration

def resultFormation (symbol : TermSymbol D) :
    Derivation (signature vertex) (.type ((signature vertex).termParameters symbol)
      ((signature vertex).termResult symbol)) :=
  match symbol with
  | .sort carrier _ => codeFormed vertex carrier (emptyFormed vertex)
  | .former declaration => formerResultFormation vertex declaration
  | .starBox carrier => typingFormed vertex carrier (emptyFormed vertex)
      (sortCode carrier .star 0) (sortCode carrier .box 0)
      (sortFormed vertex carrier .star (emptyFormed vertex))
      (sortFormed vertex carrier .box (emptyFormed vertex))
  | .formation declaration => formationResultFormation vertex declaration

def primitiveFormation (symbol : TermSymbol D) :
    Derivation (signature vertex) (.term ((signature vertex).termParameters symbol)
      (.primitive symbol TermExpr.var) ((signature vertex).termResult symbol)) := by
  let formed := parameterFormation vertex symbol
  have tree := deriveList (.primitive ((signature vertex).termParameters symbol) symbol TermExpr.var)
    (.cons formed (.cons formed (.cons (resultFormation vertex symbol)
      (.cons (deriveList (.substitutionIdentity ((signature vertex).termParameters symbol))
        (.cons formed .nil)) .nil))))
  have equal : (RuleCode.primitive (D := signature vertex) ((signature vertex).termParameters symbol)
      symbol TermExpr.var).conclusion =
      .term ((signature vertex).termParameters symbol) (.primitive symbol TermExpr.var)
        ((signature vertex).termResult symbol) := by
    simp only [RuleCode.conclusion, TypeExpr.substitute_identity]
  exact equal ▸ tree

variable [DecidableEq D.Carrier] [DecidableEq D.Former]

def primitiveCertificate (symbol : TermSymbol D) : Refinement.Certificate (signature vertex) :=
  Refinement.erase (primitiveFormation vertex symbol)

theorem primitiveCertificate_checked (symbol : TermSymbol D) :
    Refinement.check (primitiveCertificate vertex symbol)
      (.term ((signature vertex).termParameters symbol) (.primitive symbol TermExpr.var)
        ((signature vertex).termResult symbol)) = true :=
  Refinement.check_erase (primitiveFormation vertex symbol)

theorem primitiveCertificate_same_judgment (symbol : TermSymbol D) :
    Refinement.check (primitiveCertificate vertex symbol)
      (CubeNativeDeclarations.primitiveCertificate vertex symbol).root.conclusion = true := by
  have original := CubeNativeDeclarations.primitiveCertificate_checked vertex symbol
  have root : (CubeNativeDeclarations.primitiveCertificate vertex symbol).root.conclusion =
      .term ((signature vertex).termParameters symbol) (.primitive symbol TermExpr.var)
        ((signature vertex).termResult symbol) := by
    cases certificate : CubeNativeDeclarations.primitiveCertificate vertex symbol with
    | node rule children =>
      rw [certificate] at original
      have clauses : decide (rule.conclusion =
          .term ((signature vertex).termParameters symbol) (.primitive symbol TermExpr.var)
            ((signature vertex).termResult symbol)) = true ∧
          decide (∀ position,
            Tree.check (children position) (rule.premises.get position) = true) = true := by
        simpa only [Refinement.check, Tree.check, Bool.and_eq_true] using original
      exact of_decide_eq_true clauses.1
  rw [root]
  exact primitiveCertificate_checked vertex symbol

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeClosedFormation
