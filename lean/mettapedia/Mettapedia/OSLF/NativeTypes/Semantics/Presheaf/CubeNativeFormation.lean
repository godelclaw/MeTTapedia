import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation

/-!
# Generated cube declaration formation in the common native rules
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open CubeEnrichment

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

abbrev Theory := signature vertex

@[simp] theorem codeType_substitute (carrier : D.Carrier) {n m : Nat}
    (substitution : Substitution (symbols D) n m) :
    (codeType carrier n).substitute substitution = codeType carrier m := by
  apply congrArg (TypeExpr.family (S := symbols D) (.code carrier))
  funext position
  exact Fin.elim0 position

def emptyFormed : Derivation (Theory vertex) (.context .nil) := deriveList .contextNil .nil

def codeFormed (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) :
    Derivation (Theory vertex) (.type context (codeType carrier n)) :=
  deriveList (.typeFamily context (.code carrier) Fin.elim0)
    (.cons formed (.cons (emptyFormed vertex)
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

def extendFormed {n : Nat} {context : ContextExpr (symbols D) n} {type : TypeExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context))
    (typed : Derivation (Theory vertex) (.type context type)) :
    Derivation (Theory vertex) (.context (.snoc context type)) :=
  deriveList (.contextExtend context type) (.cons formed (.cons typed .nil))

def typingContextFormed (carrier : D.Carrier) :
    Derivation (Theory vertex) (.context (typingContext carrier)) :=
  let first := extendFormed vertex (emptyFormed vertex) (codeFormed vertex carrier (emptyFormed vertex))
  extendFormed vertex first (codeFormed vertex carrier first)

def codeArgument (carrier : D.Carrier) {n m : Nat} {context : ContextExpr (symbols D) n}
    {target : ContextExpr (symbols D) m} {mapping : Substitution (symbols D) m n}
    {value : TermExpr (symbols D) n}
    (previous : Derivation (Theory vertex) (.substitution context target mapping))
    (formed : Derivation (Theory vertex) (.type target (codeType carrier m)))
    (typed : Derivation (Theory vertex) (.term context value (codeType carrier n))) :
    Derivation (Theory vertex) (.substitution context (.snoc target (codeType carrier m))
      (extendSubstitution mapping value)) := by
  have adjusted : Derivation (Theory vertex)
      (.term context value ((codeType carrier m).substitute mapping)) := by
    exact (congrArg (Judgment.term context value)
      (codeType_substitute carrier mapping)).symm ▸ typed
  exact deriveList (.substitutionExtend context target (codeType carrier m) mapping value)
    (.cons previous (.cons formed (.cons adjusted .nil)))

def typingArguments (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (first second : TermExpr (symbols D) n)
    (firstTyped : Derivation (Theory vertex) (.term context first (codeType carrier n)))
    (secondTyped : Derivation (Theory vertex) (.term context second (codeType carrier n))) :
    Derivation (Theory vertex) (.substitution context (typingContext carrier)
      (Fin.cases first (fun _ => second))) := by
  let start := deriveList (.substitutionNil context) (.cons formed .nil)
  let firstHeader := extendFormed vertex (emptyFormed vertex) (codeFormed vertex carrier (emptyFormed vertex))
  let one := codeArgument vertex carrier start (codeFormed vertex carrier (emptyFormed vertex)) secondTyped
  let two := codeArgument vertex carrier one (codeFormed vertex carrier firstHeader) firstTyped
  have equal : extendSubstitution (extendSubstitution Fin.elim0 second) first =
      (Fin.cases first (fun _ => second) : Substitution (symbols D) 2 n) := by
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ previous => cases previous using Fin.cases with
      | zero => rfl
      | succ impossible => exact Fin.elim0 impossible
  exact (congrArg (Judgment.substitution context (typingContext carrier)) equal) ▸ two

def typingFormed (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (first second : TermExpr (symbols D) n)
    (firstTyped : Derivation (Theory vertex) (.term context first (codeType carrier n)))
    (secondTyped : Derivation (Theory vertex) (.term context second (codeType carrier n))) :
    Derivation (Theory vertex) (.type context (typingType carrier first second)) := by
  refine deriveList (.typeFamily context (.typing carrier)
    ((Fin.cases first (fun _ => second)) : Substitution (symbols D) 2 n))
    (.cons formed (.cons (typingContextFormed vertex carrier) (.cons ?_ .nil)))
  change Derivation (Theory vertex) (.substitution context (typingContext carrier)
    ((Fin.cases first (fun _ => second)) : Substitution (symbols D) 2 n))
  exact typingArguments vertex carrier formed first second firstTyped secondTyped

def sortFormed (carrier : D.Carrier) (sort : HSort) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) :
    Derivation (Theory vertex) (.term context (sortCode carrier sort n) (codeType carrier n)) := by
  have tree := deriveList (.primitive context (.sort carrier sort) Fin.elim0)
    (.cons formed (.cons (emptyFormed vertex)
      (.cons (codeFormed vertex carrier (emptyFormed vertex))
        (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil))))
  have equal : (RuleCode.primitive (D := Theory vertex) context (.sort carrier sort) Fin.elim0).conclusion =
      .term context (sortCode carrier sort n) (codeType carrier n) := by
    simp only [RuleCode.conclusion, signature, codeType_substitute, sortCode]
  exact equal ▸ tree

def codeVariable (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) :
    Derivation (Theory vertex) (.term (.snoc context (codeType carrier n)) (.var 0) (codeType carrier (n + 1))) := by
  have tree := deriveList (.variable (.snoc context (codeType carrier n)) 0)
    (.cons (extendFormed vertex formed (codeFormed vertex carrier formed)) .nil)
  have equal : (RuleCode.variable (D := Theory vertex) (.snoc context (codeType carrier n)) 0).conclusion =
      .term (.snoc context (codeType carrier n)) (.var 0) (codeType carrier (n + 1)) := by
    simp only [RuleCode.conclusion, ContextExpr.lookup_zero, codeType_rename]
  exact equal ▸ tree

def certifiedFormed (carrier : D.Carrier) (sort : HSort) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) :
    Derivation (Theory vertex) (.type context (certifiedCode carrier sort n)) :=
  let codeTree := codeFormed vertex carrier formed
  let extended := extendFormed vertex formed codeTree
  let body := typingFormed vertex carrier extended (.var 0) (sortCode carrier sort (n + 1))
    (codeVariable vertex carrier formed) (sortFormed vertex carrier sort extended)
  deriveList (.sigmaFormation context (codeType carrier n)
    (typingType carrier (.var 0) (sortCode carrier sort (n + 1)))) (.cons codeTree (.cons body .nil))

/-- A closed expression has the same weakening after any further substitution. -/
theorem closed_substitute (type : TypeExpr (symbols D) 0) {n m : Nat}
    (mapping : Substitution (symbols D) n m) :
    (type.rename (Fin.elim0 : Renaming 0 n)).substitute mapping =
      type.rename (Fin.elim0 : Renaming 0 m) := by
  rw [TypeExpr.substitute_rename, ← TypeExpr.substitute_variables]
  congr 1
  funext position
  exact Fin.elim0 position

def vectorFormed : {n : Nat} → (types : Fin n → TypeExpr (symbols D) 0) →
    (∀ position {m : Nat} {context : ContextExpr (symbols D) m},
      Derivation (Theory vertex) (.context context) →
      Derivation (Theory vertex) (.type context ((types position).rename Fin.elim0))) →
    Derivation (Theory vertex) (.context (vectorTelescope types))
  | 0, _, _ => emptyFormed vertex
  | n + 1, types, typesFormed =>
      let prior := vectorFormed (fun position : Fin n => types position.succ)
        (fun position => typesFormed position.succ)
      extendFormed vertex prior (typesFormed 0 prior)

def parametersFormed (declaration : D.Former) :
    Derivation (Theory vertex) (.context (parameterContext declaration)) :=
  vectorFormed vertex _ (by
    intro position n context formed
    exact (congrArg (Judgment.type context) (codeType_rename _ (Fin.elim0 : Renaming 0 n))).symm ▸
      codeFormed vertex _ formed)

def formationParametersFormed (declaration : D.Former) :
    Derivation (Theory vertex) (.context (formationContext vertex declaration)) :=
  vectorFormed vertex _ (by
    intro position n context formed
    exact (congrArg (Judgment.type context) (certifiedCode_rename _ _ (Fin.elim0 : Renaming 0 n))).symm ▸
      certifiedFormed vertex _ _ formed)

theorem vectorLookup {n : Nat} (types : Fin n → TypeExpr (symbols D) 0) (position : Fin n) :
    (vectorTelescope types).lookup position = (types position).rename Fin.elim0 := by
  induction n with
  | zero => exact Fin.elim0 position
  | succ n hypotheses =>
      cases position using Fin.cases with
      | zero =>
          simp only [vectorTelescope, ContextExpr.lookup_zero, TypeExpr.rename_comp]
          congr 1
          funext position
          exact Fin.elim0 position
      | succ previous =>
          simp only [vectorTelescope, ContextExpr.lookup_succ]
          rw [hypotheses (fun position => types position.succ) previous, TypeExpr.rename_comp]
          congr 1
          funext position
          exact Fin.elim0 position

def vectorVariable {n : Nat} (types : Fin n → TypeExpr (symbols D) 0)
    (formed : Derivation (Theory vertex) (.context (vectorTelescope types))) (position : Fin n) :
    Derivation (Theory vertex) (.term (vectorTelescope types) (.var position)
      ((types position).rename Fin.elim0)) := by
  exact (congrArg (Judgment.term (vectorTelescope types) (.var position))
    (vectorLookup types position)) ▸
      deriveList (.variable (vectorTelescope types) position) (.cons formed .nil)

def vectorArguments {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) :
    {m : Nat} → (types : Fin m → TypeExpr (symbols D) 0) →
    (∀ position {length : Nat} {gamma : ContextExpr (symbols D) length},
      Derivation (Theory vertex) (.context gamma) →
      Derivation (Theory vertex) (.type gamma ((types position).rename Fin.elim0))) →
    (mapping : Substitution (symbols D) m n) →
    (∀ position, Derivation (Theory vertex) (.term context (mapping position)
      ((types position).rename Fin.elim0))) →
    Derivation (Theory vertex) (.substitution context (vectorTelescope types) mapping)
  | 0, _, _, mapping, _ => by
      have equal : mapping = Fin.elim0 := by funext position; exact Fin.elim0 position
      exact (congrArg (Judgment.substitution context .nil) equal).symm ▸
        deriveList (.substitutionNil context) (.cons formed .nil)
  | m + 1, types, typesFormed, mapping, typed => by
      let tail := fun position : Fin m => mapping position.succ
      let tailTypes := fun position : Fin m => types position.succ
      let prior := vectorArguments formed tailTypes (fun position => typesFormed position.succ)
        tail (fun position => typed position.succ)
      let tailFormed := vectorFormed vertex tailTypes (fun position => typesFormed position.succ)
      have adjusted : Derivation (Theory vertex) (.term context (mapping 0)
          (((types 0).rename (Fin.elim0 : Renaming 0 m)).substitute tail)) := by
        exact (congrArg (Judgment.term context (mapping 0))
          (closed_substitute (types 0) tail)).symm ▸ typed 0
      have tree := deriveList (.substitutionExtend context (vectorTelescope tailTypes)
        ((types 0).rename Fin.elim0) tail (mapping 0))
        (.cons prior (.cons (typesFormed 0 tailFormed) (.cons adjusted .nil)))
      have equal : extendSubstitution tail (mapping 0) = mapping := by
        funext position
        cases position using Fin.cases <;> rfl
      exact (congrArg (Judgment.substitution context (vectorTelescope types)) equal) ▸ tree

def projectedCode (declaration : D.Former) (position : Fin (D.arity declaration)) :
    Derivation (Theory vertex) (.term (formationContext vertex declaration)
      (codeArguments vertex declaration position) (codeType (D.input declaration position) _)) := by
  let formed := formationParametersFormed vertex declaration
  let carrier := D.input declaration position
  let sort := inputSort D vertex declaration position
  let domain := codeFormed vertex carrier formed
  let extended := extendFormed vertex formed domain
  let body := typingFormed vertex carrier extended (.var 0) (sortCode carrier sort _)
    (codeVariable vertex carrier formed) (sortFormed vertex carrier sort extended)
  have parameter : Derivation (Theory vertex) (.term (formationContext vertex declaration) (.var position)
      (certifiedCode carrier sort _)) := by
    have read := vectorVariable vertex _ formed position
    exact (congrArg (Judgment.term (formationContext vertex declaration) (.var position))
      (certifiedCode_rename carrier sort (Fin.elim0 : Renaming 0 (D.arity declaration)))) ▸ read
  exact deriveList (.firstProjection (formationContext vertex declaration) (codeType carrier _)
    (typingType carrier (.var 0) (sortCode carrier sort _)) (.var position))
    (.cons domain (.cons body (.cons parameter .nil)))

def formerResultFormed (declaration : D.Former) :
    Derivation (Theory vertex) (.type (parameterContext declaration)
      (codeType (D.output declaration) _)) :=
  codeFormed vertex _ (parametersFormed vertex declaration)

def formedCodeFormed (declaration : D.Former) :
    Derivation (Theory vertex) (.term (formationContext vertex declaration)
      (formedCode vertex declaration) (codeType (D.output declaration) _)) := by
  let formed := formationParametersFormed vertex declaration
  let arguments := vectorArguments vertex formed
    (fun position => codeType (D.input declaration position) 0)
    (by intro position n context tree; exact
      (congrArg (Judgment.type context) (codeType_rename _ (Fin.elim0 : Renaming 0 n))).symm ▸
        codeFormed vertex _ tree)
    (codeArguments vertex declaration)
    (fun position => (congrArg (Judgment.term (formationContext vertex declaration)
      (codeArguments vertex declaration position))
        (codeType_rename _ (Fin.elim0 : Renaming 0 (D.arity declaration)))).symm ▸
          projectedCode vertex declaration position)
  have tree := deriveList (.primitive (formationContext vertex declaration) (.former declaration)
    (codeArguments vertex declaration))
    (.cons formed (.cons (parametersFormed vertex declaration)
      (.cons (formerResultFormed vertex declaration) (.cons arguments .nil))))
  have equal : (RuleCode.primitive (D := Theory vertex) (formationContext vertex declaration)
      (.former declaration) (codeArguments vertex declaration)).conclusion =
      .term (formationContext vertex declaration) (formedCode vertex declaration)
        (codeType (D.output declaration) (D.arity declaration)) := by
    simp only [RuleCode.conclusion, signature, codeType_substitute, formedCode]
  exact equal ▸ tree

def formationResultFormed (declaration : D.Former) :
    Derivation (Theory vertex) (.type (formationContext vertex declaration)
      (formationResult vertex declaration)) :=
  typingFormed vertex (D.output declaration) (formationParametersFormed vertex declaration)
    (formedCode vertex declaration) (sortCode (D.output declaration) (outputSort D vertex declaration) _)
    (formedCodeFormed vertex declaration)
    (sortFormed vertex _ _ (formationParametersFormed vertex declaration))


end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations
