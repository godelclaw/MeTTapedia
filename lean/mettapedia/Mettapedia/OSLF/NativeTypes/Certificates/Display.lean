import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking

/-!+# Display of the shared dependent native grammar

The display traverses the actual checked syntax. Primitive names are supplied
by the installed signature; all dependent annotations, argument positions and
mixed-context assumptions remain visible.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.NativeDisplay

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u
variable {S : Symbols.{u}}

structure Names (S : Symbols.{u}) where
  type : S.TypeSymbol → String
  term : S.TermSymbol → String
  predicate : S.PredicateSymbol → String

def application (name : String) (arguments : List String) : String :=
  if arguments.isEmpty then name else name ++ "(" ++ String.intercalate ", " arguments ++ ")"

mutual

def type (names : Names S) : {n : Nat} → TypeExpr S n → String
  | _, .family symbol arguments =>
      application (names.type symbol)
        ((List.finRange (S.typeArity symbol)).map fun position => term names (arguments position))
  | _, .propositions => "Prop"
  | _, .pi domain body => "Π(" ++ type names domain ++ "). " ++ type names body
  | _, .sigma domain body => "Σ(" ++ type names domain ++ "). " ++ type names body
  | _, .comprehension domain predicate =>
      "{" ++ type names domain ++ " | " ++ proposition names predicate ++ "}"

def term (names : Names S) : {n : Nat} → TermExpr S n → String
  | _, .var index => "#" ++ toString index.val
  | _, .primitive symbol arguments =>
      application (names.term symbol)
        ((List.finRange (S.termArity symbol)).map fun position => term names (arguments position))
  | _, .lam domain codomain body =>
      application "λ" [type names domain, type names codomain, term names body]
  | _, .app domain body function argument =>
      application "apply" [type names domain, type names body, term names function, term names argument]
  | _, .pair domain body first second =>
      application "pair" [type names domain, type names body, term names first, term names second]
  | _, .fst domain body pair =>
      application "fst" [type names domain, type names body, term names pair]
  | _, .snd domain body pair =>
      application "snd" [type names domain, type names body, term names pair]
  | _, .sigmaElim domain body motive branch pair =>
      application "Σ-elim" [type names domain, type names body, type names motive,
        term names branch, term names pair]
  | _, .quote predicate => application "quote" [proposition names predicate]
  | _, .refine domain predicate value =>
      application "refine" [type names domain, proposition names predicate, term names value]
  | _, .forget domain predicate value =>
      application "forget" [type names domain, proposition names predicate, term names value]

def proposition (names : Names S) : {n : Nat} → PropExpr S n → String
  | _, .atom symbol arguments =>
      application (names.predicate symbol)
        ((List.finRange (S.predicateArity symbol)).map fun position => term names (arguments position))
  | _, .truth => "⊤"
  | _, .falsehood => "⊥"
  | _, .and first second => "(" ++ proposition names first ++ " ∧ " ++ proposition names second ++ ")"
  | _, .or first second => "(" ++ proposition names first ++ " ∨ " ++ proposition names second ++ ")"
  | _, .implies first second => "(" ++ proposition names first ++ " ⇒ " ++ proposition names second ++ ")"
  | _, .all domain predicate => "∀(" ++ type names domain ++ "). " ++ proposition names predicate
  | _, .exists domain predicate => "∃(" ++ type names domain ++ "). " ++ proposition names predicate
  | _, .holds value => application "holds" [term names value]
  | _, .image family => application "inhabited" [type names family]

end

def context (names : Names S) : {n : Nat} → ContextExpr S n → String
  | _, .nil => "[]"
  | _, .snoc previous family => context names previous ++ "; " ++ type names family
  | _, .assume previous predicate => context names previous ++ "; assume " ++ proposition names predicate

def substitution (names : Names S) {n m : Nat} (values : Substitution S m n) : String :=
  "[" ++ String.intercalate ", " ((List.finRange m).map fun position =>
    "#" ++ toString position.val ++ " := " ++ term names (values position)) ++ "]"

def judgment (names : Names S) : Judgment S → String
  | .context source => context names source ++ " context"
  | .type source family => context names source ++ " ⊢ " ++ type names family ++ " type"
  | .term source value family => context names source ++ " ⊢ " ++ term names value ++ " : " ++ type names family
  | .substitution source target values => context names source ++ " ⊢ " ++ substitution names values ++ " : " ++ context names target
  | .contextEq first second => context names first ++ " ≡ " ++ context names second ++ " context"
  | .typeEq source first second => context names source ++ " ⊢ " ++ type names first ++ " ≡ " ++ type names second ++ " type"
  | .termEq source first second family => context names source ++ " ⊢ " ++ term names first ++ " ≡ " ++ term names second ++ " : " ++ type names family
  | .substitutionEq source target first second => context names source ++ " ⊢ " ++ substitution names first ++ " ≡ " ++ substitution names second ++ " : " ++ context names target
  | .predicate source predicate => context names source ++ " ⊢ " ++ proposition names predicate ++ " proposition"
  | .entails source predicate => context names source ++ " ⊢ " ++ proposition names predicate
  | .predicateEq source first second => context names source ++ " ⊢ " ++ proposition names first ++ " ≡ " ++ proposition names second ++ " proposition"

end Mettapedia.OSLF.NativeTypes.Certificates.NativeDisplay
