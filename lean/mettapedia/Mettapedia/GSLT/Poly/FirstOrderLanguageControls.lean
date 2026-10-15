import Mettapedia.GSLT.Poly.FirstOrderLanguage

/-!
# Controls for first-order languages as indexed polynomials

Positive: in the language `Z : Nat`, `S : Nat → Nat`, the numeral two prints as the
pattern `S (S Z)`, both hypotheses of the equivalence hold, and the pattern is typed
by the language's own judgment.

Negative, binders: in a lambda-calculus language the identity `Lam (λ. #0)` is a
closed object pattern typed at `Term`, but no closed term of the first-order fragment
prints to it. Binders are outside this polynomial.

Negative, labels: when two constructors share a label, two terms at different sorts
print to the same pattern, so printing is not injective on terms of all sorts. The
distinct-labels hypothesis of the equivalence is needed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.FirstOrderLanguageControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.GSLT.Poly.FirstOrderLanguage

/-! ## Positive: numerals -/

def zeroRule : GrammarRule :=
  { label := "Z", category := "Nat", params := [], syntaxPattern := [] }

def succRule : GrammarRule :=
  { label := "S", category := "Nat", params := [.simple "n" (.base "Nat")], syntaxPattern := [] }

def peanoLanguage : LanguageDef :=
  { name := "Peano", types := [{ name := "Nat" }], terms := [zeroRule, succRule],
    equations := [], rewrites := [] }

theorem peano_firstOrder : ∀ rule ∈ peanoLanguage.terms, FirstOrderRule rule := by
  intro rule member
  simp only [peanoLanguage, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [FirstOrderRule, zeroRule, succRule, baseSort?]

theorem peano_labels : (peanoLanguage.terms.map (·.label)).Nodup := by
  simp [peanoLanguage, zeroRule, succRule]

def zeroConstructor : (signature peanoLanguage).Constructor :=
  ⟨zeroRule, by simp [peanoLanguage], peano_firstOrder _ (by simp [peanoLanguage])⟩

def succConstructor : (signature peanoLanguage).Constructor :=
  ⟨succRule, by simp [peanoLanguage], peano_firstOrder _ (by simp [peanoLanguage])⟩

def zero : Term (signature peanoLanguage) "Nat" :=
  @Term.node (signature peanoLanguage) zeroConstructor (fun position => Fin.elim0 position)

def succ (term : Term (signature peanoLanguage) "Nat") : Term (signature peanoLanguage) "Nat" :=
  @Term.node (signature peanoLanguage) succConstructor fun
    | ⟨0, _⟩ => term
    | ⟨_ + 1, outside⟩ => by simp [succConstructor, succRule] at outside

theorem two_pattern : toPattern (succ (succ zero)) =
    .apply "S" [.apply "S" [.apply "Z" []]] := rfl

example : HasType peanoLanguage FreeTypeContext.empty []
    (.apply "S" [.apply "S" [.apply "Z" []]]) (.base "Nat") :=
  two_pattern ▸ toPattern_hasType (succ (succ zero))

/-- The closed `Nat` patterns of the language are the polynomial's free-monad trees. -/
noncomputable example :
    {pattern : Pattern // HasType peanoLanguage FreeTypeContext.empty [] pattern (.base "Nat") ∧
        isObjectPattern pattern = true} ≃
      SortedSignature.ClosedFree (signature peanoLanguage) "Nat" :=
  closedPatternFreeEquiv peano_firstOrder peano_labels "Nat"

/-! ## Negative: a binder is outside the first-order fragment -/

def lamRule : GrammarRule :=
  { label := "Lam", category := "Term", params := [.abstraction "body" (.base "Term")],
    syntaxPattern := [] }

def appRule : GrammarRule :=
  { label := "App", category := "Term",
    params := [.simple "f" (.base "Term"), .simple "a" (.base "Term")], syntaxPattern := [] }

def lambdaLanguage : LanguageDef :=
  { name := "Lambda", types := [{ name := "Term" }], terms := [lamRule, appRule],
    equations := [], rewrites := [] }

theorem lamRule_not_firstOrder : ¬ FirstOrderRule lamRule := by
  intro firstOrder
  have isBase := firstOrder _ (List.mem_singleton_self _)
  simp [baseSort?] at isBase

def identityPattern : Pattern := .apply "Lam" [.lambda none (.bvar 0)]

theorem identity_typed :
    HasType lambdaLanguage FreeTypeContext.empty [] identityPattern (.base "Term") := by
  refine HasType.constructor (rule := lamRule) (by simp [lambdaLanguage]) ?_ ?_
  · rintro ⟨_, _, _, shape⟩
    simp [lamRule] at shape
  · refine ArgumentsHaveTypes.cons trivial rfl ?_ ArgumentsHaveTypes.nil
    exact HasType.lambda (HasType.bvar rfl)

theorem identity_isObjectPattern : isObjectPattern identityPattern = true := rfl

theorem identity_not_printed :
    {sort : String} → (term : Term (signature lambdaLanguage) sort) →
      toPattern term ≠ identityPattern
  | _, .node rule _, printed => by
      simp only [toPattern, identityPattern, Pattern.apply.injEq] at printed
      obtain ⟨declared, member, firstOrder⟩ := rule
      simp only [lambdaLanguage, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact lamRule_not_firstOrder firstOrder
      · simp [appRule] at printed

/-! ## Negative: a shared label breaks injectivity across sorts -/

def labelAtA : GrammarRule := { label := "C", category := "A", params := [], syntaxPattern := [] }

def labelAtB : GrammarRule := { label := "C", category := "B", params := [], syntaxPattern := [] }

def clashLanguage : LanguageDef :=
  { name := "Clash", types := [{ name := "A" }, { name := "B" }], terms := [labelAtA, labelAtB],
    equations := [], rewrites := [] }

theorem clash_labels_not_distinct : ¬ (clashLanguage.terms.map (·.label)).Nodup := by
  simp [clashLanguage, labelAtA, labelAtB]

def termAtA : Term (signature clashLanguage) "A" :=
  @Term.node (signature clashLanguage)
    ⟨labelAtA, by simp [clashLanguage], by simp [FirstOrderRule, labelAtA]⟩
    (fun position => Fin.elim0 position)

def termAtB : Term (signature clashLanguage) "B" :=
  @Term.node (signature clashLanguage)
    ⟨labelAtB, by simp [clashLanguage], by simp [FirstOrderRule, labelAtB]⟩
    (fun position => Fin.elim0 position)

theorem clash_same_pattern : toPattern termAtA = toPattern termAtB := rfl

theorem clash_terms_differ :
    (⟨"A", termAtA⟩ : Σ sort, Term (signature clashLanguage) sort) ≠ ⟨"B", termAtB⟩ := by
  intro same
  have := congrArg Sigma.fst same
  simp at this

end Mettapedia.GSLT.Poly.FirstOrderLanguageControls
