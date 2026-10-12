import Mettapedia.Languages.MM0.Kernel.Typing

/-!
# Term symbols of an expression

Typing an expression reads the declarations of the term symbols that occur
in it, and no others. So a typing derivation over one signature is a typing
derivation over every signature that has the same declarations for those
symbols. This is the step from "typed in the finished theory" to "typed in
the theory as it stood when the declaration was admitted".
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

namespace Preterm

/-- Every term symbol of the expression satisfies the predicate. -/
def SymbolsWithin (allowed : Nat → Prop) : Preterm → Prop
  | .var _ => True
  | .term index => allowed index
  | .app function argument => SymbolsWithin allowed function ∧ SymbolsWithin allowed argument

theorem SymbolsWithin.mono {narrow broad : Nat → Prop}
    (includes : ∀ index, narrow index → broad index) {expression : Preterm}
    (within : SymbolsWithin narrow expression) : SymbolsWithin broad expression := by
  induction expression with
  | var _ => trivial
  | term index => exact includes index within
  | app function argument functionHypothesis argumentHypothesis =>
      exact ⟨functionHypothesis within.1, argumentHypothesis within.2⟩

theorem symbolsWithin_applyArgs (allowed : Nat → Prop) (function : Preterm)
    (arguments : List Preterm) :
    SymbolsWithin allowed (applyArgs function arguments) ↔
      SymbolsWithin allowed function ∧
        ∀ argument ∈ arguments, SymbolsWithin allowed argument := by
  induction arguments generalizing function with
  | nil => simp
  | cons argument arguments inductionHypothesis =>
      rw [applyArgs, inductionHypothesis]
      simp only [SymbolsWithin, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- Typing reads only the declarations of the symbols that occur. -/
theorem HasType.restrictSignature {large small : TermSignature} {allowed : Nat → Prop}
    (agrees : ∀ index, allowed index → small index = large index)
    {context remaining : Context} {expression : Preterm} {sort : Nat}
    (typed : HasType large context expression remaining sort)
    (within : SymbolsWithin allowed expression) :
    HasType small context expression remaining sort := by
  induction typed with
  | var known => exact .var known
  | term known => exact .term ((agrees _ within).trans known)
  | bound _ known inductionHypothesis => exact .bound (inductionHypothesis within.1) known
  | regular _ _ functionHypothesis argumentHypothesis =>
      exact .regular (functionHypothesis within.1) (argumentHypothesis within.2)

example : SymbolsWithin (· = 3) (.app (.term 3) (.var 0)) := ⟨rfl, trivial⟩

example : ¬ SymbolsWithin (· = 3) (.app (.term 4) (.var 0)) := by
  rintro ⟨impossible, -⟩
  cases impossible

end Preterm

end Mettapedia.Languages.MM0.Kernel
