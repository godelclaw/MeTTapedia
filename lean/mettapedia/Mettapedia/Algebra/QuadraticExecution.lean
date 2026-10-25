import Mettapedia.Algebra.QuadraticPolynomialPresentation
import Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Executed multiplication of quadratic normal forms

The forward rules contract the generator square and multiply degree-one
coefficient pairs. General expression reduction uses the polynomial quotient.
Coefficient expressions use the existing readout evaluator with caller-supplied
query values. The output agrees with quadratic multiplication and the monic
polynomial remainder under the declared coefficient interpretation.
-/

set_option autoImplicit false
namespace Mettapedia.Algebra.QuadraticExecution

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.GSLT.LanguageDef.PolynomialReadoutCalculus (add mul)
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- Only the grammar is quoted here; rule schemas below retain explicit parameter contexts. -/
def signature : QuotedTheory := moduleTheory! Theory QuadraticMultiplication() {
  Types { Query; Coefficient; Quadratic; State; }
  Terms {
    KeyZero . |- : Query;
    KeySucc . previous:Query |- : Query;
    Read . query:Query |- : Coefficient;
    Zero . |- : Coefficient;
    One . |- : Coefficient;
    Sum . first:Coefficient, second:Coefficient |- : Coefficient;
    Product . first:Coefficient, second:Coefficient |- : Coefficient;
    Omega . |- : Quadratic;
    Pair . first:Coefficient, second:Coefficient |- : Quadratic;
    Multiply . a:Coefficient, b:Coefficient, first:Quadratic, second:Quadratic |- : State;
    Done . result:Quadratic |- : State;
  }
  Exports { Coefficient; Quadratic; State; }
}

def pair (x y : Pattern) : Pattern := app "Pair" [x, y]
def omega : Pattern := app "Omega" []
def request (a b first second : Pattern) : Pattern := app "Multiply" [a, b, first, second]
def done (x y : Pattern) : Pattern := app "Done" [pair x y]

def productResult (a b x y z w : Pattern) : Pattern :=
  done (add (mul x z) (mul a (mul y w)))
    (add (add (mul x w) (mul y z)) (mul b (mul y w)))

private def context (names : List String) := names.map (·, TypeExpr.base "Coefficient")

def squareRule : RewriteRule := RewriteRule.mk (bindings := none) "Square" (context ["a", "b"]) []
  (request (fv "a") (fv "b") omega omega) (done (fv "a") (fv "b"))

def multiplyRule : RewriteRule := RewriteRule.mk (bindings := none) "MultiplyPairs"
  (context ["a", "b", "x", "y", "z", "w"]) []
  (request (fv "a") (fv "b") (pair (fv "x") (fv "y")) (pair (fv "z") (fv "w")))
  (productResult (fv "a") (fv "b") (fv "x") (fv "y") (fv "z") (fv "w"))

def language : LanguageDef := { signature.toLanguageDef with «rewrites» := [squareRule, multiplyRule] }
def quoted : QuotedTheory := ofCore language signature.extension

theorem language_validates : language.validate = [] := by decide_cbv

def successors (source : Pattern) : List Pattern := rewriteAt (engineBasePremises .empty) language 1 source

macro "quadratic_rewrite" : tactic => `(tactic|
  simp [successors, rewriteAt, language, squareRule, multiplyRule, request, done, pair, omega,
    productResult, context, app, fv, add, mul, applyRuleUsing, matchPatternForRule,
    matchPatternForRuleUsing, applyBindingsForRule, applyBindingsForRuleUsing, applyRuleBindings,
    premisesUsing, matchingPresentationForRule?, substitutionPresentationForRule?, reflectiveRuleForRule?,
    matchPattern, matchArgs, mergeBindings, applyBindings,
    Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile.empty])

theorem square_exact (a b : Pattern) : successors (request a b omega omega) = [done a b] := by
  quadratic_rewrite

theorem multiply_exact (a b x y z w : Pattern) :
    successors (request a b (pair x y) (pair z w)) = [productResult a b x y z w] := by
  quadratic_rewrite

theorem done_normal (x y : Pattern) : successors (done x y) = [] := by quadratic_rewrite

/-- Query identifiers are ground unary keys; malformed coefficient syntax has no fallback. -/
def keyValid : Pattern → Bool
  | .apply "KeyZero" [] => true
  | .apply "KeySucc" [previous] => keyValid previous
  | _ => false

def coefficientValid : Pattern → Bool
  | .apply "Read" [key] => keyValid key
  | .apply "Zero" [] | .apply "One" [] => true
  | .apply "Sum" [x, y] | .apply "Product" [x, y] => coefficientValid x && coefficientValid y
  | _ => false
termination_by term => sizeOf term

def run? (source : Pattern) : Option (List Pattern) := do
  match source with
  | .apply "Multiply" [a, b, .apply "Pair" [x, y], .apply "Pair" [z, w]] =>
      if [a, b, x, y, z, w].all coefficientValid then some (successors source) else none
  | .apply "Multiply" [a, b, .apply "Omega" [], .apply "Omega" []] =>
      if coefficientValid a && coefficientValid b then some (successors source) else none
  | _ => none

theorem run_multiply_exact (a b x y z w : Pattern)
    (valid : [a, b, x, y, z, w].all coefficientValid = true) :
    run? (request a b (pair x y) (pair z w)) = some [productResult a b x y z w] := by
  simp only [run?, request, app, pair, valid, ↓reduceIte]
  exact congrArg some (multiply_exact a b x y z w)

variable {R : Type*} [CommRing R]

def coefficient (query : Pattern → R) (term : Pattern) : R :=
  (PolynomialReadoutEvaluation.run query term).value

/-- Interpretation of the computed coordinate pair. -/
def value (query : Pattern → R) (a b x y : Pattern) :
    QuadraticAlgebra R (coefficient query a) (coefficient query b) :=
  ⟨coefficient query x, coefficient query y⟩

/-- Evaluating the actual emitted coefficients gives independent quadratic multiplication. -/
theorem product_value (query : Pattern → R) (a b x y z w : Pattern) :
    value query a b (add (mul x z) (mul a (mul y w)))
      (add (add (mul x w) (mul y z)) (mul b (mul y w))) =
        value query a b x y * value query a b z w := by
  ext <;> simp only [value, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  all_goals (simp [coefficient, add, mul, app, PolynomialReadoutEvaluation.run]; ring)

/-- The square contraction realizes the equation, without enabling its reverse. -/
theorem square_value (query : Pattern → R) (a b : Pattern) :
    value query a b a b =
      (QuadraticAlgebra.omega : QuadraticAlgebra R (coefficient query a) (coefficient query b)) ^ 2 := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl

/-- The computed pair is also the monic remainder of the independent polynomial product. -/
theorem product_remainder (query : Pattern → R) (a b x y z w : Pattern) :
    let left := value query a b x y
    let right := value query a b z w
    (QuadraticPolynomialPresentation.representative left *
      QuadraticPolynomialPresentation.representative right) %ₘ
        QuadraticPolynomialPresentation.definingPolynomial (coefficient query a) (coefficient query b) =
      QuadraticPolynomialPresentation.representative (left * right) := by
  dsimp only
  rw [QuadraticPolynomialPresentation.modByMonic_eq_representative]
  congr 1
  rw [map_mul, ← QuadraticPolynomialPresentation.equivAdjoinRoot_eq_mk,
    ← QuadraticPolynomialPresentation.equivAdjoinRoot_eq_mk]
  simp

/-- The actual emitted normal form is observed through the same coefficient evaluator. -/
def resultValue? (query : Pattern → R) (a b : Pattern) : Pattern → Option (QuadraticAlgebra R
    (coefficient query a) (coefficient query b))
  | .apply "Done" [.apply "Pair" [x, y]] => some (value query a b x y)
  | _ => none

theorem executed_product_value (query : Pattern → R) (a b x y z w : Pattern) :
    (successors (request a b (pair x y) (pair z w))).map (resultValue? query a b) =
      [some (value query a b x y * value query a b z w)] := by
  rw [multiply_exact]
  simpa only [List.map_singleton, productResult, done, pair, app, resultValue?] using
    congrArg (fun result => [some result]) (product_value query a b x y z w)

/-- The portable module exports the complete authored theory, including its forward rules. -/
def envelope : ModuleFormat.Module ModuleFormat.upstreamLimits :=
  ⟨⟨"QuadraticMultiplication", [], [⟨"Multiplication", ModuleFormat.Portable.specification
    "quadratic-multiplication/1" ModuleFormat.Portable.exportsCodec quoted⟩]⟩, by decide +kernel⟩

def moduleText : String := ModuleFormat.renderText ModuleFormat.upstreamLimits envelope
def moduleBytes : ByteArray := moduleText.toUTF8

def readModule? (text : String) : Option QuotedTheory := do
  let parsed ← ModuleFormat.readText? ModuleFormat.upstreamLimits text
  match parsed.val.exports with
  | [exported] => (ModuleFormat.Portable.admitSpecification? "quadratic-multiplication/1"
      ModuleFormat.Portable.exportsCodec exported.spec).bind admit?
  | _ => none

theorem moduleText_read : ModuleFormat.readText? ModuleFormat.upstreamLimits moduleText = some envelope :=
  ModuleFormat.readText_renderText _ _

theorem quoted_admitted : admit? quoted = some quoted := by
  have valid : quoted.validate.isEmpty = true := by
    change language.validate.isEmpty = true
    rw [language_validates]; rfl
  have exports : exportsValid quoted = true := by decide_cbv
  simp only [admit?, valid, exports, Bool.and_self, ↓reduceIte]

theorem moduleTheory_read : readModule? moduleText = some quoted := by
  simp [readModule?, moduleText_read, envelope, ModuleFormat.Portable.specification_roundtrip, quoted_admitted]

set_option maxRecDepth 100000 in
theorem moduleBytes_read : ModuleFormat.Text.readBytes? moduleBytes =
    some (ModuleFormat.Value.Wire.encode (ModuleFormat.encodeRaw envelope.val)) := by
  exact ModuleFormat.Text.readBytes_renderBytes _

end Mettapedia.Algebra.QuadraticExecution
