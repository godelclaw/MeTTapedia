import Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation
import Mettapedia.Logic.WorldModel.PolynomialObservations
import Mettapedia.GSLT.LanguageDef.PolynomialReadoutCalculus

/-!
# Checked polynomial query identities preserve WM observations

The portable algebra calculus supplies symbolic polynomial equalities. Renaming
its primitive query generators into a world model's query carrier and evaluating
those polynomials gives the actual readouts. A checked equality proof therefore
permits replacement in every represented state. This does not assert that a
particular native implementation or optimizer follows that certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.WorldModel.PolynomialPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.PolynomialReadoutCalculus
open PolynomialObservations

variable {State Query Value : Type*} [CommSemiring Value] [WorldModel State Query Value]

noncomputable def readout (base : Pattern → Query) (state : State) (term : Pattern) : Value :=
  observe state (MvPolynomial.rename base (polynomial term))

@[simp] theorem readout_read (base : Pattern → Query) (state : State) (request : Pattern) :
    readout base state (read request) = (WorldModel.extract state (base request) : Value) := by
  simp [readout, PolynomialReadoutCalculus.read, app, polynomial]

/-- Symbolic equality licenses every semiring-valued WM interpretation,
including models with nonadditive or noncommutative revision. -/
theorem checked_readouts_equal (base : Pattern → Query) (state : State)
    (context : List Pattern) (first second : Pattern) (proof : RawOpenProof)
    (checked : checkOpenRaw validated context (equal first second) proof = true)
    (contextSound : ∀ premise ∈ context, meaning premise) :
    (readout base state first : Value) = readout base state second := by
  exact congrArg (fun query => observe state (MvPolynomial.rename base query) :
    PolynomialReadoutCalculus.PolynomialQuery → Value)
    (checked_polynomial_equal context first second proof checked contextSound)

/-- The interpretation also commutes with the existing general observation
maps when their value map is a semiring homomorphism. -/
theorem readout_naturality {Target Request Result : Type*} [CommSemiring Result]
    [WorldModel Target Request Result]
    (map : ObservationMap State Query Value Target Request Result)
    (hom : Value →+* Result) (compatible : map.value = hom)
    (base : Pattern → Query) (state : State) (term : Pattern) :
    readout (map.query ∘ base) (map.state state) term = hom (readout base state term) := by
  let := PolynomialObservations.model (State := State) (Query := Query) (Value := Value)
  let := PolynomialObservations.model (State := Target) (Query := Request) (Value := Result)
  have law := (lift map hom compatible).observe state (MvPolynomial.rename base (polynomial term))
  change observe (map.state state)
    (MvPolynomial.rename map.query (MvPolynomial.rename base (polynomial term))) =
      hom (observe state (MvPolynomial.rename base (polynomial term))) at law
  simpa only [MvPolynomial.rename_rename, readout] using law

/-- The declared evaluator computes the WM readout independently described
by polynomial evaluation. -/
theorem run_value_eq_readout (base : Pattern → Query) (state : State) (term : Pattern) :
    (PolynomialReadoutEvaluation.run (fun request => WorldModel.extract state (base request) :
      Pattern → Value) term).value = readout base state term := by
  rw [PolynomialReadoutEvaluation.run_value]
  simp only [readout, PolynomialObservations.observe, MvPolynomial.eval₂_rename]
  rfl

namespace Controls

def a : Pattern := read (app "a" [])
def b : Pattern := read (app "b" [])
def c : Pattern := read (app "c" [])
def source : Pattern := mul a (add b c)
def intermediate : Pattern := add (mul a b) (mul a c)
def target : Pattern := add (mul b a) (mul c a)

def distribution : RawOpenProof := .node ⟨⟨"distribute"⟩, [a, b, c]⟩ []
def commuteFirst : RawOpenProof := .node ⟨⟨"product-comm"⟩, [a, b]⟩ []
def commuteSecond : RawOpenProof := .node ⟨⟨"product-comm"⟩, [a, c]⟩ []
def commuteSum : RawOpenProof :=
  .node ⟨⟨"sum-congr"⟩, [mul a b, mul b a, mul a c, mul c a]⟩ [commuteFirst, commuteSecond]
def compositeProof : RawOpenProof :=
  .node ⟨⟨"trans"⟩, [source, intermediate, target]⟩ [distribution, commuteSum]

theorem composite_proof_checks :
    checkOpenRaw validated [] (equal source target) compositeProof = true := by decide +kernel

theorem replacement_preserves_every_readout (base : Pattern → Query) (state : State) :
    (readout base state source : Value) = readout base state target :=
  checked_readouts_equal base state [] source target compositeProof composite_proof_checks
    (by simp)

local instance : WorldModel (Fin 3 → ℕ) (Fin 3) ℕ where
  revise := (· + ·)
  empty := 0
  extract state query := state query

def base (query : Pattern) : Fin 3 :=
  if query = app "a" [] then 0 else if query = app "b" [] then 1 else 2

def state : Fin 3 → ℕ := ![2, 3, 5]

theorem concrete_readouts :
    readout base state source = (16 : ℕ) ∧ readout base state target = (16 : ℕ) := by
  norm_num [readout, source, target, a, b, c, mul, add, PolynomialReadoutCalculus.read, app, polynomial,
    PolynomialObservations.observe, MvPolynomial.eval₂_rename,
    WorldModel.extract, base, state]
  simp only [String.reduceEq, ↓reduceIte, Matrix.cons_val]
  norm_num

def invalidIdempotence : RawOpenProof := .node ⟨⟨"product-idempotent"⟩, [a]⟩ []

theorem unjustified_idempotence_does_not_check :
    checkOpenRaw validated [] (equal (mul a a) a) invalidIdempotence = false := by decide +kernel

theorem idempotence_changes_readout :
    readout base state (mul a a) ≠ (readout base state a : ℕ) := by
  norm_num [readout, a, mul, PolynomialReadoutCalculus.read, app, polynomial, PolynomialObservations.observe,
    MvPolynomial.eval₂_rename, WorldModel.extract, base, state]

open Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation

/-- Factoring has one multiplication and three primitive query occurrences
in the declared evaluator. This is an operation account, not a runtime cost. -/
theorem source_profile (query : Pattern → Value) :
    (run query source).profile = ⟨[app "a" [], app "b" [], app "c" []], 1, 1⟩ := by
  simp [run, source, a, b, c, PolynomialReadoutCalculus.read, mul, add, app]

theorem target_profile (query : Pattern → Value) :
    (run query target).profile = ⟨[app "b" [], app "a" [], app "c" [], app "a" []], 1, 2⟩ := by
  simp [run, target, a, b, c, PolynomialReadoutCalculus.read, mul, add, app]

/-- Request occurrences and arithmetic counts cannot be recovered from the
extensional polynomial alone. Answer-preserving replacement therefore does
not automatically preserve an observer of the evaluator's full account. -/
theorem operation_account_does_not_factor_through_polynomial (query : Pattern → Value) :
    ¬ ∃ account : PolynomialReadoutCalculus.PolynomialQuery → Profile,
      ∀ term, account (polynomial term) = (run query term).profile := by
  rintro ⟨account, correct⟩
  have samePolynomial := checked_polynomial_equal [] source target compositeProof
    composite_proof_checks (by simp)
  have sameProfile := (correct source).symm.trans
    ((congrArg account samePolynomial).trans (correct target))
  rw [source_profile, target_profile] at sameProfile
  have sameLength := congrArg (fun profile => profile.requests.length) sameProfile
  norm_num at sameLength

end Controls

end Mettapedia.Logic.WorldModel.PolynomialPresentation
