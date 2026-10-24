import Mettapedia.Algebra.Order.Infinitesimal.LevelSeries

/-!
# Transformations that carry their justification

A rewriting step on a numeric expression is only sound under conditions, and
the conditions are numeric facts.  Dividing through by a term is exact — but
only if that term is nonzero, and in Lean division by zero is silently `0`, so
an unjustified step does not fail loudly: it quietly returns the wrong answer.

`Justified.Step` records a value-preserving transformation. Division changes
the value instead: `DivisionResult` retains the quotient, a nonzero-divisor
proof, and the equation reconstructing the original input. Its reconstruction
is a value-preserving step; composition retains the assumption annotations.

* `normalize` is justified by `toHahn_norm` and assumes nothing.
* `divideByTerm` is justified only when the divisor's coefficient is nonzero;
  `tryDivideByTerm` is the checked entry point and returns `none` otherwise.
* `divideByZero_is_wrong` is the negative control: with a zero divisor the
  identity genuinely fails, so the hypothesis is doing work rather than
  decorating the statement.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries LevelSeries

namespace Justified

/-- A transformation together with everything needed to trust it. -/
structure Step where
  /-- What went in. -/
  input : LevelSeries
  /-- What came out. -/
  output : LevelSeries
  /-- The numeric facts the step required, recorded by name. -/
  assumptions : List String
  /-- The two denote the same number. -/
  valid : toLevelField output = toLevelField input

/-- Doing nothing is justified, and assumes nothing. -/
def id (l : LevelSeries) : Step where
  input := l
  output := l
  assumptions := []
  valid := rfl

/-- **Canonicalisation is justified and assumption-free.** -/
def normalize (l : LevelSeries) : Step where
  input := l
  output := norm l
  assumptions := []
  valid := toLevelField_norm l

/-- **Steps compose, and their assumptions accumulate.**  A result never
loses track of what it rests on. -/
def trans (s t : Step) (h : t.input = s.output) : Step where
  input := s.input
  output := t.output
  assumptions := s.assumptions ++ t.assumptions
  valid := by rw [t.valid, h, s.valid]

theorem trans_assumptions (s t : Step) (h : t.input = s.output) :
    (trans s t h).assumptions = s.assumptions ++ t.assumptions := rfl

end Justified

/-! ## Dividing through by a term -/

/-- Divide every term by one term: subtract its level, divide by its
coefficient. -/
def divideByTerm (l : LevelSeries) (i : ℤ) (c : ℚ) : LevelSeries :=
  l.map fun t => (t.1 - i, t.2 / c)

/-- **The numeric fact the step needs.**  Multiplying the quotient back by the
divisor returns the original — provided the divisor's coefficient is nonzero.
This is where `c ≠ 0` is consumed: without it, `t.2 / c * c` is not `t.2`. -/
theorem toHahn_divideByTerm_mul {i : ℤ} {c : ℚ} (hc : c ≠ 0) :
    ∀ l : LevelSeries,
      toHahn (divideByTerm l i c) * single i c = toHahn l
  | [] => by simp [divideByTerm]
  | t :: rest => by
      simpa only [divideByTerm, List.map_cons, toHahn_cons, add_mul, single_mul_single,
        sub_add_cancel, div_mul_cancel₀ _ hc] using
        congrArg (single t.1 t.2 + ·) (toHahn_divideByTerm_mul hc rest)

/-- The same statement in the ordered field. -/
theorem toLevelField_divideByTerm_mul {i : ℤ} {c : ℚ} (hc : c ≠ 0) (l : LevelSeries) :
    toLevelField (divideByTerm l i c) * toLevelField [(i, c)] = toLevelField l := by
  simpa only [toLevelField, toHahn_cons, toHahn_nil, add_zero, toLex_mul] using
    congrArg toLex (toHahn_divideByTerm_mul hc l)

/-- Exact division is specified by reconstruction, not equality with the quotient. -/
structure DivisionResult (input : LevelSeries) (level : ℤ) (coefficient : ℚ) where
  quotient : LevelSeries
  divisor_ne_zero : coefficient ≠ 0
  reconstruct : toHahn quotient * single level coefficient = toHahn input

namespace DivisionResult

variable {input : LevelSeries} {level : ℤ} {coefficient : ℚ}

/-- Canonicalizing the quotient preserves its division certificate. -/
def normalize (result : DivisionResult input level coefficient) : DivisionResult input level coefficient :=
  { result with quotient := norm result.quotient
                reconstruct := by rw [toHahn_norm]; exact result.reconstruct }

/-- Multiplication back by the divisor is a genuine value-preserving step. -/
def reconstructionStep (result : DivisionResult input level coefficient) : Justified.Step where
  input := mul result.quotient [(level, coefficient)]
  output := input
  assumptions := ["divisor coefficient nonzero"]
  valid := congrArg toLex (by simpa only [toHahn_mul, toHahn_cons, toHahn_nil, add_zero]
    using result.reconstruct.symm)

end DivisionResult

/-- Compute a quotient and certify its reconstruction; reject a zero divisor. -/
def tryDivideByTerm (l : LevelSeries) (i : ℤ) (c : ℚ) : Option (DivisionResult l i c) :=
  if hc : c = 0 then none
  else some ⟨divideByTerm l i c, hc, toHahn_divideByTerm_mul hc l⟩

theorem tryDivideByTerm_rejects (l : LevelSeries) (i : ℤ) :
    tryDivideByTerm l i 0 = none := by
  simp [tryDivideByTerm]

theorem tryDivideByTerm_accepts {c : ℚ} (l : LevelSeries) (i : ℤ) (hc : c ≠ 0) :
    (tryDivideByTerm l i c).isSome := by
  simp [tryDivideByTerm, hc]

/-- **The negative control.**  With a zero divisor the identity is false, not
merely unproved: the left side collapses to `0` while the right side is `1`.
So the hypothesis in `toHahn_divideByTerm_mul` is load-bearing. -/
theorem divideByZero_is_wrong :
    toHahn (divideByTerm [(0, 1)] 0 0) * single (0 : ℤ) (0 : ℚ) ≠ toHahn [(0, 1)] := by
  simp [divideByTerm, toHahn, single_zero_one]

/-! ## Dividing by `Ω` is exact and stays in the representation

Finite denotations are closed under ring operations, while raw lists retain
their presentation order. Inverting `Ω - 1` needs infinitely many terms.
Division by a nonzero single term is exact and stays finite. -/

/-- Divide by `Ω`, shifting every level up by one. -/
def divideByOmega (l : LevelSeries) : LevelSeries := divideByTerm l (-1) 1

theorem divideByOmega_mul (l : LevelSeries) :
    toLevelField (divideByOmega l) * Om = toLevelField l := by
  have h := toLevelField_divideByTerm_mul (i := -1) (c := 1) one_ne_zero l
  rwa [show toLevelField [((-1 : ℤ), (1 : ℚ))] = Om from by
    simp [toLevelField, toHahn, Om]] at h

/-! ## Controls -/

namespace TransformControls

/-- `3Ω − 5 + 2Ω⁻¹` divided by `Ω` is `3 − 5Ω⁻¹ + 2Ω⁻²`. -/
theorem divide_sample :
    divideByOmega [(-1, 3), (0, -5), (1, 2)] = [(0, 3), (1, -5), (2, 2)] := by
  norm_num [divideByOmega, divideByTerm]

/-- The checked entry point refuses a zero divisor. -/
theorem reject_zero : tryDivideByTerm [(0, 1)] 0 0 = none :=
  tryDivideByTerm_rejects _ _

/-- And accepts a nonzero one. -/
theorem accept_nonzero : (tryDivideByTerm [(0, 1)] 0 2).isSome :=
  tryDivideByTerm_accepts _ _ (by norm_num)

/-- A concrete successful division certificate. -/
def checkedHalf : DivisionResult [(0, 1)] 0 2 :=
  (tryDivideByTerm [(0, 1)] 0 2).get (tryDivideByTerm_accepts _ _ (by norm_num))

theorem checked_quotient : checkedHalf.quotient = [(0, 1 / 2)] := by decide +kernel

/-- An unchanged quotient cannot certify dividing one by two. -/
theorem wrong_quotient_rejected (result : DivisionResult [(0, 1)] 0 2) : result.quotient ≠ [(0, 1)] := by
  intro wrong
  have coefficient := congrArg (fun value => value.coeff 0) result.reconstruct
  rw [wrong] at coefficient
  norm_num [toHahn, single_mul_single] at coefficient

/-- Composing a value-preserving step with canonicalisation retains its annotations. -/
theorem composed_assumptions
    (s : Justified.Step) (h : (Justified.normalize s.output).input = s.output) :
    (Justified.trans s (Justified.normalize s.output) h).assumptions
      = s.assumptions :=
  by simp [Justified.trans, Justified.normalize]

end TransformControls

end Mettapedia.Algebra.Order.Infinitesimal
