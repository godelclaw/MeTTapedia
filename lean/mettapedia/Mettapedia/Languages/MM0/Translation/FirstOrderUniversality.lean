import Mettapedia.GSLT.LanguageDef.PartialRecursivePresentation
import Mettapedia.Languages.MM0.Translation.FirstOrderFragment
import Mettapedia.Languages.MM0.Kernel.FirstOrderEnumeration

/-!
# A universal MM0 theory

The presentation of partial recursive functions is admitted and compiled to
an MM0 theory without binders: three sorts, nineteen term constructors, no
definitions, and one axiom for each of its twenty-three rules. A closed
judgment of the presentation is a closed MM0 term.

MM0 derives the term of a judgment exactly when the presentation derives
the judgment, and the presentation derives it exactly when it is true. So
the MM0 checker accepts a proof that code `c` halts on `n` exactly when
`c.eval n` is defined (`mm0_checks_halts_iff`).

This fixes where MM0 lies among the decision problems. Every recursively
enumerable predicate on numbers is the set of inputs on which one code has
an accepted halting proof (`mm0_every_re_represented`). For one code these
inputs form a recursively enumerable set (`mm0_halts_re`). Whether a
halting judgment has an accepted proof is not computable
(`mm0_halts_undecidable`), and the judgments without one do not form a
recursively enumerable set (`mm0_unprovable_not_re`). Checking a supplied
proof is a terminating computation; finding one is not.

Together with the recursive enumerability of every first-order theory
(`Kernel.FirstOrderEnumeration.derives_re`) this is a characterization:
a predicate on numbers is recursively enumerable exactly when some
first-order MM0 theory derives exactly its instances along a computable
family of closed expressions (`re_iff_firstOrder_mm0`). So no such theory
derives exactly the inputs on which a code does not halt
(`nonhalting_not_representable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderUniversality

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.PartialRecursive
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules
open Nat.Partrec (Code)
open Kernel.FirstOrderEnumeration (code code_injective derives_re)

/-! ## The generated theory -/

theorem admitted : (Presentation.admit? language ["wff"] rules).isSome = true := by
  decide +kernel

/-- The admitted presentation of partial recursive functions. -/
def presentation : Presentation :=
  (Presentation.admit? language ["wff"] rules).get admitted

theorem presentation_retains :
    presentation.syntaxSignature.language = language ∧
      presentation.judgmentSorts = ["wff"] ∧ presentation.rules = rules :=
  Presentation.admit?_retains (Option.some_get admitted).symm

/-- The MM0 term of a numeral. -/
def numTerm : ℕ → Preterm
  | 0 => .term 0
  | n + 1 => Preterm.applyArgs (.term 1) [numTerm n]

/-- The MM0 term of a code. -/
def codeTerm : Code → Preterm
  | .zero => .term 2
  | .succ => .term 3
  | .left => .term 4
  | .right => .term 5
  | .pair f g => Preterm.applyArgs (.term 6) [codeTerm f, codeTerm g]
  | .comp f g => Preterm.applyArgs (.term 7) [codeTerm f, codeTerm g]
  | .prec f g => Preterm.applyArgs (.term 8) [codeTerm f, codeTerm g]
  | .rfind' f => Preterm.applyArgs (.term 9) [codeTerm f]

/-- The MM0 term of a closed judgment. -/
def judgmentTerm : Judgment → Preterm
  | .add a b c => Preterm.applyArgs (.term 10) [numTerm a, numTerm b, numTerm c]
  | .mul a b c => Preterm.applyArgs (.term 11) [numTerm a, numTerm b, numTerm c]
  | .lt a b => Preterm.applyArgs (.term 12) [numTerm a, numTerm b]
  | .le a b => Preterm.applyArgs (.term 13) [numTerm a, numTerm b]
  | .pair a b c => Preterm.applyArgs (.term 14) [numTerm a, numTerm b, numTerm c]
  | .eval c n m => Preterm.applyArgs (.term 15) [codeTerm c, numTerm n, numTerm m]
  | .prec f g a k m =>
      Preterm.applyArgs (.term 16) [codeTerm f, codeTerm g, numTerm a, numTerm k, numTerm m]
  | .search f a s j =>
      Preterm.applyArgs (.term 17) [codeTerm f, numTerm a, numTerm s, numTerm j]
  | .halts c n => Preterm.applyArgs (.term 18) [codeTerm c, numTerm n]

theorem encodes_num : ∀ n : ℕ, Encodes (constructorNames language) (num n) (numTerm n)
  | 0 => Encodes.constructor (name := "zero") (index := 0) (by decide) .nil
  | n + 1 => Encodes.constructor (name := "succ") (index := 1) (by decide)
      (.cons (encodes_num n) .nil)

theorem encodes_code :
    ∀ c : Code, Encodes (constructorNames language) (codePattern c) (codeTerm c)
  | .zero => Encodes.constructor (name := "czero") (index := 2) (by decide) .nil
  | .succ => Encodes.constructor (name := "csucc") (index := 3) (by decide) .nil
  | .left => Encodes.constructor (name := "cleft") (index := 4) (by decide) .nil
  | .right => Encodes.constructor (name := "cright") (index := 5) (by decide) .nil
  | .pair f g => Encodes.constructor (name := "cpair") (index := 6) (by decide)
      (.cons (encodes_code f) (.cons (encodes_code g) .nil))
  | .comp f g => Encodes.constructor (name := "ccomp") (index := 7) (by decide)
      (.cons (encodes_code f) (.cons (encodes_code g) .nil))
  | .prec f g => Encodes.constructor (name := "cprec") (index := 8) (by decide)
      (.cons (encodes_code f) (.cons (encodes_code g) .nil))
  | .rfind' f => Encodes.constructor (name := "crfind") (index := 9) (by decide)
      (.cons (encodes_code f) .nil)

theorem encodes_judgment : ∀ judgment : Judgment,
    Encodes (constructorNames language) judgment.pattern (judgmentTerm judgment)
  | .add a b c => Encodes.constructor (name := "add") (index := 10) (by decide)
      (.cons (encodes_num a) (.cons (encodes_num b) (.cons (encodes_num c) .nil)))
  | .mul a b c => Encodes.constructor (name := "mul") (index := 11) (by decide)
      (.cons (encodes_num a) (.cons (encodes_num b) (.cons (encodes_num c) .nil)))
  | .lt a b => Encodes.constructor (name := "lt") (index := 12) (by decide)
      (.cons (encodes_num a) (.cons (encodes_num b) .nil))
  | .le a b => Encodes.constructor (name := "le") (index := 13) (by decide)
      (.cons (encodes_num a) (.cons (encodes_num b) .nil))
  | .pair a b c => Encodes.constructor (name := "pair") (index := 14) (by decide)
      (.cons (encodes_num a) (.cons (encodes_num b) (.cons (encodes_num c) .nil)))
  | .eval c n m => Encodes.constructor (name := "eval") (index := 15) (by decide)
      (.cons (encodes_code c) (.cons (encodes_num n) (.cons (encodes_num m) .nil)))
  | .prec f g a k m => Encodes.constructor (name := "prec") (index := 16) (by decide)
      (.cons (encodes_code f) (.cons (encodes_code g) (.cons (encodes_num a)
        (.cons (encodes_num k) (.cons (encodes_num m) .nil)))))
  | .search f a s j => Encodes.constructor (name := "search") (index := 17) (by decide)
      (.cons (encodes_code f) (.cons (encodes_num a) (.cons (encodes_num s)
        (.cons (encodes_num j) .nil))))
  | .halts c n => Encodes.constructor (name := "halts") (index := 18) (by decide)
      (.cons (encodes_code c) (.cons (encodes_num n) .nil))

/-! ## MM0 derivability is truth -/

/-- **MM0 derives the term of a closed judgment exactly when the judgment
is true.** -/
theorem mm0_derives_iff (judgment : Judgment) :
    Kernel.Derives presentation.theory.termSignature presentation.theory.definitionSignature
        presentation.theory.theoremSignature [] [] (judgmentTerm judgment) ↔ judgment.Holds := by
  obtain ⟨sameLanguage, -, sameRules⟩ := presentation_retains
  have transported := Presentation.derivability_iff_of_equationFree
    (presentation := presentation) (by rw [sameLanguage]; rfl)
    (bound := []) (context := []) (hypotheses := []) (targetHypotheses := [])
    (pattern := judgment.pattern) (expression := judgmentTerm judgment)
    (by rw [Signature.sorts, sameLanguage]; exact .nil) .nil
    (by rw [Signature.names, sameLanguage]; exact encodes_judgment judgment)
  rw [sameLanguage, sameRules] at transported
  exact transported.symm.trans (derives_iff judgment)

/-- The same, for proofs the MM0 checker accepts. -/
theorem mm0_checks_iff (judgment : Judgment) :
    (∃ witness, ProofWitness.check presentation.theory.termSignature
        presentation.theory.definitionSignature presentation.theory.theoremSignature
        [] [] witness (judgmentTerm judgment) = true) ↔ judgment.Holds :=
  (Kernel.derives_iff_checked _ _ _ _ _ _).symm.trans (mm0_derives_iff judgment)

/-- The MM0 term stating that code `c` halts on `n`. -/
abbrev haltsTerm (c : Code) (n : ℕ) : Preterm := judgmentTerm (.halts c n)

/-- The checker accepts a proof that code `c` sends `n` to `m` exactly when
it does. -/
theorem mm0_checks_eval_iff (c : Code) (n m : ℕ) :
    (∃ witness, ProofWitness.check presentation.theory.termSignature
        presentation.theory.definitionSignature presentation.theory.theoremSignature
        [] [] witness (judgmentTerm (.eval c n m)) = true) ↔ m ∈ c.eval n :=
  mm0_checks_iff (.eval c n m)

/-- **The checker accepts a proof that code `c` halts on `n` exactly when it
does.** -/
theorem mm0_checks_halts_iff (c : Code) (n : ℕ) :
    (∃ witness, ProofWitness.check presentation.theory.termSignature
        presentation.theory.definitionSignature presentation.theory.theoremSignature
        [] [] witness (haltsTerm c n) = true) ↔ (c.eval n).Dom :=
  mm0_checks_iff (.halts c n)

/-! ## Where MM0 lies -/

/-- **Every recursively enumerable predicate on numbers is the set of
inputs on which one code has an accepted MM0 halting proof.** -/
theorem mm0_every_re_represented {p : ℕ → Prop} (enumerable : REPred p) :
    ∃ c : Code, ∀ n, p n ↔ ∃ witness, ProofWitness.check presentation.theory.termSignature
      presentation.theory.definitionSignature presentation.theory.theoremSignature
      [] [] witness (haltsTerm c n) = true := by
  obtain ⟨c, represents⟩ := every_re_represented enumerable
  exact ⟨c, fun n => (represents n).trans
    ((derives_halts_iff c n).trans (mm0_checks_halts_iff c n).symm)⟩

/-- For one code, the inputs with an accepted halting proof form a
recursively enumerable set. -/
theorem mm0_halts_re (c : Code) :
    REPred fun n => ∃ witness, ProofWitness.check presentation.theory.termSignature
      presentation.theory.definitionSignature presentation.theory.theoremSignature
      [] [] witness (haltsTerm c n) = true :=
  (halts_re c).of_eq fun n => (derives_halts_iff c n).trans (mm0_checks_halts_iff c n).symm

/-- **MM0 provability is undecidable**: no computable procedure decides, for
every code, whether its halting judgment at one input has an accepted
proof. -/
theorem mm0_halts_undecidable (n : ℕ) :
    ¬ ComputablePred fun c : Code => ∃ witness, ProofWitness.check
      presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature [] [] witness (haltsTerm c n) = true :=
  fun decidable => ComputablePred.halting_problem n
    (decidable.of_eq fun c => mm0_checks_halts_iff c n)

/-- The halting judgments without an accepted proof are not recursively
enumerable. -/
theorem mm0_unprovable_not_re (n : ℕ) :
    ¬ REPred fun c : Code => ¬ ∃ witness, ProofWitness.check
      presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature [] [] witness (haltsTerm c n) = true :=
  fun enumerable => ComputablePred.halting_problem_not_re n
    (enumerable.of_eq fun c => not_congr (mm0_checks_halts_iff c n))

/-! ## Where first-order MM0 lies -/

theorem code_numTerm (n : ℕ) :
    code (numTerm n) = (fun string : List ℕ => 0 :: 4 :: string)^[n] [2] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ← ih]
      rfl

theorem code_haltsTerm (c : Code) (n : ℕ) :
    code (haltsTerm c n) = (0 :: 0 :: 38 :: code (codeTerm c)) ++ code (numTerm n) := by
  simp [haltsTerm, judgmentTerm, Preterm.applyArgs, code]

theorem haltsTerm_computable (c : Code) : Computable fun n => code (haltsTerm c n) := by
  have numerals : Primrec fun n : ℕ => (fun string : List ℕ => 0 :: 4 :: string)^[n] [2] :=
    Primrec.nat_iterate Primrec.id (Primrec.const [2])
      (Primrec.list_cons.comp (Primrec.const 0)
        (Primrec.list_cons.comp (Primrec.const 4) Primrec.snd)).to₂
  refine (Primrec.list_append.comp (Primrec.const (0 :: 0 :: 38 :: code (codeTerm c)))
    numerals).to_comp.of_eq fun n => ?_
  rw [code_haltsTerm, code_numTerm]

/-- **Where first-order MM0 lies.** A predicate on numbers is recursively
enumerable exactly when some first-order MM0 theory derives exactly its
instances, along a computable family of closed expressions. -/
theorem re_iff_firstOrder_mm0 (p : ℕ → Prop) :
    REPred p ↔ ∃ (theory : Theory) (_ : theory.FirstOrder) (expression : ℕ → Preterm),
      Computable (fun n => code (expression n)) ∧
      ∀ n, p n ↔ Kernel.Derives theory.termSignature theory.definitionSignature
        theory.theoremSignature [] [] (expression n) := by
  constructor
  · intro enumerable
    obtain ⟨c, represents⟩ := every_re_represented enumerable
    obtain ⟨theory, -, firstOrder, -, -, terms, definitions, theorems⟩ :=
      FirstOrderFragment.generated_firstOrder presentation
    refine ⟨theory, firstOrder, haltsTerm c, haltsTerm_computable c, fun n => ?_⟩
    rw [terms, definitions, theorems]
    exact (represents n).trans ((derives_halts_iff c n).trans (mm0_derives_iff (.halts c n)).symm)
  · rintro ⟨theory, firstOrder, expression, computable, represents⟩
    have composed : REPred fun n => ∃ other, code other = code (expression n) ∧
        Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
          [] [] other :=
      Partrec.comp (derives_re theory firstOrder [] []) computable
    refine composed.of_eq fun n => ?_
    rw [represents n]
    exact ⟨fun ⟨other, same, derived⟩ => code_injective same ▸ derived,
      fun derived => ⟨_, rfl, derived⟩⟩

/-- **No first-order MM0 theory derives exactly the inputs on which a code
does not halt**, numbered by their codes, along any computable family of
expressions. -/
theorem nonhalting_not_representable (n : ℕ) :
    ¬ ∃ (theory : Theory) (_ : theory.FirstOrder) (expression : ℕ → Preterm),
      Computable (fun index => code (expression index)) ∧
      ∀ index, ¬ ((Denumerable.ofNat Code index).eval n).Dom ↔
        Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
          [] [] (expression index) := by
  intro representable
  have enumerable := (re_iff_firstOrder_mm0 _).mpr representable
  have encoded : REPred fun c : Code =>
      ¬ ((Denumerable.ofNat Code (Encodable.encode c)).eval n).Dom :=
    Partrec.comp enumerable Computable.encode
  have onCodes : REPred fun c : Code => ¬ (c.eval n).Dom :=
    encoded.of_eq fun c => by rw [Denumerable.ofNat_encode]
  exact ComputablePred.halting_problem_not_re n onCodes

/-! ## Controls -/

/-- The theory has nineteen term constructors, no definition and
twenty-three axioms. -/
example : presentation.theory.terms.length = 19 ∧ presentation.theory.definitions = [] ∧
    presentation.theory.theorems.length = 23 := by
  decide +kernel

/-- The checker accepts a proof that two successors send three to five. -/
example : ∃ witness, ProofWitness.check presentation.theory.termSignature
    presentation.theory.definitionSignature presentation.theory.theoremSignature [] [] witness
    (judgmentTerm (.eval (.comp .succ .succ) 3 5)) = true :=
  (mm0_checks_eval_iff _ 3 5).mpr
    (mem_eval_comp.mpr ⟨4, mem_eval_succ.mpr rfl, mem_eval_succ.mpr rfl⟩)

/-- No proof that the successor sends three to three is accepted. -/
example : ¬ ∃ witness, ProofWitness.check presentation.theory.termSignature
    presentation.theory.definitionSignature presentation.theory.theoremSignature [] [] witness
    (judgmentTerm (.eval .succ 3 3)) = true := by
  rw [mm0_checks_eval_iff, mem_eval_succ]
  omega

/-- No proof that searching for a zero of the successor halts is accepted. -/
example : ¬ ∃ witness, ProofWitness.check presentation.theory.termSignature
    presentation.theory.definitionSignature presentation.theory.theoremSignature [] [] witness
    (haltsTerm (.rfind' .succ) 0) = true := by
  rw [mm0_checks_halts_iff, Part.dom_iff_mem]
  rintro ⟨m, value⟩
  obtain ⟨j, -, zero, -⟩ := mem_eval_rfind.mp value
  rw [mem_eval_succ] at zero
  omega

end Mettapedia.Languages.MM0.Translation.FirstOrderUniversality
