import Mettapedia.GSLT.Logic.PropositionalResolutionAuthority
import Mettapedia.GSLT.LanguageDef.KernelCheckingClasses
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

/-!
# LRAT refutations over the native propositional clauses

The public checker from Lean's standard library checks RUP, RAT and deletion
actions. This adapter changes only the literal representation and proves
pointwise Boolean semantics preservation. It retains clause order, repeated
clauses and repeated literals.

An accepted LRAT refutation entails a derivation of the empty clause in the
independent resolution calculus. This direction uses resolution completeness;
it is not a polynomial LRAT-to-resolution compiler. The public LRAT checker
may stop at a successful empty-clause action. Acceptance certifies that
refutation, not validation of an unused suffix of the supplied array.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalLRAT

open PropositionalFormula
open Mettapedia.GSLT.LanguageDef

abbrev Proof := Array Std.Tactic.BVDecide.LRAT.IntAction

def encodeLiteral : Literal → Std.Sat.Literal Nat
  | .pos index => (index, true)
  | .neg index => (index, false)

def decodeLiteral : Std.Sat.Literal Nat → Literal
  | (index, true) => .pos index
  | (index, false) => .neg index

theorem decode_encodeLiteral (literal : Literal) :
    decodeLiteral (encodeLiteral literal) = literal := by
  cases literal <;> rfl

theorem encode_decodeLiteral (literal : Std.Sat.Literal Nat) :
    encodeLiteral (decodeLiteral literal) = literal := by
  rcases literal with ⟨index, polarity⟩
  cases polarity <;> rfl

def encodeClause (clause : Clause) : Std.Sat.CNF.Clause Nat := clause.map encodeLiteral

def encode (formula : CNF) : Std.Sat.CNF Nat := ⟨(formula.map encodeClause).toArray⟩

theorem encodeClause_length (clause : Clause) : (encodeClause clause).length = clause.length := by
  simp [encodeClause]

theorem encode_size (formula : CNF) : (encode formula).clauses.size = formula.length := by
  simp [encode]

theorem literal_semantics (valuation : Nat → Bool) (literal : Literal) :
    (valuation (encodeLiteral literal).1 == (encodeLiteral literal).2) =
      Literal.sat valuation literal := by
  cases literal <;> simp [encodeLiteral, Literal.sat]

theorem clause_semantics (valuation : Nat → Bool) (clause : Clause) :
    Std.Sat.CNF.Clause.eval valuation (encodeClause clause) = Clause.sat valuation clause := by
  simp only [Std.Sat.CNF.Clause.eval, encodeClause, List.any_map, Clause.sat]
  congr 1
  funext literal
  exact literal_semantics valuation literal

theorem formula_semantics (valuation : Nat → Bool) (formula : CNF) :
    Std.Sat.CNF.eval valuation (encode formula) = CNF.sat valuation formula := by
  simp [Std.Sat.CNF.eval, encode, CNF.sat, List.all_map, Function.comp_def, clause_semantics]

theorem unsat_iff (formula : CNF) :
    (encode formula).Unsat ↔ PropositionalResolution.Unsat formula := by
  simp only [Std.Sat.CNF.Unsat, PropositionalResolution.Unsat, formula_semantics]

/-- Native clause syntax is retained at the request boundary. -/
def checker : KernelAuthority.Checker CNF Proof where
  check formula proof := Std.Tactic.BVDecide.LRAT.check proof (encode formula)

theorem check_sound (formula : CNF) (proof : Proof)
    (accepted : checker.check formula proof = true) : PropositionalResolution.Unsat formula :=
  (unsat_iff formula).mp (Std.Tactic.BVDecide.LRAT.check_sound proof (encode formula) accepted)

theorem accepted_empty_derivable (formula : CNF) (proof : Proof)
    (accepted : checker.check formula proof = true) :
    Mettapedia.Logic.Derives (PropositionalResolution.ResRule formula) [] :=
  (PropositionalResolution.empty_iff_unsat formula).mpr (check_sound formula proof accepted)

/-- The submitted producer can be an ATP, a parser, a tactic or a repair
procedure. Its result is rechecked independently before publication. -/
def reconstruct {Output : Type} (propose : CNF → Output → Option Proof)
    (formula : CNF) (output : Output) : Option Proof :=
  checker.reconstruct propose formula output

theorem reconstruct_sound {Output : Type} (propose : CNF → Output → Option Proof)
    {formula : CNF} {output : Output} {proof : Proof}
    (published : reconstruct propose formula output = some proof) :
    PropositionalResolution.Unsat formula :=
  KernelAuthority.Checker.reconstruct_sound checker propose check_sound published

/-- Text LRAT uses the existing parser's arbitrary-precision identifiers.
The bytes are untrusted input: parsing alone never publishes evidence. -/
def parseText (bytes : ByteArray) : Option Proof :=
  (Std.Tactic.BVDecide.LRAT.Parser.Text.parseActions.run bytes).toOption

def reconstructText (formula : CNF) (bytes : ByteArray) : Option Proof :=
  reconstruct (fun _ => parseText) formula bytes

theorem reconstructText_sound {formula : CNF} {bytes : ByteArray} {proof : Proof}
    (published : reconstructText formula bytes = some proof) :
    PropositionalResolution.Unsat formula := reconstruct_sound _ published

def checkText (formula : CNF) (bytes : ByteArray) : Bool := (reconstructText formula bytes).isSome

namespace Controls

def clashProof : Proof := #[.addEmpty 3 #[1, 2]]

def ratFormula : CNF := [[.pos 1], [.neg 1], [.pos 0, .pos 1]]

def ratProof : Proof :=
  #[.addRat 4 #[1] (1, true) #[] #[], .addEmpty 5 #[1, 2]]

def xorFormula : CNF :=
  [[.pos 0, .pos 1], [.neg 0, .pos 1], [.pos 0, .neg 1], [.neg 0, .neg 1]]

def xorProof : Proof := #[.addRup 5 #[2] #[1, 2], .addEmpty 6 #[5, 3, 4]]

theorem unknown_hint_refused :
    checker.check PropositionalResolution.clash #[.addEmpty 3 #[17]] = false := by decide +kernel

/-- Executable controls use the real standard-library checker, whose hash
tables depend on the host word width. These are runtime tests, separate from
the width-independent soundness theorems above. -/
def verdicts : List (String × Bool) :=
  [("complementary units", checker.check PropositionalResolution.clash clashProof),
   ("nonempty RUP addition", checker.check xorFormula xorProof),
   ("RAT addition", checker.check ratFormula ratProof),
   ("deletion of an unused clause", checker.check ratFormula #[.del #[3], .addEmpty 4 #[1, 2]]),
   ("cached initial units", checker.check PropositionalResolution.clash #[.addEmpty 3 #[1]]),
   ("missing hint", !(checker.check xorFormula #[.addEmpty 5 #[1]])),
   ("unknown hint", !(checker.check PropositionalResolution.clash #[.addEmpty 3 #[17]])),
   ("deleted premise", !(checker.check PropositionalResolution.clash
      #[.del #[1], .addEmpty 3 #[1, 2]])),
   ("satisfiable premise", !(checker.check [[.pos 0]] clashProof)),
   ("text LRAT reconstruction", checkText PropositionalResolution.clash "3 0 1 2 0\n".toUTF8),
   ("text LRAT missing hint", !(checkText xorFormula "5 0 1 0\n".toUTF8)),
   ("text LRAT trailing garbage", !(checkText PropositionalResolution.clash "3 0 1 2 0\ngarbage\n".toUTF8))]

theorem satisfiable_formula_refused (proof : Proof) :
    checker.check [[.pos 0]] proof = false := by
  cases accepted : checker.check [[.pos 0]] proof with
  | false => rfl
  | true =>
      have impossible := check_sound _ proof accepted (fun _ => true)
      simp [CNF.sat, Clause.sat, Literal.sat] at impossible

theorem empty_formula_refused (proof : Proof) : checker.check [] proof = false := by
  cases accepted : checker.check [] proof with
  | false => rfl
  | true => exact (PropositionalResolution.not_unsat_nil (check_sound [] proof accepted)).elim

theorem repetition_preserved :
    (encode [[.pos 0, .pos 0], [.pos 0, .pos 0]]).clauses =
      #[[(0, true), (0, true)], [(0, true), (0, true)]] := rfl

end Controls
end Mettapedia.GSLT.Logic.PropositionalLRAT
