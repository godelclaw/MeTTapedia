import Mettapedia.Logic.HostingStyles.StoredPrograms.NormalForms

/-!
# Firing a rule of a table

Small tools for the tables that compute primitives: the truth values as
data (`truth`), an assignment written as a list (`assign`), one step by a
named rule (`fires`), and what the instance of a reading is
(`inst_numbered`, `inst_unary`, `inst_truth`).

Tables are joined by appending their rule lists.  A theory that holds the
rules of a list holds those of each part (`Holds`), and a primitive realized
by a part is realized by the whole.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Host boolean natural)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)

/-! ## Truth values -/

/-- **A truth value as a datum**: the symbol `True` or `False`. -/
def truth (N : Spelling) (value : Bool) : LF.Term :=
  tag "sym" (N.write (if value then "True" else "False"))

theorem datum_boolean_eq_truth (N : Spelling) (value : Bool) :
    datum N (boolean value) = truth N value :=
  datum_boolean N value

theorem passive_truth (N : Spelling) (value : Bool) : passive (truth N value) = true :=
  passive_tag (N.quiet _)

theorem inst_truth (N : Spelling) (assignment : Nat → LF.Term) (value : Bool) :
    inst assignment (truth N value) = truth N value :=
  inst_passive assignment (passive_truth N value)

/-- **Negative**: the two truth values are apart, when the spelling
identifies no two names. -/
theorem truth_injective {N : Spelling} (injective : Function.Injective N.write) :
    Function.Injective (truth N) := by
  intro first second same
  have names := injective (tag_injective same).2
  cases first <;> cases second <;> first | rfl | (revert names; decide)

/-! ## Instances of readings -/

theorem inst_unary (assignment : Nat → LF.Term) (count : Nat) :
    inst assignment (unary count) = unary count :=
  inst_passive assignment (passive_unary count)

theorem inst_numbered (assignment : Nat → LF.Term) (value mark : LF.Term) :
    inst assignment (numbered value mark) =
      numbered (inst assignment value) (inst assignment mark) := rfl

theorem inst_numeral (assignment : Nat → LF.Term) (value : Nat) :
    inst assignment (numeral value) = numeral value :=
  inst_passive assignment (passive_numeral value)

/-! ## One step by a named rule -/

/-- **An assignment written as a list**: the pattern variable at a position is
the term at that position. -/
def assign (values : List LF.Term) : Nat → LF.Term :=
  fun index => values.getD index (.con "unbound")

/-- **A rule of the theory fires**: the instance of its left side reduces to
the instance of its right side. -/
theorem fires {theory : Theory} {rule : RewriteRule} (member : theory.rule rule)
    (values : List LF.Term) {source target : LF.Term}
    (left : inst (assign values) rule.lhs = source)
    (right : inst (assign values) rule.rhs = target) : Reduces theory source target :=
  .single (step_of_rule member _ left right)

/-- Compute the instance of a reading under an assignment written as a
list. -/
macro "instances" : tactic =>
  `(tactic| simp only [inst_callTerm, inst_libTerm, inst_tag, inst_cells, inst_numbered, inst_truth,
    inst_unary, inst_numeral, inst_write, inst_literal, inst_datum, Dedukti.inst_var,
    Dedukti.inst_app, Dedukti.inst_con, List.map_cons, List.map_nil, assign, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil])

/-! ## Parts of a table -/

/-- **A theory holds a list of rules.** -/
def Holds (theory : Theory) (rules : List RewriteRule) : Prop := ∀ rule ∈ rules, theory.rule rule

theorem Holds.left {theory : Theory} {first second : List RewriteRule}
    (holds : Holds theory (first ++ second)) : Holds theory first :=
  fun rule member => holds rule (List.mem_append_left _ member)

theorem Holds.right {theory : Theory} {first second : List RewriteRule}
    (holds : Holds theory (first ++ second)) : Holds theory second :=
  fun rule member => holds rule (List.mem_append_right _ member)

/-- The theory of a table holds the table. -/
theorem holds_programTheory (rules : List RewriteRule) : Holds (programTheory rules) rules :=
  fun _ member => member

/-- Primitives realized one list after another are realized together. -/
theorem RealizesPrimitives.append {N : Spelling} {theory : Theory} {host : Host}
    {first second : List String} (left : RealizesPrimitives N theory host first)
    (right : RealizesPrimitives N theory host second) :
    RealizesPrimitives N theory host (first ++ second) := by
  intro head member
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact left head inFirst
  · exact right head inSecond

/-- Primitives realized for one host are realized for a host that returns the
same on them. -/
theorem RealizesPrimitives.of_agrees {N : Spelling} {theory : Theory} {host reference : Host}
    {primitives : List String}
    (agrees : ∀ head ∈ primitives, ∀ arguments,
      host.primitive head arguments = reference.primitive head arguments)
    (realizes : RealizesPrimitives N theory reference primitives) :
    RealizesPrimitives N theory host primitives :=
  fun head member arguments result returned =>
    realizes head member arguments result (agrees head member arguments ▸ returned)

#print axioms truth_injective
#print axioms fires
#print axioms RealizesPrimitives.append
#print axioms RealizesPrimitives.of_agrees

end Mettapedia.Logic.HostingStyles.StoredPrograms
