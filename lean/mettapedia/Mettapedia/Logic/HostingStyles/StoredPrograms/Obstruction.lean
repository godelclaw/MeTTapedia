import Mettapedia.Logic.HostingStyles.StoredPrograms.Firing
import Mathlib.Data.Fintype.EquivFin

/-!
# Why the equality of data needs a finite alphabet

With a name written as one constant, **no finite table decides the equality
of two symbols** (`no_table_decides_constants`): for every list of rules, it
is not the case that the call of `nik:data-eq` on two symbols reduces to
`False` exactly when the two names differ.

The reason is that a table mentions finitely many constants, and reduction
does not see the others.  A renaming of constants that leaves the constants
of the rules alone carries a step to a step (`Step.rename`).  Take two names
that no rule mentions, and rename the second to the first: the call on two
different names, which should reduce to `False`, becomes the call on one name
twice, which should not.

So data are compared with their names written in a finite alphabet
(`letterSpelling`, `Comparison.lean`).  For what a program does not compare,
a name may stay a constant: the lookup and the instance of a theorem are run
with names as constants.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule RootStep Step Reduces inst instantiate)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)

/-- **A term with its constants renamed.** -/
def renameConstants (naming : String → String) : LF.Term → LF.Term
  | .con name => .con (naming name)
  | .var index => .var index
  | .srt sort => .srt sort
  | .pi domain body => .pi (renameConstants naming domain) (renameConstants naming body)
  | .lam domain body => .lam (renameConstants naming domain) (renameConstants naming body)
  | .app function argument =>
      .app (renameConstants naming function) (renameConstants naming argument)

/-- The constants of a term. -/
def constantsOf : LF.Term → List String
  | .con name => [name]
  | .var _ => []
  | .srt _ => []
  | .pi domain body => constantsOf domain ++ constantsOf body
  | .lam domain body => constantsOf domain ++ constantsOf body
  | .app function argument => constantsOf function ++ constantsOf argument

/-- A renaming that fixes the constants of a term fixes the term. -/
theorem renameConstants_of_fixed (naming : String → String) :
    ∀ term : LF.Term, (∀ name ∈ constantsOf term, naming name = name) →
      renameConstants naming term = term := by
  intro term
  induction term with
  | con name => intro fixed; simp [renameConstants, fixed name (by simp [constantsOf])]
  | var index => intro _; rfl
  | srt sort => intro _; rfl
  | pi domain body ihDomain ihBody =>
      intro fixed
      simp only [constantsOf, List.mem_append] at fixed
      simp [renameConstants, ihDomain fun name member => fixed name (.inl member),
        ihBody fun name member => fixed name (.inr member)]
  | lam domain body ihDomain ihBody =>
      intro fixed
      simp only [constantsOf, List.mem_append] at fixed
      simp [renameConstants, ihDomain fun name member => fixed name (.inl member),
        ihBody fun name member => fixed name (.inr member)]
  | app function argument ihFunction ihArgument =>
      intro fixed
      simp only [constantsOf, List.mem_append] at fixed
      simp [renameConstants, ihFunction fun name member => fixed name (.inl member),
        ihArgument fun name member => fixed name (.inr member)]

theorem renameConstants_lift (naming : String → String) (term : LF.Term) :
    ∀ amount cutoff : Nat,
      renameConstants naming (lift amount cutoff term) =
        lift amount cutoff (renameConstants naming term) := by
  induction term with
  | con name => intro _ _; rfl
  | var index => intro _ _; rfl
  | srt sort => intro _ _; rfl
  | pi domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, renameConstants, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, renameConstants, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff; simp [lift, renameConstants, ihFunction, ihArgument]

theorem renameConstants_subst (naming : String → String) (term : LF.Term) :
    ∀ (position : Nat) (replacement : LF.Term),
      renameConstants naming (subst position replacement term) =
        subst position (renameConstants naming replacement) (renameConstants naming term) := by
  induction term with
  | con name => intro _ _; rfl
  | var index =>
      intro position replacement
      simp only [subst, renameConstants]
      split
      · rfl
      · split <;> rfl
  | srt sort => intro _ _; rfl
  | pi domain body ihDomain ihBody =>
      intro position replacement
      simp [subst, renameConstants, ihDomain, ihBody, renameConstants_lift]
  | lam domain body ihDomain ihBody =>
      intro position replacement
      simp [subst, renameConstants, ihDomain, ihBody, renameConstants_lift]
  | app function argument ihFunction ihArgument =>
      intro position replacement
      simp [subst, renameConstants, ihFunction, ihArgument]

theorem renameConstants_instantiate (naming : String → String) (assignment : Nat → LF.Term)
    (term : LF.Term) :
    ∀ depth : Nat,
      renameConstants naming (instantiate assignment depth term) =
        instantiate (fun index => renameConstants naming (assignment index)) depth
          (renameConstants naming term) := by
  induction term with
  | con name => intro _; rfl
  | var index =>
      intro depth
      simp only [instantiate, renameConstants]
      split
      · rfl
      · exact renameConstants_lift naming _ depth 0
  | srt sort => intro _; rfl
  | pi domain body ihDomain ihBody => intro depth; simp [instantiate, renameConstants, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro depth; simp [instantiate, renameConstants, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro depth; simp [instantiate, renameConstants, ihFunction, ihArgument]

/-- A context with its constants renamed. -/
def renameContext (naming : String → String) : Context → Context
  | .hole => .hole
  | .piDomain rest body => .piDomain (renameContext naming rest) (renameConstants naming body)
  | .piBody domain rest => .piBody (renameConstants naming domain) (renameContext naming rest)
  | .lamDomain rest body => .lamDomain (renameContext naming rest) (renameConstants naming body)
  | .lamBody domain rest => .lamBody (renameConstants naming domain) (renameContext naming rest)
  | .appFunction rest argument =>
      .appFunction (renameContext naming rest) (renameConstants naming argument)
  | .appArgument function rest =>
      .appArgument (renameConstants naming function) (renameContext naming rest)

theorem renameConstants_plug (naming : String → String) (term : LF.Term) :
    ∀ context : Context,
      renameConstants naming (context.plug term) =
        (renameContext naming context).plug (renameConstants naming term) := by
  intro context
  induction context with
  | hole => rfl
  | piDomain rest body ih => simp [Context.plug, renameContext, renameConstants, ih]
  | piBody domain rest ih => simp [Context.plug, renameContext, renameConstants, ih]
  | lamDomain rest body ih => simp [Context.plug, renameContext, renameConstants, ih]
  | lamBody domain rest ih => simp [Context.plug, renameContext, renameConstants, ih]
  | appFunction rest argument ih => simp [Context.plug, renameContext, renameConstants, ih]
  | appArgument function rest ih => simp [Context.plug, renameContext, renameConstants, ih]

/-- The constants that the rules of a list mention. -/
def constantsOfRules (rules : List RewriteRule) : List String :=
  rules.flatMap fun rule => constantsOf rule.lhs ++ constantsOf rule.rhs

/-- **A renaming of constants that the rules do not mention carries a step to
a step.** -/
theorem Step.rename {rules : List RewriteRule} (naming : String → String)
    (fixed : ∀ name ∈ constantsOfRules rules, naming name = name) {source target : LF.Term}
    (step : Step (programTheory rules) source target) :
    Step (programTheory rules) (renameConstants naming source) (renameConstants naming target) := by
  cases step with
  | inContext context root =>
      rw [renameConstants_plug, renameConstants_plug]
      refine Step.inContext _ ?_
      cases root with
      | beta domain body argument =>
          have contracted := RootStep.beta (theory := programTheory rules)
            (renameConstants naming domain) (renameConstants naming body)
            (renameConstants naming argument)
          simpa [renameConstants, subst0, renameConstants_subst] using contracted
      | delta defined => cases defined
      | @rule rule assignment member =>
          have left : renameConstants naming rule.lhs = rule.lhs :=
            renameConstants_of_fixed naming _ fun name found =>
              fixed name (List.mem_flatMap.mpr ⟨rule, member, List.mem_append_left _ found⟩)
          have right : renameConstants naming rule.rhs = rule.rhs :=
            renameConstants_of_fixed naming _ fun name found =>
              fixed name (List.mem_flatMap.mpr ⟨rule, member, List.mem_append_right _ found⟩)
          have fired := RootStep.rule (theory := programTheory rules)
            (fun index => renameConstants naming (assignment index)) member
          simpa [inst, renameConstants_instantiate, left, right] using fired

theorem Reduces.rename {rules : List RewriteRule} (naming : String → String)
    (fixed : ∀ name ∈ constantsOfRules rules, naming name = name) {source target : LF.Term}
    (reduces : Reduces (programTheory rules) source target) :
    Reduces (programTheory rules) (renameConstants naming source)
      (renameConstants naming target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.rename naming fixed step)

/-- There are infinitely many names. -/
theorem infinite_names : Infinite String :=
  Infinite.of_injective Nat.repr fun _ _ same => Nat.repr_injective same

/-- The call of the equality of data on two symbols, with names written as
constants. -/
def symbolsCall (first second : String) : LF.Term :=
  callTerm "nik:data-eq" (data constantSpelling [.sym first, .sym second])

theorem renameConstants_symbolsCall (naming : String → String)
    (fixed : ∀ name ∈ ["call", "nik:data-eq", "cons", "sym", "nil"], naming name = name)
    (first second : String) :
    renameConstants naming (symbolsCall first second) =
      symbolsCall (naming first) (naming second) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
  simp [symbolsCall, callTerm, data, datum, tag, cells, constantSpelling, renameConstants,
    fixed "call" (.inl rfl), fixed "nik:data-eq" (.inr (.inl rfl)),
    fixed "cons" (.inr (.inr (.inl rfl))), fixed "sym" (.inr (.inr (.inr (.inl rfl)))),
    fixed "nil" (.inr (.inr (.inr (.inr rfl))))]

/-- **With a name written as a constant, no finite table decides the equality
of two symbols**: there is no list of rules such that the call of the equality
of data on two symbols reduces to `False` exactly when the two names
differ. -/
theorem no_table_decides_constants (rules : List RewriteRule) :
    ¬ ∀ first second : String,
        Reduces (programTheory rules) (symbolsCall first second) (truth constantSpelling false) ↔
          first ≠ second := by
  intro decides
  have names := infinite_names
  let avoided : Finset String :=
    (constantsOfRules rules ++ ["call", "nik:data-eq", "cons", "sym", "nil", "False"]).toFinset
  obtain ⟨first, firstFresh⟩ := Infinite.exists_notMem_finset avoided
  obtain ⟨second, secondFresh⟩ := Infinite.exists_notMem_finset (insert first avoided)
  have different : first ≠ second := fun same =>
    secondFresh (same ▸ Finset.mem_insert_self first avoided)
  have secondAvoids : second ∉ avoided := fun member =>
    secondFresh (Finset.mem_insert_of_mem member)
  let naming : String → String := fun name => if name = second then first else name
  have fixes : ∀ name ∈ avoided, naming name = name := by
    intro name member
    have other : name ≠ second := fun same => secondAvoids (same ▸ member)
    simp [naming, other]
  have fixedRules : ∀ name ∈ constantsOfRules rules, naming name = name :=
    fun name member => fixes name (by simp [avoided, member])
  have reduces := Reduces.rename naming fixedRules ((decides first second).mpr different)
  have falseFixed : renameConstants naming (truth constantSpelling false) =
      truth constantSpelling false := by
    simp [truth, tag, constantSpelling, renameConstants, fixes "sym" (by simp [avoided]),
      fixes "False" (by simp [avoided])]
  rw [renameConstants_symbolsCall naming (fun name member => fixes name (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [avoided])),
    falseFixed] at reduces
  have firstStays : naming first = first := by simp [naming]
  have secondMoves : naming second = first := by simp [naming]
  rw [firstStays, secondMoves] at reduces
  exact (decides first first).mp reduces rfl

#print axioms Step.rename
#print axioms Reduces.rename
#print axioms no_table_decides_constants

end Mettapedia.Logic.HostingStyles.StoredPrograms
