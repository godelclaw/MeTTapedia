import Mettapedia.Logic.HOL.Embedding.InferenceRules

/-!
# Replay of finite first-order rule axioms in HOL

Each source rule is one universally closed implication chain. Its application
instantiates the quantifiers with the original canonical arguments and applies
the supplied premise proofs. Together with the source model's reflection law,
this gives faithful hosting by a finite schematic HOL theory.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.InferenceRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

/-- A typed substitution out of a homogeneous finite formal context. -/
def substOfValues {Γ : Ctx FirstOrder.BaseTy} :
    {count : Nat} → (Fin count → Term Symbol Γ dataTy) →
      Subst Symbol (FirstOrder.CtxOfArity count) Γ
  | 0, _, _, index => nomatch index
  | count + 1, values, _, .vz => values 0
  | count + 1, values, _, .vs index =>
      substOfValues (fun position => values position.succ) index

@[simp] theorem substOfValues_ofFinRepeat {Γ : Ctx FirstOrder.BaseTy} :
    ∀ {count : Nat} (values : Fin count → Term Symbol Γ dataTy) (index : Fin count),
      substOfValues values (Var.ofFinRepeat dataTy count index) = values index
  | 0, _, index => nomatch index
  | count + 1, values, ⟨0, _⟩ => rfl
  | count + 1, values, ⟨position + 1, bound⟩ => by
      simpa only [Var.ofFinRepeat, substOfValues, Fin.succ] using
        substOfValues_ofFinRepeat (fun index => values index.succ)
          ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- Supply each quantified source formal with its original argument value. -/
def argumentSubstitution (names : List String) (arguments : List Pattern)
    (arity : arguments.length = names.length) :
    Subst Symbol (FirstOrder.CtxOfArity names.length) [] :=
  substOfValues (fun index => encode (arguments[index.val]'(by rw [arity]; exact index.isLt)))

/-- Read the ordered argument vector through a declared formal's position. -/
def argumentValues (names : List String) (arguments : List Pattern) (name : String) : Pattern :=
  argumentAt arguments (names.idxOf name)

/-- Quantifier substitution and named argument lookup agree at every formal. -/
theorem subst_formalValues {names : List String} {arguments : List Pattern}
    (arity : arguments.length = names.length) {name : String} (member : name ∈ names) :
    subst (argumentSubstitution names arguments arity) (formalValues names name) =
      encode (argumentValues names arguments name) := by
  have bound : names.idxOf name < arguments.length := by
    rw [arity]
    exact List.idxOf_lt_length_iff.mpr member
  simp only [formalValues, dif_pos member, subst, argumentSubstitution,
    substOfValues_ofFinRepeat, argumentValues, argumentAt,
    List.getElem?_eq_getElem bound, Option.getD_some]

/-- The positional argument assignment is exactly the source binding row. -/
theorem argumentBindings_agree {names : List String} {arguments : List Pattern}
    (distinct : names.Nodup) (arity : arguments.length = names.length) :
    ∀ name ∈ names, (names.zip arguments).find? (fun entry => entry.1 == name) =
      some (name, argumentValues names arguments name) := by
  intro name member
  have bound : names.idxOf name < arguments.length := by
    rw [arity]
    exact List.idxOf_lt_length_iff.mpr member
  have found := find?_zip distinct (List.getElem?_idxOf member)
    (List.getElem?_eq_getElem bound)
  simpa only [argumentValues, argumentAt, List.getElem?_eq_getElem bound,
    Option.getD_some] using found

/-- Actual HOL substitution produces the encoding of the source instance. -/
theorem subst_schema {names : List String} {arguments : List Pattern} {pattern : Pattern}
    (schema : Schema names pattern) (distinct : names.Nodup)
    (arity : arguments.length = names.length) :
    subst (argumentSubstitution names arguments arity) (encodeWith (formalValues names) pattern) =
      encode (applyBindings (names.zip arguments) pattern) := by
  rw [subst_encodeWith]
  calc
    _ = encodeWith (fun name => encode (argumentValues names arguments name)) pattern :=
      encodeWith_congr schema (fun _ member => subst_formalValues arity member)
    _ = _ := (encode_applyBindings schema (argumentValues names arguments) (names.zip arguments)
      (argumentBindings_agree distinct arity)).symm

/-- The entire implication chain instantiates with the original premise order. -/
theorem subst_openRule {rules : List FORule} (package : SchemaPackage rules)
    {rule : FORule} (member : rule ∈ rules) (arguments : List Pattern)
    (arity : arguments.length = rule.vars.length) :
    subst (argumentSubstitution rule.vars arguments arity) (openRule rule) =
      hypChain (rule.instPremises arguments |>.map judgment)
        (judgment (rule.instConclusion arguments)) := by
  rw [openRule, subst_hypChain]
  congr 1
  · simp only [FORule.instPremises, FORule.bindings, List.map_map]
    apply List.map_congr_left
    intro pattern patternMember
    change holds (subst (argumentSubstitution rule.vars arguments arity)
      (encodeWith (formalValues rule.vars) pattern)) =
        holds (encode (applyBindings (rule.vars.zip arguments) pattern))
    rw [subst_schema ((package.premises rule member).member patternMember)
      (package.nodup rule member) arity]
  · change holds (subst (argumentSubstitution rule.vars arguments arity)
      (encodeWith (formalValues rule.vars) rule.conclusion)) =
        holds (encode (applyBindings (rule.vars.zip arguments) rule.conclusion))
    rw [subst_schema (package.conclusion rule member) (package.nodup rule member) arity]

/-- A source derivation replays through finitely many schematic HOL axioms. -/
theorem preserves {rules : List FORule} (package : SchemaPackage rules) {pattern : Pattern}
    (derivation : FODerivable rules pattern) : (theory rules).Provable (judgment pattern) := by
  induction derivation with
  | rule rule member arguments arity _valid _premises ih =>
      have axiomProof : (theory rules).Provable (ruleFormula rule) :=
        ClosedTheorySet.provable_of_mem (List.mem_map.mpr ⟨rule, member, rfl⟩)
      have instanceProof := ClosedTheorySet.provable_closeAll_elim (theory rules)
        (openRule rule) (argumentSubstitution rule.vars arguments arity) axiomProof
      rw [subst_openRule package member arguments arity] at instanceProof
      apply ClosedTheorySet.provable_hypChain_elim (theory rules) _ _ instanceProof
      intro premise premiseMember
      obtain ⟨sourcePremise, sourceMember, rfl⟩ := List.mem_map.mp premiseMember
      exact ih sourcePremise sourceMember

/-- The finite generated HOL theory derives precisely the canonical source
judgments, even when arbitrary additional HOL reasoning is used. -/
theorem provable_iff {rules : List FORule} (package : SchemaPackage rules) {pattern : Pattern}
    (valid : argumentValidAt 0 pattern = true) :
    (theory rules).Provable (judgment pattern) ↔ FODerivable rules pattern :=
  ⟨reflects package valid, preserves package⟩

end Mettapedia.Logic.HOL.Embedding.InferenceRules
