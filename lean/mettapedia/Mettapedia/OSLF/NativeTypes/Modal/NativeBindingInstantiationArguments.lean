import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFocusChecking
import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceCompleteness

/-!
# Ordered argument extraction for instantiated authored source trees

Successful scoped instantiation retains each authored argument address. Its
ordinary typing is recovered from the original grammar's actual parameter
list. Unique constructor labels identify that declaration independently of
the operational matcher.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingInstantiationArguments

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem grammar_equal {language : LanguageDef}
    (labels : (language.terms.map (·.label)).Nodup)
    {left right : GrammarRule} (leftMember : left ∈ language.terms)
    (rightMember : right ∈ language.terms) (same : left.label = right.label) : left = right := by
  obtain ⟨leftIndex, leftAt⟩ := List.mem_iff_getElem?.mp leftMember
  obtain ⟨rightIndex, rightAt⟩ := List.mem_iff_getElem?.mp rightMember
  have leftWithin : leftIndex < language.terms.length := List.getElem?_eq_some_iff.mp leftAt |>.1
  have rightWithin : rightIndex < language.terms.length := List.getElem?_eq_some_iff.mp rightAt |>.1
  have leftRead : language.terms[leftIndex] = left := List.getElem?_eq_some_iff.mp leftAt |>.2
  have rightRead : language.terms[rightIndex] = right := List.getElem?_eq_some_iff.mp rightAt |>.2
  have indexSame : leftIndex = rightIndex := by
    apply (labels.getElem_inj_iff (hi := by simpa using leftWithin)
      (hj := by simpa using rightWithin)).mp
    simpa only [List.getElem_map, leftRead, rightRead] using same
  exact leftRead.symm.trans (indexSame ▸ rightRead)

theorem instantiated_argument {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {assignment : Assignment} {offset index : Nat}
    {patterns results : List Pattern} {pattern : Pattern}
    (instantiated : instantiateArgsWith? operation rule spec ambient site path depth assignment offset patterns = some results)
    (located : patterns[index]? = some pattern) :
    ∃ result, results[index]? = some result ∧
      instantiateWith? operation rule spec ambient site (path ++ [offset + index]) depth assignment pattern = some result := by
  induction patterns generalizing results offset index with
  | nil => simp at located
  | cons first rest ih =>
      simp only [instantiateArgsWith?] at instantiated
      obtain ⟨result, head, remaining⟩ := Option.bind_eq_some_iff.mp instantiated
      obtain ⟨tail, tailComputed, same⟩ := Option.bind_eq_some_iff.mp remaining
      cases Option.some.inj same
      cases index with
      | zero =>
          cases Option.some.inj located
          exact ⟨result, rfl, by simpa only [Nat.add_zero] using head⟩
      | succ index =>
          obtain ⟨selected, selectedAt, computed⟩ := ih tailComputed located
          exact ⟨selected, selectedAt, by simpa only [Nat.add_assoc, Nat.add_comm 1 index] using computed⟩

theorem typed_argument {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    {index : Nat} {argument : Pattern} {parameter : TermParam} {expected : TypeExpr}
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (argumentAt : arguments[index]? = some argument)
    (parameterAt : parameters[index]? = some parameter)
    (parameterTyped : parameterType? parameter = some expected) :
    HasType language free bound argument expected := by
  cases typed with
  | nil => simp at argumentAt
  | cons _ sorted first rest =>
      cases index with
      | zero =>
          cases Option.some.inj argumentAt
          cases Option.some.inj parameterAt
          cases Option.some.inj (sorted.symm.trans parameterTyped)
          exact first
      | succ index => exact typed_argument rest argumentAt parameterAt parameterTyped
termination_by index

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingInstantiationArguments
