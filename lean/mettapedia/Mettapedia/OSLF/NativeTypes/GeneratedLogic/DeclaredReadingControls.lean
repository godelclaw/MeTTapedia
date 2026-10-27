import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings

/-!
# Controls: one set language, three declared readings

The pool language (`SetReadings.pool`, the rule `{A, ...rest} ⇒ {B, ...rest}`) is declared three ways and asked at
`{A}`, through the front door of a declared language (`askDeclared`), evaluated by the kernel:

| declared reading | some run reaches `{B}` | every run reaches `{B}` |
|---|---|---|
| consume | yes | yes |
| keep | no | no |
| either | yes | — |

The either reading's universal verdict is not settled by the front door's search within the budget; it is false
(`SetReadings.either_verdicts`), by a run that keeps copying `A`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings.Controls

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open SetReadings (pool onlyA onlyB reaches eventually)

def consumePool : DeclaredLanguage := { language := pool, sets := .consume }
def keepPool : DeclaredLanguage := { language := pool, sets := .keep }
def eitherPool : DeclaredLanguage := { language := pool }

theorem consume_reaches : askDeclared RelationEnv.empty consumePool 2 3 (reaches onlyB) onlyA = some true := by
  decide +kernel

theorem consume_eventually : askDeclared RelationEnv.empty consumePool 2 3 (eventually onlyB) onlyA = some true := by
  decide +kernel

theorem keep_reaches : askDeclared RelationEnv.empty keepPool 2 3 (reaches onlyB) onlyA = some false := by
  decide +kernel

theorem keep_eventually : askDeclared RelationEnv.empty keepPool 2 3 (eventually onlyB) onlyA = some false := by
  decide +kernel

theorem either_reaches : askDeclared RelationEnv.empty eitherPool 2 3 (reaches onlyB) onlyA = some true := by
  decide +kernel

theorem either_eventually_open :
    askDeclared RelationEnv.empty eitherPool 2 3 (eventually onlyB) onlyA = none := by
  decide +kernel

/-- **The declared readings disagree as the readings do**: consume and either establish that some run reaches `{B}`,
keep refutes it. -/
theorem declared_verdicts :
    (nativeStructure RelationEnv.empty consumePool).sat Env.closed (reaches onlyB) (pointOf consumePool onlyA) ∧
      ¬ (nativeStructure RelationEnv.empty keepPool).sat Env.closed (reaches onlyB) (pointOf keepPool onlyA) ∧
      (nativeStructure RelationEnv.empty eitherPool).sat Env.closed (reaches onlyB) (pointOf eitherPool onlyA) :=
  ⟨(askDeclared_sound (by decide) consume_reaches).mp rfl,
    fun holds => Bool.false_ne_true ((askDeclared_sound (by decide) keep_reaches).mpr holds),
    (askDeclared_sound (by decide) either_reaches).mp rfl⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings.Controls
