import Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiation

/-! Exact simultaneous substitution and the finite-word lowering boundary. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiation.Controls

def sig : Sig := sigOf fun index =>
  match index with
  | 0 | 1 | 6 | 7 => some (SymInfo.fvarOf 0)
  | 2 => some (SymInfo.fvarOf 2)
  | 3 | 5 => some ⟨.constant, [1]⟩
  | 4 => some ⟨.constant, [wordBound - 1]⟩
  | _ => none

def F : SymId := .fresh 0
def G : SymId := .fresh 1
def H : SymId := .fresh 2
def K : SymId := .fresh 3
def T : SymId := .fresh 6
def U : SymId := .fresh 7
def f : Term := .app F []
def g : Term := .app G []
def pair : Term := .eq f g

theorem crossing_replacements :
    statement sig [(F, g), (G, .natLit 7)] pair = some (.eq g (.natLit 7)) := by decide

theorem simultaneous_swap :
    statement sig [(F, g), (G, f)] pair = some (.eq g f) := by decide

theorem duplicate_first_wins :
    statement sig [(F, .natLit 8), (F, .natLit 9)] f = some (.natLit 8) := by decide

theorem invalid_shadow_refused :
    statement sig [(F, .natLit 8), (F, .bvar 0)] f = none := by decide

theorem unused_invalid_refused :
    statement sig [(F, .bvar 0)] (.natLit 3) = none := by decide

theorem constant_target_refused :
    statement sig [(K, .natLit 0)] (.natLit 3) = none := by decide

theorem higher_order_arguments :
    statement sig [(H, .eq (.bvar 1) (.bvar 0))]
      (.app H [.natLit 3, .natLit 4]) = some (.eq (.natLit 3) (.natLit 4)) := by decide

theorem under_binder :
    statement sig [(H, .eq (.bvar 1) (.bvar 0))]
      (.app K [.app H [.bvar 0, .natLit 4]]) =
        some (.app K [.eq (.bvar 0) (.natLit 4)]) := by decide

theorem singleton_under_binder_agrees :
    statement sig [(H, .eq (.bvar 1) (.bvar 0))]
      (.app K [.app H [.bvar 0, .natLit 4]]) =
    instantiateStatement sig H (.eq (.bvar 1) (.bvar 0))
      (.app K [.app H [.bvar 0, .natLit 4]]) :=
  statement_singleton sig H _ _

theorem validated_shadow_compaction :
    go sig [⟨F, 0, .natLit 8⟩, ⟨F, 0, .natLit 9⟩, ⟨G, 0, .natLit 7⟩] 0 pair =
      go sig [⟨F, 0, .natLit 8⟩, ⟨G, 0, .natLit 7⟩] 0 pair :=
  go_shadow sig ⟨F, 0, .natLit 8⟩ ⟨F, 0, .natLit 9⟩ rfl [⟨G, 0, .natLit 7⟩] 0 pair

theorem sequential_is_different :
    (instantiateStatement sig F g pair).bind (instantiateStatement sig G (.natLit 7)) =
      some (.eq (.natLit 7) (.natLit 7)) := by decide

/-- These constants have large binder counts but only one argument each.
The replacement is closed and has a free-variable head below both binders. -/
def largeClosed : Term := .app (.fresh 4) [.app (.fresh 5) [f]]

theorem large_closed : depth sig largeClosed = 0 := by decide

theorem simultaneous_large_accepts :
    statement sig [(F, largeClosed), (G, .natLit 7)] pair =
      some (.eq largeClosed (.natLit 7)) := by decide

/-- The proposed fresh-symbol lowering, retaining the old checked operations. -/
def freshSequential : Option Term := do
  let first ← instantiateStatement sig F (.app T []) pair
  let renamed ← instantiateStatement sig G (.app U []) first
  let inserted ← instantiateStatement sig T largeClosed renamed
  instantiateStatement sig U (.natLit 7) inserted

theorem fresh_sequential_refuses : freshSequential = none := by decide

def verdicts : List Bool := [
  decide (statement sig [(F, g), (G, .natLit 7)] pair = some (.eq g (.natLit 7))),
  decide (statement sig [(F, g), (G, f)] pair = some (.eq g f)),
  decide (statement sig [(F, .natLit 8), (F, .natLit 9)] f = some (.natLit 8)),
  decide (statement sig [(F, .natLit 8), (F, .bvar 0)] f = none),
  decide (statement sig [(F, .bvar 0)] (.natLit 3) = none),
  decide (statement sig [(K, .natLit 0)] (.natLit 3) = none),
  decide (statement sig [(H, .eq (.bvar 1) (.bvar 0))]
    (.app H [.natLit 3, .natLit 4]) = some (.eq (.natLit 3) (.natLit 4))),
  decide (statement sig [(H, .eq (.bvar 1) (.bvar 0))]
    (.app K [.app H [.bvar 0, .natLit 4]]) = some (.app K [.eq (.bvar 0) (.natLit 4)])),
  decide (depth sig largeClosed = 0),
  decide (statement sig [(F, largeClosed), (G, .natLit 7)] pair = some (.eq largeClosed (.natLit 7))),
  decide (freshSequential = none)]

theorem verdicts_all : verdicts.all id = true := by decide

#print axioms crossing_replacements
#print axioms under_binder
#print axioms simultaneous_large_accepts
#print axioms fresh_sequential_refuses

end Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiation.Controls
