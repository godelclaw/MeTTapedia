import Mettapedia.Languages.MeTTa.HE.TypeInterfaceOptimization

/-!
# Metatype discriminators for HE source demand

The demand decision can inspect a metatype discriminator without constructing
the corresponding symbol atom. The Boolean decision below is compared with
the existing relational policy for every subject, expected type and list
recognition service. This is a representation law, not a native allocation
bound or a correspondence proof for the C evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypeDemandDiscriminator

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypeInterfaceOptimization

inductive Metatype where
  | symbol | variable | grounded | expression | list | undefined
  deriving DecidableEq, Repr

def Metatype.name : Metatype → String
  | .symbol => "Symbol"
  | .variable => "Variable"
  | .grounded => "Grounded"
  | .expression => "Expression"
  | .list => "List"
  | .undefined => "%Undefined%"

def Metatype.atom (tag : Metatype) : Atom := .symbol tag.name

def matchesName (expected : Atom) (name : String) : Bool :=
  match expected with
  | .symbol value => value == name
  | _ => false

theorem matchesName_iff (expected : Atom) (name : String) :
    matchesName expected name = true ↔ expected = .symbol name := by
  cases expected <;> simp [matchesName]

def keepByTag (subject expected : Atom) (tag : Metatype) : Bool :=
  matchesName expected "Atom" || matchesName expected tag.name ||
    (matchesName expected "Expression" && expressionShape subject) ||
    decide (tag = .variable)

theorem variable_tag_iff (tag : Metatype) :
    tag = .variable ↔ tag.atom = Atom.variableType := by
  cases tag <;> simp [Metatype.atom, Metatype.name, Atom.variableType]

theorem keepByTag_iff (subject expected : Atom) (tag : Metatype) :
    keepByTag subject expected tag = true ↔
      KeepCondition subject expected tag.atom := by
  simp only [keepByTag, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    matchesName_iff, variable_tag_iff]
  simp [KeepCondition, Metatype.atom, Atom.atomType, Atom.expressionType, or_assoc]

def castByShape (listForm : Atom → Bool) : Atom → Bool
  | .symbol _ => true
  | .grounded _ => true
  | .expression [] => true
  | subject => listForm subject

theorem castByShape_iff (listForm : Atom → Bool) (subject : Atom) :
    castByShape listForm subject = true ↔ CastCondition listForm subject := by
  cases subject with
  | symbol _ => simp [castByShape, CastCondition]
  | var _ => simp [castByShape, CastCondition]
  | grounded _ => simp [castByShape, CastCondition]
  | expression items =>
      cases items <;> simp [castByShape, CastCondition]

def demandByTag (listForm : Atom → Bool) (subject expected : Atom)
    (tag : Metatype) : Demand :=
  if keepByTag subject expected tag then .keep
  else if castByShape listForm subject then .cast else .interpret

theorem demandByTag_exact (listForm : Atom → Bool) (subject expected : Atom)
    (tag : Metatype) :
    demandByTag listForm subject expected tag =
      demand listForm subject expected tag.atom := by
  simp only [demandByTag, demand, keepByTag_iff, castByShape_iff]

theorem demandByTag_sound (listForm : Atom → Bool) (subject expected : Atom)
    (tag : Metatype) :
    DemandRel listForm subject expected tag.atom
      (demandByTag listForm subject expected tag) := by
  rw [demandByTag_exact]
  exact demand_sound listForm subject expected tag.atom

namespace Controls

def integer : Atom := .grounded (.int 6)

theorem grounded_staging_is_preserved :
    demandByTag (fun _ => false) integer Atom.groundedType .grounded = .keep := by
  decide

theorem wrong_discriminator_changes_demand :
    demandByTag (fun _ => false) integer Atom.groundedType .symbol ≠
      demand (fun _ => false) integer Atom.groundedType Metatype.grounded.atom := by
  decide

theorem non_symbol_expected_is_not_a_metatype_match :
    matchesName (.expression [Atom.groundedType]) "Grounded" = false := by
  rfl

theorem undefined_application_still_interprets :
    demandByTag (fun _ => false) Controls.application Atom.undefinedType
      .expression = .interpret := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.HE.TypeDemandDiscriminator
