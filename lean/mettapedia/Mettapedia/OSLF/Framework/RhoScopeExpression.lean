import Mettapedia.OSLF.Framework.RhoEquationGeneratedScope

/-!
# Sorted positive scope expressions over the rho equation quotient

Process predicates and name predicates have distinct sorts. Quotation,
parallel composition and drop are interpreted by the actual quotient
operations and their complete image fibres. Variables are name predicates;
the least-fixed-point binder extends their positional environment.

Every expression is monotone in that environment. The interpretation is
constructed for arbitrary positive expressions, independently of the
two-atom scope generator. The syntax also retains its own description cost;
this cost is not recovered from an erased semantic transformer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeExpression

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationGeneratedScope

universe u

inductive Expression (Atom : Type u) : Srt → Type u where
  | atom (label : Atom) : Expression Atom Srt.pr
  | var (index : Nat) : Expression Atom Srt.nm
  | or {sort : Srt} (first second : Expression Atom sort) : Expression Atom sort
  | quote (process : Expression Atom Srt.pr) : Expression Atom Srt.nm
  | drop (name : Expression Atom Srt.nm) : Expression Atom Srt.pr
  | par (first second : Expression Atom Srt.pr) : Expression Atom Srt.pr
  | mu (body : Expression Atom Srt.nm) : Expression Atom Srt.nm

abbrev Environment (context : Ctx sig) := Nat → NamePredicate context

def push {context : Ctx sig} (names : NamePredicate context) (env : Environment context) :
    Environment context
  | 0 => names
  | index + 1 => env index

def pushNames {context : Ctx sig} (env : Environment context) :
    NamePredicate context →o Environment context where
  toFun := fun names => push names env
  monotone' := by
    intro first second inclusion index name member
    cases index with
    | zero => exact inclusion name member
    | succ index => exact member

theorem push_env_mono {context : Ctx sig} {first second : Environment context}
    (inclusion : first ≤ second) (names : NamePredicate context) :
    push names first ≤ push names second := by
  intro index name member
  cases index with
  | zero => exact member
  | succ index => exact inclusion index name member

def denote {Atom : Type u} {context : Ctx sig} (atoms : Atom → Process context → Prop) :
    {sort : Srt} → Expression Atom sort →
      Environment context →o (TermQ rhoSourceE context sort → Prop)
  | _, .atom label =>
      ⟨fun _ => atoms label, by intro _ _ _; exact le_rfl⟩
  | _, .var index =>
      ⟨fun env => env index, by intro _ _ inclusion; exact inclusion index⟩
  | _, .or first second =>
      { toFun := fun env value => denote atoms first env value ∨ denote atoms second env value
        monotone' := by
          intro firstEnv secondEnv inclusion value admitted
          rcases admitted with left | right
          · exact Or.inl ((denote atoms first).monotone inclusion value left)
          · exact Or.inr ((denote atoms second).monotone inclusion value right) }
  | _, .quote process =>
      { toFun := fun env name => ∃ origin, denote atoms process env origin ∧ quote origin = name
        monotone' := by
          intro firstEnv secondEnv inclusion name
          rintro ⟨origin, admitted, readout⟩
          exact ⟨origin, (denote atoms process).monotone inclusion origin admitted, readout⟩ }
  | _, .drop name =>
      { toFun := fun env process => ∃ origin, denote atoms name env origin ∧ drop origin = process
        monotone' := by
          intro firstEnv secondEnv inclusion process
          rintro ⟨origin, admitted, readout⟩
          exact ⟨origin, (denote atoms name).monotone inclusion origin admitted, readout⟩ }
  | _, .par first second =>
      { toFun := fun env process => ∃ firstOrigin secondOrigin,
          denote atoms first env firstOrigin ∧ denote atoms second env secondOrigin ∧
            join firstOrigin secondOrigin = process
        monotone' := by
          intro firstEnv secondEnv inclusion process
          rintro ⟨firstOrigin, secondOrigin, firstAdmitted, secondAdmitted, readout⟩
          exact ⟨firstOrigin, secondOrigin,
            (denote atoms first).monotone inclusion firstOrigin firstAdmitted,
            (denote atoms second).monotone inclusion secondOrigin secondAdmitted, readout⟩ }
  | _, .mu body =>
      { toFun := fun env => ((denote atoms body).comp (pushNames env)).lfp
        monotone' := by
          intro firstEnv secondEnv inclusion
          apply OrderHom.lfp.monotone
          intro names name admitted
          exact (denote atoms body).monotone (push_env_mono inclusion names) name admitted }

namespace Expression

def description {Atom : Type u} (atomCost : Atom → Nat) :
    {sort : Srt} → Expression Atom sort → Nat
  | _, .atom label => atomCost label
  | _, .var _ => 1
  | _, .or first second => description atomCost first + description atomCost second + 1
  | _, .quote process => description atomCost process + 1
  | _, .drop name => description atomCost name + 1
  | _, .par first second => description atomCost first + description atomCost second + 1
  | _, .mu body => description atomCost body + 1

def closedAt {Atom : Type u} : {sort : Srt} → Nat → Expression Atom sort → Bool
  | _, _, .atom _ => true
  | _, depth, .var index => decide (index < depth)
  | _, depth, .or first second => closedAt depth first && closedAt depth second
  | _, depth, .quote process => closedAt depth process
  | _, depth, .drop name => closedAt depth name
  | _, depth, .par first second => closedAt depth first && closedAt depth second
  | _, depth, .mu body => closedAt (depth + 1) body

end Expression

end Mettapedia.OSLF.Framework.RhoScopeExpression
