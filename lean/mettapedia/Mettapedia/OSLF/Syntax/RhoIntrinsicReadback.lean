import Mettapedia.OSLF.Syntax.RhoQuotationClassFibres

/-!
# Sorted readback into the intrinsic rho presentation

The readback checks the sort of every bound index against its actual context.
An input opens its body under a name variable, as in the intrinsic signature.
Quotation reads a process in the same context; it does not replace the
intrinsic presentation's substitution discipline by the separately admitted
sealed-code payload profile.

Parallel bags are read as binary composition ending in null. The source unit
equation will compare this representation with the original binary term.
Malformed constructors, mismatched sorts, unbound indices and constructors
outside the signature return no term.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open MeTTaIL.Syntax

def variableAt : (context : Ctx sig) → (sort : Srt) → Nat → Option (Var context sort)
  | [], _, _ => none
  | head :: _, sort, 0 =>
      if same : head = sort then some (same ▸ Var.zero) else none
  | _ :: tail, sort, index + 1 => (variableAt tail sort index).map Var.succ

theorem variableAt_index : ∀ {context : Ctx sig} {sort : Srt} (position : Var context sort),
    variableAt context sort (varIdx position).val = some position
  | _, _, .zero => by simp [variableAt, varIdx]
  | _, _, .succ position => by
      simp only [variableAt, varIdx, Fin.val_succ, variableAt_index position, Option.map_some]

def outputRaw {context : Ctx sig} (name : Term sig context Srt.nm)
    (payload : Term sig context Srt.pr) : Term sig context Srt.pr :=
  .op Op.out (.cons name (.cons payload .nil))

def inputRaw {context : Ctx sig} (name : Term sig context Srt.nm)
    (continuation : Term sig (Srt.nm :: context) Srt.pr) : Term sig context Srt.pr :=
  .op Op.inp (.cons name (.cons continuation .nil))

mutual
def readName (context : Ctx sig) : Pattern → Option (Term sig context Srt.nm)
  | .bvar index => (variableAt context Srt.nm index).map Term.var
  | .apply "NQuote" [process] => (readProcess context process).map quoteRaw
  | _ => none

def readProcess (context : Ctx sig) : Pattern → Option (Term sig context Srt.pr)
  | .bvar index => (variableAt context Srt.pr index).map Term.var
  | .apply "PZero" [] => some null
  | .apply "PDrop" [name] => (readName context name).map dropRaw
  | .apply "POutput" [name, payload] =>
      (readName context name).bind fun channel =>
        (readProcess context payload).map (outputRaw channel)
  | .apply "PInput" [name, .lambda none body] =>
      (readName context name).bind fun channel =>
        (readProcess (Srt.nm :: context) body).map (inputRaw channel)
  | .collection .hashBag elements none => readProcesses context elements
  | _ => none

def readProcesses (context : Ctx sig) : List Pattern → Option (Term sig context Srt.pr)
  | [] => some null
  | process :: remaining =>
      (readProcess context process).bind fun first =>
        (readProcesses context remaining).map (parallel first)
end

def read (context : Ctx sig) (sort : Srt) : Pattern → Option (Term sig context sort) :=
  match sort with
  | .nm => readName context
  | .pr => readProcess context

theorem mismatched_variable_sort : readName [Srt.pr] (.bvar 0) = none := by decide +kernel

theorem unbound_variable_rejected : readProcess [] (.bvar 0) = none := rfl

theorem wrong_constructor_sort : readName [] (.apply "PZero" []) = none := by decide +kernel

theorem input_bound_name_retained :
    readProcess [] (.apply "PInput" [.apply "NQuote" [.apply "PZero" []],
      .lambda none (.apply "PDrop" [.bvar 0])]) =
      some (inputRaw (quoteRaw null) (dropRaw (.var .zero))) := by decide +kernel

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
