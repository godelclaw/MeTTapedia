import Mettapedia.OSLF.Syntax.RhoIntrinsicReadback

/-!
# Whole sorted intrinsic encoding/readback roundtrip

Every intrinsic term reads back in its original context and sort. The readback
retains input binders and arbitrary variables under quotations. The only
representation difference is the trailing null of a parallel bag; the actual
source unit equation earns its removal. Hence encoding followed by readback
recovers the original source equation class, for every term.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding

theorem read_encoded : ∀ {context : Ctx sig} {sort : Srt} (term : Term sig context sort),
    ∃ decoded : Term sig context sort,
      read context sort (encodeTerm term) = some decoded ∧ EqClosure rhoSourceE decoded term
  | _, sort, .var position => by
      refine ⟨.var position, ?_, .refl _⟩
      cases sort <;>
        simp only [read, encodeTerm, readName, readProcess, variableAt_index, Option.map_some]
  | _, _, .op .nil .nil => ⟨null, rfl, .refl _⟩
  | _, _, .op .par (.cons first (.cons second .nil)) => by
      obtain ⟨firstDecoded, firstRead, firstEquation⟩ := read_encoded first
      obtain ⟨secondDecoded, secondRead, secondEquation⟩ := read_encoded second
      simp only [read, List.nil_append] at firstRead secondRead
      refine ⟨parallel firstDecoded (parallel secondDecoded null), ?_, ?_⟩
      · simp only [read, encodeTerm, encodeArgs, wrapBinders, List.foldr_nil,
          readProcess, readProcesses, firstRead, secondRead, Option.bind_some, Option.map_some]
      · exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.par (.cons (bs := []) firstEquation
          (.cons (bs := []) ((parallel_null_equation secondDecoded).trans secondEquation) .nil))
  | _, _, .op .out (.cons name (.cons payload .nil)) => by
      obtain ⟨nameDecoded, nameRead, nameEquation⟩ := read_encoded name
      obtain ⟨payloadDecoded, payloadRead, payloadEquation⟩ := read_encoded payload
      simp only [read, List.nil_append] at nameRead payloadRead
      refine ⟨outputRaw nameDecoded payloadDecoded, ?_, ?_⟩
      · simp only [read, encodeTerm, encodeArgs, wrapBinders, List.foldr_nil,
          readProcess, nameRead, payloadRead, Option.bind_some, Option.map_some]
      · exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.out
          (.cons (bs := []) nameEquation (.cons (bs := []) payloadEquation .nil))
  | _, _, .op .inp (.cons name (.cons continuation .nil)) => by
      obtain ⟨nameDecoded, nameRead, nameEquation⟩ := read_encoded name
      obtain ⟨bodyDecoded, bodyRead, bodyEquation⟩ := read_encoded continuation
      simp only [read, List.nil_append, List.cons_append] at nameRead bodyRead
      refine ⟨inputRaw nameDecoded bodyDecoded, ?_, ?_⟩
      · simp only [read, encodeTerm, encodeArgs, wrapBinders, List.foldr_cons, List.foldr_nil,
          readProcess, nameRead, bodyRead, Option.bind_some, Option.map_some]
      · exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.inp
          (.cons (bs := []) nameEquation
            (EqArgs.cons (S := sig) (E := rhoSourceE) (bs := [Srt.nm]) bodyEquation .nil))
  | _, _, .op .quo (.cons process .nil) => by
      obtain ⟨decoded, readout, equation⟩ := read_encoded process
      simp only [read, List.nil_append] at readout
      refine ⟨quoteRaw decoded, ?_, ?_⟩
      · simp only [read, encodeTerm, encodeArgs, wrapBinders, List.foldr_nil,
          readName, readout, Option.map_some]
      · exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.quo (.cons (bs := []) equation .nil)
  | _, _, .op .drp (.cons name .nil) => by
      obtain ⟨decoded, readout, equation⟩ := read_encoded name
      simp only [read, List.nil_append] at readout
      refine ⟨dropRaw decoded, ?_, ?_⟩
      · simp only [read, encodeTerm, encodeArgs, wrapBinders, List.foldr_nil,
          readProcess, readout, Option.map_some]
      · exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.drp (.cons (bs := []) equation .nil)

theorem read_encoded_class {context : Ctx sig} {sort : Srt}
    (term : Term sig context sort) :
    ∃ decoded, read context sort (encodeTerm term) = some decoded ∧
      (project decoded : TermQ rhoSourceE context sort) = project term := by
  obtain ⟨decoded, readout, equation⟩ := read_encoded term
  exact ⟨decoded, readout, Quotient.sound equation⟩

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
