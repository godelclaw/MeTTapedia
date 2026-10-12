import Mettapedia.OSLF.Syntax.RhoIntrinsicCanonicalBag
import Mettapedia.OSLF.MeTTaIL.PatternTreeSize

/-!
# Recursive components of actual quoted parallel decompositions

An exposed dropped-name component either refers to the quoted name itself,
through the name equation and a parallel unit, or has strictly smaller
canonical syntax. The self-reference alternative is retained explicitly.
Thus this result does not assume that all equation-class decompositions
strictly decrease a measure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoRecursiveComponentDescent

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback RhoCanonicalNamePairs
open RhoFiniteQuotationOrigins RhoIntrinsicCanonicalBag
open MeTTaIL.Syntax
open MeTTaIL.PatternTreeSize
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

theorem bagSplice_member_size {pattern component : Pattern}
    (member : component ∈ bagSplice pattern) : nodes component ≤ nodes pattern := by
  unfold bagSplice at member
  split at member
  ·
    have smaller := member_nodes_le member
    simp_all only [nodes]
    omega
  · have same := List.mem_singleton.mp member
    rw [same]

theorem component_size {context : Ctx sig} (process : Process context) {component : Pattern}
    (member : component ∈ components process) :
    nodes component ≤ nodes (encodeEquationClass process) := by
  rw [components_bagContents] at member
  have contained : component ∈ bagSplice (encodeEquationClass process) := by
    have filtered : component ∈ bagSplice (encodeEquationClass process) ∧
        decide (component ≠ Pattern.apply "PZero" []) = true := by
      simpa only [Multiset.mem_coe, bagContents, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_filter] using (show component ∈ bagContents
        [encodeEquationClass process] from member)
    exact filtered.1
  exact bagSplice_member_size contained

theorem drop_component_self_or_smaller {context : Ctx sig} (process : Process context)
    (child : Name context)
    (member : Pattern.apply "PDrop" [encodeEquationClass child] ∈ components process) :
    child = quote process ∨
      nodes (encodeEquationClass child) < nodes (encodeEquationClass (quote process)) := by
  cases dropped : dropBody (encodeEquationClass process) with
  | some pattern =>
    have shape := dropBody_shape dropped
    have decoded := read_encoded_equation_class process
    change readProcessClass context (encodeEquationClass process) = some process at decoded
    rw [shape, readProcessClass_drop] at decoded
    obtain ⟨name, _, processReadout⟩ := Option.map_eq_some_iff.mp decoded
    have inSingleton := member
    rw [← processReadout, drop_components, Multiset.mem_singleton] at inSingleton
    have same : child = name := canonical_encoding_injective context Srt.nm
      ((List.cons.inj (Pattern.apply.inj inSingleton).2).1)
    exact Or.inl (same.trans ((quote_drop name).symm.trans (congrArg quote processReadout)))
  | none =>
    have notDrop : ∀ name, encodeEquationClass process ≠ .apply "PDrop" [name] := by
      intro name same
      rw [same] at dropped
      cases dropped
    have contained := component_size process member
    rw [encode_quote, normalizeQuote_eq_quote_of_not_drop notDrop]
    simp only [nodes, listNodes] at contained ⊢
    exact Or.inr (by omega)

theorem left_recursive_self_or_smaller {context : Ctx sig} (child : Name context)
    (second : Process context) :
    child = quote (join (drop child) second) ∨
      nodes (encodeEquationClass child) <
        nodes (encodeEquationClass (quote (join (drop child) second))) := by
  apply drop_component_self_or_smaller
  rw [join_components, drop_components]
  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))

theorem right_recursive_self_or_smaller {context : Ctx sig} (first : Process context)
    (child : Name context) :
    child = quote (join first (drop child)) ∨
      nodes (encodeEquationClass child) <
        nodes (encodeEquationClass (quote (join first (drop child)))) := by
  apply drop_component_self_or_smaller
  rw [join_components, drop_components]
  exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))

end Mettapedia.OSLF.Binding.RhoRecursiveComponentDescent
