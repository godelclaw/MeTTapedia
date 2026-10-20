import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.SourceFilling

/-!
# Reconstructing authored source programs from contextual native requests

The source is determined by the selected hole, shared indices and rely
values. Reconstruction instantiates the enclosing authored syntax at its
original scoped addresses. It never enumerates a universe of terms and
does not need the metavariables hidden inside the supplied focus.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Source

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching DerivedContexts
open Mettapedia.OSLF.NativeTypes.Modal Instantiation
open FocusMeaning FiniteFocusChecking

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

def seed (parameters : Parameters installed index ambient)
    (values : RelyValues installed index ambient) : ScopedRuleMatching.Assignment :=
  (List.finRange _).map (fun position =>
    (installed.indexed.headers[index].indices[position].slot.name,
      (parameters.indices position).value.val)) ++
  (List.finRange _).map (fun position =>
    (installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely[position].slot.name,
      (values position).val))

/-- At most one whole source is needed for a fixed contextual request. -/
def source? (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) : Option Pattern :=
  (fill? Substitution.instantiateBVar (installed.indexed.schema index).declaration.rule
    (installed.indexed.schema index).declaration.binding.spec ambient.length .left [] 0
    (seed parameters values) focus (installed.indexed.schema index).declaration.rule.left
    (installed.indexed.schema index).position).map Pattern.eraseBinderMetadata

def sources (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) : List Pattern :=
  (source? parameters focus values).toList

theorem sources_length (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) : (sources parameters focus values).length ≤ 1 := by
  unfold sources
  cases source? parameters focus values <;> simp

theorem sources_exact (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (source : Pattern) :
    source ∈ sources parameters focus values ↔
      ∃ rawSource, fill? Substitution.instantiateBVar (installed.indexed.schema index).declaration.rule
        (installed.indexed.schema index).declaration.binding.spec ambient.length .left [] 0
        (seed parameters values) focus (installed.indexed.schema index).declaration.rule.left
        (installed.indexed.schema index).position = some rawSource ∧
          rawSource.eraseBinderMetadata = source := by
  simp only [sources, source?, Option.mem_toList, Option.map_eq_some_iff]

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Source
