import Mettapedia.GraphTheory.FourColor.KempeChainCertificate
import Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
import Mettapedia.GraphTheory.FourColor.MatchingEdgeClosure

/-!
# When a single physical switch cannot equalize two edge requests

Different endpoint requests can become equal in one switch only by
swapping those two colours and touching exactly one endpoint. An actual
two-colour chain joining the endpoints prevents that particular repair.
-/

namespace Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch

open GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V E : Type*} [DecidableEq V]
variable {inc : E → Finset V} {S : Finset E}
variable (C : (graph inc S).Coloring (Fin 3)) (r s : Fin 3)
variable (K : (C.bicoloredSubgraph r s).ConnectedComponent)

/-- A connected saturated chain at the two contacts certifies identical
contact with every physical component of the selected colours. -/
theorem touches_iff_of_chain (chain : List E)
    (hc : chain.IsChain (graph inc S).Adj)
    (ha : ∀ x ∈ chain, C x = r ∨ C x = s)
    (hclosed : ∀ x ∈ chain, ∀ y, (graph inc S).Adj x y →
      (C y = r ∨ C y = s) → y ∈ chain)
    {u v : V} {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hux : u ∈ inc x) (hvy : v ∈ inc y) (hxc : x ∈ chain) (hyc : y ∈ chain) :
    Touches C r s K u ↔ Touches C r s K v := by
  constructor
  · intro hu
    have hxK := mem_component_of_touches C r s K hu hx hux (ha x hxc)
    have hyK := (C.kempe_component_iff_mem_chain r s K chain hc ha hclosed hxc hxK y).mpr hyc
    exact ⟨y, hy, hvy, hyK⟩
  · intro hv
    have hyK := mem_component_of_touches C r s K hv hy hvy (ha y hyc)
    have hxK := (C.kempe_component_iff_mem_chain r s K chain hc ha hclosed hyc hyK x).mpr hxc
    exact ⟨x, hx, hux, hxK⟩

private theorem other_pair_keeps_distinct : ∀ r s a b : Fin 3, r ≠ s →
    ¬ ((a = r ∧ b = s) ∨ (a = s ∧ b = r)) → ∀ hu hv : Bool,
    (if hu then Equiv.swap a b r else r) ≠ (if hv then Equiv.swap a b s else s) := by
  decide

omit r s K in
/-- The only potentially successful colour pair is the pair of requests;
if all its components have equal contact at the endpoints, none repairs it. -/
theorem switched_requests_distinct {u v : V} (m n : Fin 3) (hmn : m ≠ n)
    (hcontact : ∀ a b : Fin 3, ∀ L : (C.bicoloredSubgraph a b).ConnectedComponent,
      ((a = m ∧ b = n) ∨ (a = n ∧ b = m)) →
      (Touches C a b L u ↔ Touches C a b L v))
    (a b : Fin 3) (L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (if Touches C a b L u then Equiv.swap a b m else m) ≠
      (if Touches C a b L v then Equiv.swap a b n else n) := by
  classical
  by_cases hp : (a = m ∧ b = n) ∨ (a = n ∧ b = m)
  · have hc := hcontact a b L hp
    by_cases hu : Touches C a b L u
    · simpa only [hu, hc.mp hu, ite_true] using (Equiv.swap a b).injective.ne hmn
    · have hv : ¬ Touches C a b L v := fun h => hu (hc.mpr h)
      simpa only [hu, hv, ite_false] using hmn
  · simpa only [decide_eq_true_eq] using
      other_pair_keeps_distinct m n a b hmn hp (decide (Touches C a b L u))
        (decide (Touches C a b L v))

end
end Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
