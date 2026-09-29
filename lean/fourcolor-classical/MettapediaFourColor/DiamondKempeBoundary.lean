import MettapediaFourColor.DiamondJointContract
import FourColor.CfReducible

/-!
# A boundary obstruction to separate diamond repairs

The two boundary insertions of configuration 4 share the internal diamond.
Repairing only one of their side-edge contractions does not satisfy the
Kempe coclosure obligation. The obstruction is a predicate on traces; no
realizability as a planar exterior is asserted.
-/

namespace FourColor.DiamondKempeBoundary

open Color DiamondConfigurations DiamondContract ConfigurationTable

def monochrome : List Color := List.replicate 8 c1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- Evaluate the small ring-eight closure, including convergence, in the kernel.
theorem monochrome_retained :
    Ctree.mem (kempeTree cf004.prog) (evenize (List.replicate 7 c1)) = true := by
  decide +kernel

theorem monochrome_not_coclosure :
    ¬ KempeCoclosure ((cfmap cf004).map.RingTrace ((cfmap cf004).cpring.rotate 1))
      monochrome := by
  intro h
  have h' := (not_mem_kempeTree_iff cf004.prog
    (et := List.replicate 7 c1) (by decide +kernel)).mpr h
  rw [monochrome_retained] at h'
  contradiction

def leftOnly : faces004.ContractAssignment [12, 25] :=
  ⟨fun v => ConfigurationFaceGraph.colorEquiv (lookup "ABABABABCDAD" v),
    by decide +kernel⟩

def rightOnly : faces004.ContractAssignment [32, 39] :=
  ⟨fun v => ConfigurationFaceGraph.colorEquiv (lookup "ABABABABADCD" v),
    by decide +kernel⟩

def referenceContract (cc : List (Fin 50)) : List (cfmap cf004).Dart :=
  cc.map realization004.numbering.symm

private theorem lift_contractTrace (cc : List (Fin 50)) {et : List Color}
    (h : table004.map.CcRingTrace cc (ring004.rotate 1) et) :
    (cfmap cf004).map.CcRingTrace (referenceContract cc)
      ((cfmap cf004).cpring.rotate 1) et := by
  rw [realization004.ccRingTrace, List.map_rotate, realization004.ring, cpring004]
  simpa [referenceContract, List.map_map, Function.comp_def] using h

theorem leftOnly_trace :
    (cfmap cf004).map.CcRingTrace (referenceContract [12, 25])
      ((cfmap cf004).cpring.rotate 1) monochrome := by
  apply lift_contractTrace
  rw [faces004.ccRingTrace_iff]
  exact ⟨leftOnly, by decide +kernel⟩

theorem rightOnly_trace :
    (cfmap cf004).map.CcRingTrace (referenceContract [32, 39])
      ((cfmap cf004).cpring.rotate 1) monochrome := by
  apply lift_contractTrace
  rw [faces004.ccRingTrace_iff]
  exact ⟨rightOnly, by decide +kernel⟩

/-- The left insertion alone fails the exact trace-repair obligation. -/
theorem leftOnly_not_repair : ¬ ∀ et,
    (cfmap cf004).map.CcRingTrace (referenceContract [12, 25])
      ((cfmap cf004).cpring.rotate 1) et →
    KempeCoclosure ((cfmap cf004).map.RingTrace ((cfmap cf004).cpring.rotate 1)) et :=
  fun h => monochrome_not_coclosure (h _ leftOnly_trace)

/-- The right insertion alone fails the same obligation. -/
theorem rightOnly_not_repair : ¬ ∀ et,
    (cfmap cf004).map.CcRingTrace (referenceContract [32, 39])
      ((cfmap cf004).cpring.rotate 1) et →
    KempeCoclosure ((cfmap cf004).map.RingTrace ((cfmap cf004).cpring.rotate 1)) et :=
  fun h => monochrome_not_coclosure (h _ rightOnly_trace)

private theorem joint_boundary_not_monochrome : ∀ a b x y z w,
    DiamondJointContract.Admissible a b x y z w →
      trace (DiamondJointContract.boundary a b x y z w) ≠ monochrome := by
  decide +kernel

/-- The shared diamond edge excludes this obstruction from the joint contract. -/
theorem monochrome_not_joint_contract :
    ¬ (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse
      monochrome := by
  rw [DiamondJointContract.contractTrace_iff]
  rintro ⟨a, b, x, y, z, w, h, he⟩
  exact joint_boundary_not_monochrome a b x y z w h he.symm

end FourColor.DiamondKempeBoundary
