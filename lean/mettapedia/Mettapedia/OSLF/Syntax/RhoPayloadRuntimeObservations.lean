import Mettapedia.OSLF.Syntax.RhoPayloadParameterizedRuntime
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.OperationalReadback
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation

/-!
# Public input observations through the admitted payload comparison

The target observer reads its own payload-class representative. It does not
query source termination or compilation success. On translated runtime states,
the canonical readback and all finite public-input observations agree exactly
with the authored executor, by equation comparison and local step coverage.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoPayloadParameterizedRuntime

open Mettapedia.OSLF.Binding.RhoPayloadPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {free : FreeSortContext}
variable (namesOnly : ∀ x, free x ≠ some rhoReflectivePresentation.processSort)

theorem class_readback_canonical (process : ParameterizedRewriteSystem.Process free) :
    canonicalize (readback (Quotient.out (mapClass namesOnly process))) =
      canonicalize process.1 := by
  have representative := readback_sc (cls_eq_iff.mp
    (Quotient.out_eq (mapClass namesOnly process)))
  have translated := readback_translate.2.1 (Env.empty []) process.1
    (decode namesOnly process) VarEnv.empty (decode_spec namesOnly process)
  have combined := representative.trans _ _ _ translated
  have sourceFree := rhoProcWellSorted_hashSetFree
    ((ParameterizedRewriteSystem.process_iff _ _).mp process.2).1
  exact canonicalize_eq_of_structuralCongruence combined
    ((hashSetFree_iff_of_structuralCongruence combined).mpr sourceFree) sourceFree

def publicInput (channel : Pattern) : EquationPredicate targetTheory.closure :=
  ⟨fun state => ActiveInputObservation.HasInput channel (readback (Quotient.out state)), by
    intro first second equal
    cases equal
    rfl⟩

def sourceInput (channel : Pattern) :
    EquationPredicate (ParameterizedRewriteSystem.theory free).closure :=
  ⟨fun state => ActiveInputObservation.HasInput channel state.1,
    fun _ _ equal => ActiveInputObservation.canonical_congr equal⟩

theorem publicInput_map (channel : Pattern) (process : ParameterizedRewriteSystem.Process free) :
    (publicInput channel).1 (mapClass namesOnly process) ↔ (sourceInput channel).1 process :=
  ActiveInputObservation.canonical_congr (class_readback_canonical namesOnly process)

/-- An actual public response is reachable in either independently defined
presentation exactly when it is reachable in the other. -/
theorem may_input_iff (channel : Pattern) (process : ParameterizedRewriteSystem.Process free) :
    (semanticDiamond (ParameterizedRewriteSystem.theory free).closure (sourceInput channel)).1
      process ↔
    (semanticDiamond targetTheory.closure (publicInput channel)).1 (mapClass namesOnly process) := by
  constructor
  · intro result
    obtain ⟨reached, path, observed⟩ :=
      (Mettapedia.GSLT.IndexedOperational.closure_nativeDiamond_iff _ _ _).mp result
    apply (Mettapedia.GSLT.IndexedOperational.closure_nativeDiamond_iff _ _ _).mpr
    exact ⟨mapClass namesOnly reached, (covered namesOnly).cover.mapMultiStep path,
      (publicInput_map namesOnly channel reached).mpr observed⟩
  · intro result
    obtain ⟨reached, path, observedReached⟩ :=
      (Mettapedia.GSLT.IndexedOperational.closure_nativeDiamond_iff _ _ _).mp result
    obtain ⟨sourceEndpoint, equal, sourcePath⟩ := (covered namesOnly).cover.liftMultiStep path
    apply (Mettapedia.GSLT.IndexedOperational.closure_nativeDiamond_iff _ _ _).mpr
    refine ⟨sourceEndpoint, sourcePath,
      (publicInput_map namesOnly channel sourceEndpoint).mp ?_⟩
    exact Eq.mpr (congrArg (publicInput channel).1 equal) observedReached

end Mettapedia.OSLF.Binding.RhoPayloadParameterizedRuntime
