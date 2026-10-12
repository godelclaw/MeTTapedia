import Mettapedia.OSLF.Syntax.RhoFiniteParallelSplits

/-!
# Complete finite quoted-parallel decomposition catalogues

Each name's complete quotation-origin catalogue is combined with the complete
parallel-split catalogue of each origin. Both directions earn a finite list
of all source equation-class decompositions used by the scope generator.
This is an extensional value catalogue, not a recovery of execution origins
or a proof that all recursive decompositions strictly decrease.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoFiniteQuotedParallel

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoIntrinsicReadback
open RhoFiniteQuotationOrigins RhoFiniteParallelSplits

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

def decompositions {context : Ctx sig} (name : Name context) :
    Finset (Process context × Process context) := (origins name).biUnion candidates

theorem quoted_parallel_iff {context : Ctx sig} (name : Name context)
    (first second : Process context) :
    quote (join first second) = name ↔ (first, second) ∈ decompositions name := by
  rw [decompositions, Finset.mem_biUnion]
  constructor
  · intro readout
    exact ⟨join first second, (quotation_fibre_iff _ _).mp readout,
      (parallel_split_iff _ _ _).mp rfl⟩
  · rintro ⟨origin, admitted, pair⟩
    rw [(parallel_split_iff _ _ _).mpr pair]
    exact (quotation_fibre_iff _ _).mpr admitted

theorem left_unit_decomposition {context : Ctx sig} (name : Name context) :
    (zero context, drop name) ∈ decompositions name :=
  (quoted_parallel_iff _ _ _).mp ((congrArg quote (join_zero_left _)).trans (quote_drop name))

theorem right_unit_decomposition {context : Ctx sig} (name : Name context) :
    (drop name, zero context) ∈ decompositions name :=
  (quoted_parallel_iff _ _ _).mp (own_drop_beside_zero name)

theorem no_strict_measure_on_catalogue (context : Ctx sig) :
    ¬ ∃ measure : Name context → Nat, ∀ name : Name context,
      (drop name, zero context) ∈ decompositions name →
        measure name < measure (quote (join (drop name) (zero context))) := by
  rintro ⟨measure, decreases⟩
  have impossible := decreases (quote (zero context)) (right_unit_decomposition _)
  rw [own_drop_beside_zero] at impossible
  exact Nat.lt_irrefl _ impossible

end Mettapedia.OSLF.Binding.RhoFiniteQuotedParallel
