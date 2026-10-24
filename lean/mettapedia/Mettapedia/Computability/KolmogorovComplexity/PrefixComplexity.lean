import Mettapedia.Computability.KolmogorovComplexity.PrefixMass
import Mettapedia.Computability.KolmogorovComplexity.ReferenceMachine

/-!
# Shortest descriptions and output mass

Shortest-description weight is bounded by output mass. Finite Kraft bounds
need representability only on queried outputs; global output completeness gives
unconditional bounds. Compiler-overhead invariance concerns effective reference
machines. The controls separate shortest weight, mass and observation.
-/

namespace KolmogorovComplexity

open scoped Classical BigOperators

open Mettapedia.UniversalAI.SolomonoffPrior

abbrev PrefixFreeMachine := Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine
abbrev OutputComplete := Mettapedia.UniversalAI.SolomonoffPrior.OutputComplete

/-- Prefix-free Kolmogorov complexity relative to a prefix-free machine `U`. -/
noncomputable abbrev prefixComplexity (U : PrefixFreeMachine) (x : BinString) : ℕ :=
  Mettapedia.UniversalAI.SolomonoffPrior.kolmogorovComplexity U x

notation "Kpf[" U "](" x ")" => prefixComplexity U x

/-- Output completeness supplies a program for every finite output. -/
theorem outputComplete_has_program (U : PrefixFreeMachine) [OutputComplete U]
    (x : BinString) : ∃ p : BinString, U.compute p = some x :=
  OutputComplete.has_program x

/-- A chosen shortest program for `x` under a prefix-free machine with every output represented. -/
noncomputable def shortestProgram (U : PrefixFreeMachine) [OutputComplete U] (x : BinString) : BinString :=
  Classical.choose
    (Mettapedia.UniversalAI.SolomonoffPrior.exists_program_of_complexity (U := U) (x := x)
      (h := outputComplete_has_program (U := U) x))

theorem shortestProgram_spec (U : PrefixFreeMachine) [OutputComplete U] (x : BinString) :
    U.compute (shortestProgram U x) = some x ∧ (shortestProgram U x).length = Kpf[U](x) :=
  Classical.choose_spec
    (Mettapedia.UniversalAI.SolomonoffPrior.exists_program_of_complexity U x (outputComplete_has_program U x))

theorem shortestProgram_injective (U : PrefixFreeMachine) [OutputComplete U] :
    Function.Injective (shortestProgram U) := by
  intro x y hxy
  simpa only [(shortestProgram_spec U x).1, (shortestProgram_spec U y).1, Option.some.injEq] using
    congrArg U.compute hxy

/-- Effective reference machines agree up to an additive compiler constant. -/
theorem invariance_Kpf (U V : ReferenceMachine) :
    ∃ c : ℕ, ∀ x : BinString, Kpf[U](x) ≤ Kpf[V](x) + c :=
  ReferenceMachine.invariance_le U V

/-- Convert the real weight `2^{-n}` into the `ENNReal`-native expression. -/
theorem ofReal_two_zpow_neg_nat (n : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ))) = (2 : ENNReal) ^ (-(n : ℤ)) := by
  simp [zpow_neg, ENNReal.zpow_neg, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_pow]

theorem two_zpow_neg_nat (n : ℕ) : (2 : ENNReal) ^ (-(n : ℤ)) = ((2 : ENNReal) ^ n)⁻¹ := by
  simp [ENNReal.zpow_neg]

/-- A represented output has at least the mass contributed by a shortest program. -/
theorem prefixComplexityWeight_le_outputMass (U : PrefixFreeMachine) (output : BinString)
    (represented : ∃ program, U.compute program = some output) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](output) : ℤ))) ≤ prefixOutputMass U.compute output := by
  classical
  obtain ⟨program, computes, lengthEq⟩ :=
    Mettapedia.UniversalAI.SolomonoffPrior.exists_program_of_complexity U output represented
  unfold prefixOutputMass
  refine le_trans ?_ (ENNReal.le_tsum program)
  simp [prefixProgramWeight, computes, lengthEq, prefixComplexity]

/-- Only the outputs actually queried must be represented. -/
theorem sum_weightByKpf_le_one_on (U : PrefixFreeMachine) (s : Finset BinString)
    (represented : ∀ output ∈ s, ∃ program, U.compute program = some output) :
    (∑ output ∈ s, ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](output) : ℤ)))) ≤ 1 :=
  (Finset.sum_le_sum fun output member =>
    prefixComplexityWeight_le_outputMass U output (represented output member)).trans
      ((ENNReal.sum_le_tsum s).trans
        (prefixOutputMass_total_le_one U.compute (haltingPrograms_prefixFree U)))

/-- Finite Kraft bound for the weights `2^{-Kpf[U](x)}`. -/
theorem sum_weightByKpf_le_one (U : PrefixFreeMachine) [OutputComplete U] (s : Finset BinString) :
    (∑ x ∈ s, ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](x) : ℤ)))) ≤ 1 := by
  exact sum_weightByKpf_le_one_on U s (fun output _ => outputComplete_has_program U output)

/-- Finite Kraft bound, using `ENNReal` powers (matches Chapter 3 weights). -/
theorem sum_weightByKpf_le_one_ennreal (U : PrefixFreeMachine) [OutputComplete U] (s : Finset BinString) :
    (∑ x ∈ s, (2 : ENNReal) ^ (-(Kpf[U](x) : ℤ))) ≤ 1 := by
  simpa [two_zpow_neg_nat] using (sum_weightByKpf_le_one (U := U) s)

/-- Kraft/summability: `∑' x, 2^{-Kpf[U](x)} ≤ 1`. -/
theorem tsum_weightByKpf_le_one (U : PrefixFreeMachine) [OutputComplete U] :
    (∑' x : BinString, ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[U](x) : ℤ)))) ≤ 1 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (sum_weightByKpf_le_one U)

/-- Kraft/summability: `∑' x, 2^{-Kpf[U](x)} ≤ 1` using `ENNReal` powers. -/
theorem tsum_weightByKpf_le_one_ennreal (U : PrefixFreeMachine) [OutputComplete U] :
    (∑' x : BinString, (2 : ENNReal) ^ (-(Kpf[U](x) : ℤ))) ≤ 1 := by
  simpa only [← ofReal_two_zpow_neg_nat] using tsum_weightByKpf_le_one U

namespace Controls

/-- Two distinct one-bit descriptions may return the same or different outputs. -/
def bitMachine (output : Bool → BinString) : PrefixFreeMachine where
  compute p := if p = [false] then some (output false) else if p = [true] then some (output true) else none
  prefix_free := by
    intro p q pref different active
    split_ifs at active ⊢ <;> simp_all

@[simp] theorem bitMachine_map (output : Bool → BinString) (observe : BinString → BinString) (p : BinString) :
    ((bitMachine output).compute p).map observe = (bitMachine (observe ∘ output)).compute p := by
  dsimp only [bitMachine]
  split_ifs <;> rfl

theorem bitMachine_mass (output : Bool → BinString) (x : BinString) :
    prefixOutputMass (bitMachine output).compute x =
      (if output false = x then 1 / 2 else 0) + (if output true = x then 1 / 2 else 0) := by
  unfold prefixOutputMass
  rw [tsum_eq_sum (s := {[false], [true]})]
  · norm_num [bitMachine, prefixProgramWeight, ENNReal.ofReal_div_of_pos]
  · intro p absent
    simp_all [bitMachine]

theorem bitMachine_complexity (output : Bool → BinString) : Kpf[bitMachine output](output false) = 1 := by
  obtain ⟨p, computed, lengthEq⟩ := Mettapedia.UniversalAI.SolomonoffPrior.exists_program_of_complexity
    (bitMachine output) (output false) ⟨[false], rfl⟩
  have upper : Kpf[bitMachine output](output false) ≤ 1 :=
    Mettapedia.UniversalAI.SolomonoffPrior.complexity_le_program_length _ _ [false] rfl
  have nonempty : p ≠ [] := by rintro rfl; simp [bitMachine] at computed
  have positive := Nat.succ_le_of_lt (List.length_pos_iff.mpr nonempty)
  exact le_antisymm upper (by simpa only [prefixComplexity, lengthEq] using positive)

theorem shortest_weight_is_not_output_mass :
    prefixOutputMass (fun p => ((bitMachine (fun bit => [bit])).compute p).map (fun _ => ([] : BinString))) [] = 1 ∧
      ENNReal.ofReal ((2 : ℝ) ^ (-(Kpf[bitMachine (fun _ => [])]([]) : Int))) = 1 / 2 ∧
      prefixOutputMass (bitMachine (fun bit => [bit])).compute [false] = 1 / 2 := by
  norm_num [bitMachine_mass, bitMachine_complexity, ENNReal.ofReal_div_of_pos, ENNReal.inv_two_add_inv_two]

end Controls
end KolmogorovComplexity
