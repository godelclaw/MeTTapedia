import MettapediaFourColor.NearLinearChainData
import FourColor.CfQuiz

/-!
# The three-triangle chain as an exact configuration construction

Six Y steps and five H steps construct the D0004 disk. The complete dart
permutations and ordered face boundary are checked against the source graph.
The Y/H language and its embeddability theorem are due to Gonthier and Werner,
ported to Lean by Chris Emery; source attribution is retained in the dependency.
-/

namespace FourColor.NearLinearChainConstruction

open ExecutableConfiguration ConfigurationTable ConfigurationFaceGraph
open NearLinearChainData

set_option maxRecDepth 32768

def program : List Step := [.join, .rotate 1, .join, .rotate 1, .join, .rotate 1, .fork, .rotate 1, .join, .rotate 6, .fork, .rotate 2, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 3, .fork, .fork]

def config : Config := ⟨false, [], program.map Step.reference⟩

theorem reference : evaluate program = cfmap config := evaluate_eq program

def table : Data 56 where
  edges := "BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badcfehgjilknmporqtsvuxw"
  nodes := "FnBGDLEsHMJRK]NSPVQWT\\U`XaZfOo^Y[rbgdjekhAixlC_vpcIwtqum"
  faces := "CjEnAGIDKsFMOJQ]LSUPRWYT[`Va_NXocZer\\gidfkmhBxq^bvuHpwlt"
  cancel := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Compare the complete construction; later consumers use the finite table.
theorem numbered_eq : numbered program = table.map := by
  apply table.eq_of_tables
  decide +kernel

def vertex : Fin 56 → Fin 13 := lookup "AHAMABBMBJBCCJCICDDIDEEIEKEFIJIKFKFLFGGLGHHLHMKJKLJMJLLM"
def representative : Fin 13 → Fin 56 := lookup "AFLRV\\fBPJZdD"

def faces : Presentation table.map input0004.graph where
  vertex := vertex
  representative := representative
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := same_face_of_reaches (n := 6) (by decide +kernel)
  adjacent := by decide +kernel

def realization : Realization (cfmap config) table 0 :=
  reference ▸
    ({ numbering := (index program).symm
       map_eq := numbered_eq
       point_eq := by decide +kernel } : Realization (evaluate program) table 0)

def ring : List (Fin 56) := [5, 0, 41, 37, 27, 21, 17, 11]
def boundary : List (Fin 13) := [1, 0, 7, 6, 5, 4, 3, 2]

theorem cpring : table.map.cpring 0 = ring := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem source_boundary : ring.map vertex = boundary := by decide +kernel

theorem ringTrace_iff (et : List Color) :
    (cfmap config).map.RingTrace (cfring config).reverse et ↔
      KempeBoundarySplit.GraphTrace input0004.graph boundary et := by
  change (cfmap config).map.RingTrace (cfmap config).cpring.reverse.reverse et ↔ _
  rw [List.reverse_reverse, realization.forwardRingTrace, cpring, faces.ringTrace_iff]
  rfl

theorem boundary_alignment : boundary.rotate 2 = boundary0004 := by decide +kernel

def degree (v : Fin 13) : ℕ := (stars0004 v).length

theorem source_rotation : ∀ v : Fin 13, ∃ shift : Fin 6,
    ConfigurationFaceGraph.star table.map vertex representative degree v =
      ((stars0004 v).reverse).rotate shift.val := by decide +kernel

theorem quiz_right : (cfquiz config).IsQuizR := by decide +kernel

theorem embeddable : (cfmap config).map.Embeddable (cfring config) :=
  embeddable_cfquiz quiz_right

end FourColor.NearLinearChainConstruction
