import MettapediaFourColor.D3009Wheel
import MettapediaFourColor.ConfigurationRealization
import MettapediaFourColor.KempeBoundarySplit
import FourColor.CfQuiz

/-!
# D3009 as an exact composition of elementary constructions

Eleven Y steps and eight H steps construct the complete thirteen-port source.
All three dart permutations, all source edges and cyclic stars, and the ordered
boundary trace are checked. The transport preserves actual colouring witnesses.
The construction theorem also proves the reference embeddability contract.

The Y/H language is due to Gonthier and Werner, in Chris Emery's Lean port.
D3009 and its MIT attribution are retained with `D3009Wheel.input`.
No colouring repair or coverage assertion is inferred from this construction.
-/

namespace FourColor.D3009Construction

open ExecutableConfiguration ConfigurationTable ConfigurationFaceGraph

set_option maxRecDepth 32768

def program : List Step :=
  [.join, .rotate 1, .join, .rotate 1, .fork, .rotate 10, .join, .rotate 11, .fork, .join,
   .rotate 10, .join, .rotate 10, .fork, .join, .rotate 9, .fork, .join, .rotate 8, .fork,
   .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .rotate 1,
   .fork, .fork]

def config : Config := ⟨false, [], program.map Step.reference⟩

theorem reference : evaluate program = cfmap config := evaluate_eq program

def table : Data 94 where
  base := 32
  edges := "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLON\
    QPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx{z}|"
  nodes := "%5!&#+$o',)/*^-Z 91k3\"0?726E;g=8:IAbC<@OGBFSK}MH\
    JYQLP]UwWRTa[V.s_\\Dxche>fli4jpm(ntq`r{uXd|yvzN"
  faces := "\"0$5 &(#*o%,.)+^2649!k8:1?<@>E7gBFDI;bHJAOLPNSG}\
    RTKYVZX]Qw\\/Ua`-[sdCfx=hje3lni'prm_tvqW{zcu|My"
  cancel := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Compare the complete nested construction with the finite permutation table once.
theorem numbered_eq : numbered program = table.map := by
  apply table.eq_of_tables
  decide +kernel

def vertex : Fin 94 → Fin 21 := lookup
  "BCBPBAAPARAMMRMLCDCQCPDEDQEFEOEQFGFUFOGHGUHIHTHU\
    IJITJKJSJTKLKSLRLSOUONOQQNQPPNPRRNRSSNSTNUNTTU"
def representative : Fin 21 → Fin 94 := lookupBase 32 "% !17;AGKQU/+e=#3)WMC"

def graph : SimpleGraph (Fin 21) :=
  ConfigurationFaceGraph.graph table.map vertex (by decide +kernel) (by decide +kernel)

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def faces : Presentation table.map graph where
  vertex := vertex
  representative := representative
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := same_face_of_reaches (n := 7) (by decide +kernel)
  adjacent := fun _ _ => Iff.rfl

theorem source_graph : graph = D3009Wheel.input.graph := by
  ext a b
  revert a b
  decide +kernel

def realization : Realization (cfmap config) table 0 :=
  reference ▸
    ({ numbering := (index program).symm
       map_eq := numbered_eq
       point_eq := by decide +kernel } : Realization (evaluate program) table 0)

def ring : List (Fin 94) := [5, 0, 16, 22, 26, 32, 38, 42, 48, 52, 58, 15, 11]

theorem cpring : table.map.cpring 0 = ring := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem source_boundary : ring.map vertex = D3009Wheel.input.boundary := by
  decide +kernel

/-- Actual colourings and their whole ordered boundary trace agree. -/
theorem ringTrace_iff (et : List Color) :
    (cfmap config).map.RingTrace (cfring config).reverse et ↔
      KempeBoundarySplit.GraphTrace D3009Wheel.input.graph
        D3009Wheel.input.boundary et := by
  change (cfmap config).map.RingTrace (cfmap config).cpring.reverse.reverse et ↔ _
  rw [List.reverse_reverse, realization.forwardRingTrace, cpring, faces.ringTrace_iff]
  change (∃ k : graph.Coloring Color, et = trace (ring.map (k ∘ vertex))) ↔ _
  simp only [← List.map_map, source_boundary]
  change KempeBoundarySplit.GraphTrace graph D3009Wheel.input.boundary et ↔ _
  rw [source_graph]

/-- Full source cyclic rows, including all boundary attachments. -/
def stars (v : Fin 21) : List (Fin 21) :=
  if h : v.val < 13 then
    ![[1, 15, 17, 12],
      [0, 2, 15],
      [1, 3, 16, 15],
      [2, 4, 16],
      [3, 5, 14, 16],
      [4, 6, 20, 14],
      [5, 7, 20],
      [6, 8, 19, 20],
      [7, 9, 19],
      [8, 10, 18, 19],
      [9, 11, 18],
      [10, 12, 17, 18],
      [0, 17, 11]] ⟨v.val, h⟩
  else D3009Wheel.input.internalStar v

def degree (v : Fin 21) : ℕ := (stars v).length

theorem source_rotation : ∀ v : Fin 21, ∃ shift : Fin 8,
    ConfigurationFaceGraph.star table.map vertex representative degree v =
      (stars v).rotate shift.val := by
  decide +kernel

theorem quiz_right : (cfquiz config).IsQuizR := by decide +kernel

/-- The source construction satisfies the reference's geometric contract. -/
theorem embeddable : (cfmap config).map.Embeddable (cfring config) :=
  embeddable_cfquiz quiz_right

end FourColor.D3009Construction
