import MettapediaFourColor.ExceptionalCore
import MettapediaFourColor.ConfigurationRealization
import MettapediaFourColor.KempeBoundarySplit
import FourColor.CfQuiz

/-!
# D1774 as a composition of elementary configuration operations

Nine Y steps and eight H steps construct the full source completion. The
finite comparison retains all three dart permutations. Face naming then
recovers every source edge, every cyclic core star and the ordered ring.
The established configuration construction theorem supplies embeddability.

The Y/H construction language is due to Gonthier and Werner, as formalized
by Chris Emery. The D1774 source and its MIT attribution are retained with
`ExceptionalCore.input`.
-/

namespace FourColor.ExceptionalConstruction

open ExecutableConfiguration ConfigurationTable ConfigurationFaceGraph

set_option maxRecDepth 32768

def program : List Step :=
  [.rotate 1, .join, .rotate 9, .join, .rotate 1, .join, .rotate 9, .join,
   .rotate 10, .fork, .rotate 2, .fork, .rotate 7, .join, .rotate 1, .join,
   .rotate 7, .join, .rotate 1, .fork, .rotate 7, .join, .rotate 7, .fork,
   .fork, .rotate 2, .fork, .rotate 1, .fork, .rotate 1, .fork, .fork]

def config : Config := ⟨false, [], program.map Step.reference⟩

theorem reference : evaluate program = cfmap config := evaluate_eq program

def table : Data 86 where
  base := 32
  edges := "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQP\
    SRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrut"
  nodes := "%1!`#\\+7',) *?-u/\"&;3<5(2K946o=.EQAFC8DUGkI:@[MR\
    OBPgSHL_WdYNVc]X$pa^ZheTfliJjsm>btqnr0"
  faces := "\"+$1 `(2*7&,.)0?!u486;'<:E3K>5-oBLDQ@FHCJU9kNVP[AR\
    TOGgX\\Z_Md^%Wcb#]pfYShjeIlni=sramt/q"
  cancel := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Compare the nested program once; later consumers use the finite map.
theorem numbered_eq : numbered program = table.map := by
  apply table.eq_of_tables
  decide +kernel

def vertex : Fin 86 → Fin 19 := lookup
  "ABASAKCDCNCBBNBQBSDEDODNEFEONONQGHGMGFFMFRFOHIHPHMMPMRIJILIPJKJLKSKLPLPRRLROOLOQLSLQQS"
def representative : Fin 19 → Fin 86 := lookupBase 32 " !&'39@AMW%YC)5O/I#"

def graph : SimpleGraph (Fin 19) :=
  ConfigurationFaceGraph.graph table.map vertex (by decide +kernel) (by decide +kernel)

instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def faces : Presentation table.map graph where
  vertex := vertex
  representative := representative
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := same_face_of_reaches (n := 8) (by decide +kernel)
  adjacent := fun _ _ => Iff.rfl

theorem source_graph : graph = ExceptionalCore.input.graph := by
  ext a b
  revert a b
  decide +kernel

def realization : Realization (cfmap config) table 11 :=
  reference ▸
    ({ numbering := (index program).symm
       map_eq := numbered_eq
       point_eq := by decide +kernel } : Realization (evaluate program) table 11)

def ring : List (Fin 86) := [0, 11, 6, 18, 24, 37, 32, 44, 54, 60, 5]

theorem cpring : table.map.cpring 11 = ring := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem source_boundary : ring.map vertex = ExceptionalCore.input.boundary := by
  decide +kernel

/-- Actual colourings and their whole ordered boundary trace agree. -/
theorem ringTrace_iff (et : List Color) :
    (cfmap config).map.RingTrace (cfring config).reverse et ↔
      KempeBoundarySplit.GraphTrace ExceptionalCore.input.graph
        ExceptionalCore.input.boundary et := by
  change (cfmap config).map.RingTrace (cfmap config).cpring.reverse.reverse et ↔ _
  rw [List.reverse_reverse, realization.forwardRingTrace, cpring, faces.ringTrace_iff]
  change (∃ k : graph.Coloring Color, et = trace (ring.map (k ∘ vertex))) ↔ _
  simp only [← List.map_map, source_boundary]
  change KempeBoundarySplit.GraphTrace graph ExceptionalCore.input.boundary et ↔ _
  rw [source_graph]

/-- Full source cyclic rows, including all boundary attachments. -/
def stars (v : Fin 19) : List (Fin 19) :=
  if h : v.val < 11 then
    ![[1, 18, 10],
    [0, 2, 13, 16, 18],
    [1, 3, 13],
    [2, 4, 14, 13],
    [3, 5, 14],
    [4, 6, 12, 17, 14],
    [5, 7, 12],
    [6, 8, 15, 12],
    [7, 9, 11, 15],
    [8, 10, 11],
    [0, 18, 11, 9]] ⟨v.val, h⟩
  else ExceptionalCore.input.internalStar v

def degree (v : Fin 19) : ℕ := (stars v).length

theorem source_rotation : ∀ v : Fin 19, ∃ shift : Fin 8,
    ConfigurationFaceGraph.star table.map vertex representative degree v =
      (stars v).rotate shift.val := by
  decide +kernel

/-- The eight local degree observations compiled from the construction. -/
def query : Quiz :=
  ⟨.askR .qa5 .ask0,
   .askR .qa5 (.askR .qa8 (.askLR .qa7
     (.askL .qa5 (.askR .qa5 (.ask1 .qa5))) (.ask1 .qa5)))⟩

theorem compiled_query : cfquiz config = query := by decide +kernel

theorem query_degrees : query.flat = [5, 5, 8, 7, 5, 5, 5, 5] := rfl

theorem quiz_right : (cfquiz config).IsQuizR := by
  rw [compiled_query]
  exact ⟨trivial, trivial⟩

/-- The source construction satisfies the reference's geometric contract. -/
theorem embeddable : (cfmap config).map.Embeddable (cfring config) :=
  embeddable_cfquiz quiz_right

end FourColor.ExceptionalConstruction
