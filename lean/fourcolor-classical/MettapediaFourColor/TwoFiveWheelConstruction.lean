import MettapediaFourColor.TwoFiveWheelData
import MettapediaFourColor.ConfigurationRealization
import FourColor.CfQuiz

/-!
# Exact twelve-port construction programs for the two-five wheel family

The six source programs preserve all dart permutations, full graph adjacency,
cyclic stars and the ordered boundary. Their actual colouring witnesses
transport through the same graph/face presentation theorem. No colouring
repair is inferred from the construction.

The Y/H language is due to Gonthier and Werner, through Chris Emery's
MIT-licensed Lean port. The wheel source attribution is in D3009Wheel.
-/

namespace FourColor.TwoFiveWheelConstruction

open ExecutableConfiguration ConfigurationTable ConfigurationFaceGraph

set_option maxRecDepth 32768
set_option linter.style.longLine false

def program : Fin 6 → List Step :=
  ![[.join, .rotate 1, .join, .rotate 1, .fork, .rotate 9, .join, .rotate 10, .fork, .join, .rotate 9, .join, .rotate 9, .join, .rotate 9, .fork, .join, .rotate 8, .fork, .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .fork],
    [.join, .rotate 1, .join, .rotate 1, .fork, .rotate 9, .join, .rotate 10, .fork, .join, .rotate 9, .join, .rotate 9, .fork, .join, .rotate 8, .join, .rotate 8, .fork, .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .fork],
    [.join, .rotate 1, .join, .rotate 1, .fork, .rotate 9, .join, .rotate 10, .fork, .join, .rotate 9, .join, .rotate 9, .fork, .join, .rotate 8, .fork, .join, .rotate 7, .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .fork],
    [.join, .rotate 1, .join, .rotate 10, .join, .rotate 11, .fork, .join, .rotate 10, .join, .rotate 10, .fork, .join, .rotate 9, .fork, .join, .rotate 8, .fork, .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .fork],
    [.rotate 11, .join, .rotate 1, .join, .rotate 1, .join, .rotate 1, .fork, .rotate 8, .join, .rotate 10, .join, .rotate 10, .fork, .join, .rotate 9, .fork, .join, .rotate 8, .fork, .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .fork],
    [.join, .rotate 1, .join, .rotate 1, .fork, .rotate 9, .join, .rotate 10, .join, .rotate 10, .join, .rotate 10, .fork, .join, .rotate 9, .fork, .join, .rotate 8, .fork, .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .rotate 1, .fork, .fork]]

def config (p : Fin 6) : Config := ⟨false, [], (program p).map Step.reference⟩

theorem reference (p : Fin 6) : evaluate (program p) = cfmap (config p) := evaluate_eq _

theorem size_eq : ∀ p, size (program p) = 90 := by decide +kernel

def numbering (p : Fin 6) : (evaluate (program p)).Dart ≃ Fin 90 :=
  (index (program p)).symm.trans (finCongr (size_eq p))

def numbered (p : Fin 6) : Hypermap (Fin 90) :=
  (evaluate (program p)).map.relabel (numbering p)

def edgeTable : Fin 6 → String :=
  !["! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx",
    "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx",
    "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx",
    "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx",
    "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx",
    "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx"]

def nodeTable : Fin 6 → String :=
  !["%5!&#+$k',)/*Z-V 91g3\"0?726E;c=8:KA^C<@OGyIBFUMHLYQsSNP]WR.o[XDt_da>bhe4fli(jpm\\nwqT`xurvJ",
    "%5!&#+$k',)/*Z-V 91g3\"0?726E;c=8:IA^C<@OGBFUKyMHJYQsSLP]WR.o[XDt_da>bhe4fli(jpm\\nwqT`xurvN",
    "%5!&#+$k',)/*Z-T 91g3\"0?726E;c=8:IA^C<@OGBFSKyMHJYQLP]UsWR.o[VDt_da>bhe4fli(jpm\\nwqX`xurvN",
    "%1!&#+$k'Z)V 5-g/\",;3.2A7c946E=^?8<KC>BOGyIDFUMHLYQsSNP]WR*o[X@t_da:bhe0fli(jpm\\nwqT`xurvJ",
    "%;!&#+$g',)1*k-2/50Z3V A7c9\"6E=^?8<KC>BOGyIDFUMHLYQsSNP]WR4o[X@t_da:bhe(fli.jpm\\nwqT`xurvJ",
    "%5!&#+$k',)/*Z-V ;1g3\"0A7c926E=^?8<KC>BOGyIDFUMHLYQsSNP]WR.o[X@t_da:bhe4fli(jpm\\nwqT`xurvJ"]

def faceTable : Fin 6 → String :=
  !["\"0$5 &(#*k%,.)+Z2649!g8:1?<@>E7cBFDK;^HLJOAyNPGURVTYMsX/Q]\\-Wo`Cbt=dfa3hje'lni[prmSwv_qxIu",
    "\"0$5 &(#*k%,.)+Z2649!g8:1?<@>E7cBFDI;^HJAOLPNUGyRVTYKsX/Q]\\-Wo`Cbt=dfa3hje'lni[prmSwv_qxMu",
    "\"0$5 &(#*k%,.)+Z2649!g8:1?<@>E7cBFDI;^HJAOLPNSGyRTKYV/X]Qs\\-Uo`Cbt=dfa3hje'lni[prmWwv_qxMu",
    "\",$1 &(#*k%Z.205!g46-;8<:A3c>B@E7^DF=KHLJOCyNPGURVTYMsX+Q]\\)Wo`?bt9dfa/hje'lni[prmSwv_qxIu",
    "\"6$; &(#*g%,.)0k+24/1Z8<:A!c>B@E7^DF=KHLJOCyNPGURVTYMsX5Q]\\3Wo`?bt9dfa'hje-lni[prmSwv_qxIu",
    "\"0$5 &(#*k%,.)+Z264;!g8<:A1c>B@E7^DF=KHLJOCyNPGURVTYMsX/Q]\\-Wo`?bt9dfa3hje'lni[prmSwv_qxIu"]

def table (p : Fin 6) : Data 90 where
  base := 32
  edges := edgeTable p
  nodes := nodeTable p
  faces := faceTable p
  cancel := by revert p; decide +kernel

set_option maxHeartbeats 32000000 in
/-- Each entire construction agrees with its finite permutation presentation. -/
theorem numbered_eq (p : Fin 6) : numbered p = (table p).map := by
  apply (table p).eq_of_tables
  revert p
  decide +kernel

def vertexTable : Fin 6 → String :=
  !["BCBOBAAOAQALLQLKCDCPCODEDPEFENEPFGFTFNGHGSGTHIHSIJIRISJKJRKQKRNTNMNPPMPOOMOQQMQRRMRSMTMSST",
    "BCBOBAAOAQALLQLKCDCPCODEDPEFENEPFGFTFNGHGTHIHSHTIJIRISJKJRKQKRNTNMNPPMPOOMOQQMQRRMRSMTMSST",
    "BCBOBAAOAQALLQLKCDCPCODEDPEFENEPFGFTFNGHGTHIHSHTIJISJKJRJSKQKRNTNMNPPMPOOMOQQMQRRMRSMTMSST",
    "BCBOBAAOAQALCDCPCODEDPEFENEPFGFTFNGHGTHIHSHTIJISJKJRJSKLKRLQLRNTNMNPPMPOOMOQQMQRRMRSMTMSST",
    "CDCPCBBPBOBAAOAQALLQLKDEDNDPEFETENFGFTGHGSGTHIHSIJIRISJKJRKQKRNTNMNPPMPOOMOQQMQRRMRSMTMSST",
    "BCBOBAAOAQALLQLKCDCPCODEDNDPEFETENFGFTGHGSGTHIHSIJIRISJKJRKQKRNTNMNPPMPOOMOQQMQRRMRSMTMSST"]

def representativeTable : Fin 6 → String :=
  !["% !17;AGMQ/+a=#3)SIC",
    "% !17;AGKQ/+a=#3)SMC",
    "% !17;AGKQ/+a=#3)WMC",
    "% !-37=CGMQ+a9#/)SI?",
    "+% !7=CGMQ51a9)#/SI?",
    "% !17=CGMQ/+a9#3)SI?"]

def vertex (p : Fin 6) : Fin 90 → Fin 20 := lookup (vertexTable p)
def representative (p : Fin 6) : Fin 20 → Fin 90 := lookupBase 32 (representativeTable p)

def graph (p : Fin 6) : SimpleGraph (Fin 20) :=
  ConfigurationFaceGraph.graph (table p).map (vertex p)
    (by revert p; decide +kernel) (by revert p; decide +kernel)

instance (p : Fin 6) : DecidableRel (graph p).Adj := by unfold graph; infer_instance

def faces (p : Fin 6) : Presentation (table p).map (graph p) where
  vertex := vertex p
  representative := representative p
  vertex_rep := by revert p; decide +kernel
  vertex_face := by revert p; decide +kernel
  same_face := same_face_of_reaches (n := 7) (by revert p; decide +kernel)
  adjacent := fun _ _ => Iff.rfl

set_option maxHeartbeats 4000000 in
theorem source_graph (p : Fin 6) : graph p = (TwoFiveWheelData.input p).graph := by
  ext a b
  revert p a b
  decide +kernel

def point : Fin 6 → Fin 90 := ![0,
    0,
    0,
    0,
    5,
    0]

def realization (p : Fin 6) : Realization (cfmap (config p)) (table p) (point p) :=
  reference p ▸
    ({ numbering := numbering p
       map_eq := numbered_eq p
       point_eq := by revert p; decide +kernel } :
      Realization (evaluate (program p)) (table p) (point p))

def ring : Fin 6 → List (Fin 90) :=
  ![[5, 0, 16, 22, 26, 32, 38, 44, 48, 54, 15, 11],
    [5, 0, 16, 22, 26, 32, 38, 42, 48, 54, 15, 11],
    [5, 0, 16, 22, 26, 32, 38, 42, 48, 52, 15, 11],
    [5, 0, 12, 18, 22, 28, 34, 38, 44, 48, 54, 11],
    [11, 5, 0, 22, 28, 34, 38, 44, 48, 54, 21, 17],
    [5, 0, 16, 22, 28, 34, 38, 44, 48, 54, 15, 11]]

theorem cpring (p : Fin 6) : (table p).map.cpring (point p) = ring p := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain
    revert p; decide +kernel
  · revert p; decide +kernel
  · revert p; decide +kernel
  · revert p; decide +kernel

theorem source_boundary : ∀ p, (ring p).map (vertex p) = (TwoFiveWheelData.input p).boundary := by
  decide +kernel

/-- Actual colourings and their entire ordered boundary trace agree. -/
theorem ringTrace_iff (p : Fin 6) (et : List Color) :
    (cfmap (config p)).map.RingTrace (cfring (config p)).reverse et ↔
      KempeBoundarySplit.GraphTrace (TwoFiveWheelData.input p).graph
        (TwoFiveWheelData.input p).boundary et := by
  change (cfmap (config p)).map.RingTrace (cfmap (config p)).cpring.reverse.reverse et ↔ _
  rw [List.reverse_reverse, (realization p).forwardRingTrace, cpring, (faces p).ringTrace_iff]
  change (∃ k : (graph p).Coloring Color, et = trace ((ring p).map (k ∘ vertex p))) ↔ _
  simp only [← List.map_map, source_boundary]
  change KempeBoundarySplit.GraphTrace (graph p) (TwoFiveWheelData.input p).boundary et ↔ _
  rw [source_graph]

def degree (p : Fin 6) (v : Fin 20) : ℕ := (TwoFiveWheelData.stars p v).length

set_option maxHeartbeats 4000000 in
theorem source_rotation : ∀ (p : Fin 6) (v : Fin 20), ∃ shift : Fin 8,
    ConfigurationFaceGraph.star (table p).map (vertex p) (representative p) (degree p) v =
      (TwoFiveWheelData.stars p v).rotate shift.val := by
  decide +kernel

theorem quiz_right : ∀ p, (cfquiz (config p)).IsQuizR := by decide +kernel

/-- All six actual constructions satisfy the reference embeddability contract. -/
theorem embeddable (p : Fin 6) :
    (cfmap (config p)).map.Embeddable (cfring (config p)) :=
  embeddable_cfquiz (quiz_right p)

end FourColor.TwoFiveWheelConstruction
