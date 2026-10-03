import MettapediaFourColor.FourTriangleCore
import MettapediaFourColor.ConfigurationRealization
import MettapediaFourColor.KempeBoundarySplit
import FourColor.CfQuiz

/-!
# Complete ten-port presentations of two four-triangle patches

D0051 and D0052 are exactly the embedded source graphs of classical
configurations 33 and 37. All dart permutations, all graph edges, all cyclic
stars, prescribed core degrees and the ordered ring are checked. The first
presentation agrees with the source orientation; the second reverses it.
The equivalence transports actual colouring witnesses and joint boundary traces.

The source data and MIT attribution are retained in `FourTriangleCore`.
The Y/H language and classical configurations are due to Gonthier and Werner,
through Chris Emery's MIT-licensed Lean port. No repair follows from this
representation theorem alone.
-/

namespace FourColor.FourTriangleConstruction

open ExecutableConfiguration ConfigurationTable ConfigurationFaceGraph

set_option maxRecDepth 32768
set_option linter.style.longLine false

def program : Fin 2 → List Step :=
  ![[.join, .rotate 3, .join, .rotate 9, .join, .rotate 9, .fork, .rotate 6, .join, .rotate 2, .join, .rotate 8, .fork, .rotate 6, .join, .rotate 1, .fork, .rotate 6, .fork, .rotate 4, .fork, .fork, .rotate 2, .fork, .rotate 2, .fork],
    [.join, .rotate 2, .join, .rotate 9, .fork, .rotate 7, .join, .rotate 1, .fork, .rotate 5, .join, .rotate 2, .join, .rotate 7, .fork, .rotate 6, .join, .rotate 6, .fork, .rotate 4, .fork, .rotate 2, .fork, .rotate 2, .fork, .rotate 1, .fork]]

def config : Fin 2 → Config := ![cf033, cf037]

theorem reference (p : Fin 2) : evaluate (program p) = cfmap (config p) := by
  have h := evaluate_eq (program p)
  have he : (program p).map Step.reference = (config p).prog := by clear h; revert p; decide +kernel
  simpa only [he, cfmap] using h

theorem size_eq : ∀ p, size (program p) = 70 := by decide +kernel

def numbering (p : Fin 2) : (evaluate (program p)).Dart ≃ Fin 70 :=
  (index (program p)).symm.trans (finCongr (size_eq p))

def numbered (p : Fin 2) : Hypermap (Fin 70) :=
  (evaluate (program p)).map.relabel (numbering p)

def edgeTable : Fin 2 → String :=
  !["! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbed",
    "! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbed"]

def nodeTable : Fin 2 → String :=
  !["%A!2#,+1'P)F&5-\\/($W3.;O7B9< E=T?\":XC>KSGLI6J`M8*_QH@[U4DcYV0e]RNdaZb^",
    "%9!,#&+/'P)J$X-(5E163 4W7\"?O;F=@0IATC2>_GB:SK\\M<*[QLDcU8.eYRN`]H^daVbZ"]

def faceTable : Fin 2 → String :=
  !["\"<$A 2(,*1&P.%05'\\4#-W8K:O6B>;@E!TD9=XH+JSFLNI7`R)G_V?3[ZCUc^/QebMYd]a",
    "\"5$9 ,(%*/&P.#'X2@4E0683!W<J>O:FB?DI1TH=A_L+NS;\\R)K[VC7cZ-Qe^MG`b]UdYa"]

def table (p : Fin 2) : Data 70 where
  base := 32
  edges := edgeTable p
  nodes := nodeTable p
  faces := faceTable p
  cancel := by revert p; decide +kernel

set_option maxHeartbeats 8000000 in
-- Compare all three dart permutations of both complete nested constructions.
/-- The entire nested construction agrees with its finite permutations. -/
theorem numbered_eq (p : Fin 2) : numbered p = (table p).map := by
  apply (table p).eq_of_tables
  revert p
  decide +kernel

def vertexTable : Fin 2 → String :=
  !["ABAOAJHIHKHGIJIMIKJOJMDEDNDCBCBPBOCNCPFGFLFEELENGKGLOPOMPNPMKMKLNLNMML",
    "CBCNCDEDEOEFDNDOAJAPABBPBNHGHKHIJIJLJPIKILGFGMGKFOFMPLPNONOMKMKLLMLNNM"]

def representativeTable : Fin 2 → String :=
  ![" !;67F+&'%)I/9#?",
    "0! %&+;:?1=CM#)3"]

def vertex (p : Fin 2) : Fin 70 → Fin 16 := lookup (vertexTable p)
def representative (p : Fin 2) : Fin 16 → Fin 70 := lookupBase 32 (representativeTable p)

def faces (p : Fin 2) : Presentation (table p).map (FourTriangleCore.input p).graph where
  vertex := vertex p
  representative := representative p
  vertex_rep := by revert p; decide +kernel
  vertex_face := by revert p; decide +kernel
  same_face := same_face_of_reaches (n := 7) (by revert p; decide +kernel)
  adjacent := by revert p; decide +kernel

def point : Fin 2 → Fin 70 := ![0,
    0]

def realization (p : Fin 2) : Realization (cfmap (config p)) (table p) (point p) :=
  reference p ▸
    ({ numbering := numbering p
       map_eq := numbered_eq p
       point_eq := by revert p; decide +kernel } :
      Realization (evaluate (program p)) (table p) (point p))

def ring : Fin 2 → List (Fin 70) :=
  ![[5, 0, 28, 27, 22, 43, 38, 11, 6, 12],
    [5, 0, 21, 16, 32, 31, 26, 42, 11, 6]]

def boundary : Fin 2 → List (Fin 16) :=
  ![[9, 0, 1, 2, 3, 4, 5, 6, 7, 8],
    [3, 2, 1, 0, 9, 8, 7, 6, 5, 4]]

theorem cpring (p : Fin 2) : (table p).map.cpring (point p) = ring p := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain
    revert p; decide +kernel
  · revert p; decide +kernel
  · revert p; decide +kernel
  · revert p; decide +kernel

theorem source_boundary : ∀ p, (ring p).map (vertex p) = boundary p := by
  decide +kernel

/-- The complete ordered assignment is retained, including orientation. -/
theorem boundary_alignment :
    boundary 0 = (FourTriangleCore.input 0).boundary.rotate 9 ∧
    boundary 1 = (FourTriangleCore.input 1).boundary.reverse.rotate 6 := by
  decide +kernel

/-- Actual colourings and their entire ordered boundary trace agree. -/
theorem ringTrace_iff (p : Fin 2) (et : List Color) :
    (cfmap (config p)).map.RingTrace (cfring (config p)).reverse et ↔
      KempeBoundarySplit.GraphTrace (FourTriangleCore.input p).graph (boundary p) et := by
  change (cfmap (config p)).map.RingTrace (cfmap (config p)).cpring.reverse.reverse et ↔ _
  rw [List.reverse_reverse, (realization p).forwardRingTrace, cpring, (faces p).ringTrace_iff]
  change (∃ k : (FourTriangleCore.input p).graph.Coloring Color,
    et = trace ((ring p).map (k ∘ vertex p))) ↔ _
  simp only [← List.map_map, source_boundary]
  rfl

/-- Boundary stars complete the published core rows by their facial triangles. -/
def stars (p : Fin 2) (v : Fin 16) : List (Fin 16) :=
  if h : v.val < 10 then
    (![![[1, 14, 9],
    [0, 2, 15, 14],
    [1, 3, 13, 15],
    [2, 4, 13],
    [3, 5, 11, 13],
    [4, 6, 11],
    [5, 7, 10, 11],
    [6, 8, 10],
    [7, 9, 12, 10],
    [0, 14, 12, 8]],
    ![[1, 15, 9],
    [0, 2, 13, 15],
    [1, 3, 13],
    [2, 4, 14, 13],
    [3, 5, 14],
    [4, 6, 12, 14],
    [5, 7, 10, 12],
    [6, 8, 10],
    [7, 9, 11, 10],
    [0, 15, 11, 8]]]) p ⟨v.val, h⟩
  else (FourTriangleCore.input p).internalStar v

def degree (p : Fin 2) (v : Fin 16) : ℕ := (stars p v).length

theorem stars_exact : ∀ p v, (stars p v).Nodup ∧
    ∀ w, w ∈ stars p v ↔ (FourTriangleCore.input p).graph.Adj v w := by decide +kernel

theorem core_degrees : ∀ p (i : Fin 6), degree p (i.natAdd 10) = FourTriangleCore.degree p i := by
  decide +kernel

def orientedStars (p : Fin 2) (v : Fin 16) : List (Fin 16) :=
  if p = 0 then stars p v else (stars p v).reverse

set_option maxHeartbeats 4000000 in
-- Check every cyclic star in both source presentations.
theorem source_rotation : ∀ (p : Fin 2) (v : Fin 16), ∃ shift : Fin 8,
    ConfigurationFaceGraph.star (table p).map (vertex p) (representative p) (degree p) v =
      (orientedStars p v).rotate shift.val := by
  decide +kernel

theorem quiz_right : ∀ p, (cfquiz (config p)).IsQuizR := by decide +kernel

/-- Both complete constructions satisfy the reference embeddability contract. -/
theorem embeddable (p : Fin 2) :
    (cfmap (config p)).map.Embeddable (cfring (config p)) :=
  embeddable_cfquiz (quiz_right p)

end FourColor.FourTriangleConstruction
