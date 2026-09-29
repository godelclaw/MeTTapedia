import MettapediaFourColor.ConfigurationRealization
import MettapediaFourColor.ConfigurationFaceGraph
import FourColor.Configurations

/-!
# Exact finite presentations of the diamond configurations

The three permutation tables below are checked against the actual reference
program maps. All certificates are verified by kernel reduction. The finite
tables expose the embedded maps without changing their graph or boundary.
-/

namespace FourColor.DiamondConfigurations

open ExecutableConfiguration ConfigurationTable

def program001 : List Step :=
  [.join, .rotate 3, .join, .rotate 5, .join, .rotate 5, .fork, .rotate 4,
    .join, .rotate 4, .fork, .rotate 2, .fork, .rotate 1, .fork]

theorem reference001 : evaluate program001 = cfmap cf001 :=
  evaluate_eq program001

def table001 : Data 42 where
  edges := "BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badcfehgji"
  nodes := "F\\BSDMLRH]JWGVNhPIEdTOA`XaZCKj^Y[ebUcifQg_"
  faces := "CWE\\ASIMKRG]OFQVHhUDNdYL[`Ba_JXjcZTegbPi^f"
  cancel := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Reduce the nested program once to a finite table for all later checks.
theorem numbered001 : numbered program001 = table001.map := by
  apply table001.eq_of_tables
  decide +kernel

def program002 : List Step :=
  [.join, .rotate 2, .join, .rotate 6, .fork, .rotate 4, .join, .rotate 1,
    .fork, .rotate 4, .join, .rotate 4, .fork, .rotate 2, .fork, .fork]

theorem reference002 : evaluate program002 = cfmap cf002 :=
  evaluate_eq program002

def table002 : Data 46 where
  edges := "BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badcfehgjilknm"
  nodes := "FZBMDGLPHaJ[EnNIV`RWTAUhXCQd\\e^SKib]_lfYcmjgkO"
  faces := "CVEZAMIFKPGaODHnS[U`QWYTBh]L_dRecJ\\ig^XlkbfmNj"
  cancel := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Reduce the nested program once to a finite table for all later checks.
theorem numbered002 : numbered program002 = table002.map := by
  apply table002.eq_of_tables
  decide +kernel

def program004 : List Step :=
  [.join, .rotate 2, .join, .rotate 7, .fork, .rotate 5, .join, .rotate 1,
    .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 4, .fork, .rotate 2, .fork, .rotate 2, .fork]

theorem reference004 : evaluate program004 = cfmap cf004 :=
  evaluate_eq program004

def table004 : Data 50 where
  edges := "BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badcfehgjilknmporq"
  nodes := "FZBMDGLPHeJ[EmNIVdRWTAUlXC`h\\a^Q_ibSKpf]crjYOqngok"
  faces := "CVEZAMIFKPGeODHmS`UdQWYTBl]L_h[ac^RigJ\\pkbXroNfqjn"
  cancel := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Reduce the nested program once to a finite table for all later checks.
theorem numbered004 : numbered program004 = table004.map := by
  apply table004.eq_of_tables
  decide +kernel

def vertex001 : Fin 42 → Fin 10 := lookup "FAFJFECDCHCBDEDIDHEJEIABAGAJBHBGJGJIIGIHHG"
def representative001 : Fin 10 → Fin 42 := lookup "BLGHFAZJPD"

def graph001 : SimpleGraph (Fin 10) :=
  ConfigurationFaceGraph.graph table001.map vertex001
    (by decide +kernel) (by decide +kernel)

instance : DecidableRel graph001.Adj := by
  unfold graph001
  infer_instance

def faces001 : ConfigurationFaceGraph.Presentation table001.map graph001 where
  vertex := vertex001
  representative := representative001
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := ConfigurationFaceGraph.same_face_of_reaches
    (n := 8) (by decide +kernel)
  adjacent := fun _ _ => Iff.rfl

def realization001 : Realization (cfmap cf001) table001 0 :=
  reference001 ▸
    ({ numbering := (index program001).symm
       map_eq := numbered001
       point_eq := by decide +kernel } : Realization (evaluate program001) table001 0)

def ring001 : List (Fin 42) := [5, 0, 22, 11, 6, 12]
def boundary001 : List (Fin 10) := [3, 2, 1, 0, 5, 4]

theorem cpring001 : table001.map.cpring 0 = ring001 := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem ringTrace001 (et : List Color) :
    (cfmap cf001).map.RingTrace (cfring cf001) et ↔
      ∃ k : graph001.Coloring Color, et = trace (boundary001.map k) := by
  rw [cfring, realization001.ringTrace, cpring001, faces001.ringTrace_iff]
  rfl

def vertex002 : Fin 46 → Fin 11 := lookup "BCBHBAGAGKGFAHAKDEDIDCCICHEFEJEIFKFJIJIHJKJHHK"
def representative002 : Fin 11 → Fin 46 := lookup "FABQRLGDT^J"

def graph002 : SimpleGraph (Fin 11) :=
  ConfigurationFaceGraph.graph table002.map vertex002
    (by decide +kernel) (by decide +kernel)

instance : DecidableRel graph002.Adj := by
  unfold graph002
  infer_instance

def faces002 : ConfigurationFaceGraph.Presentation table002.map graph002 where
  vertex := vertex002
  representative := representative002
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := ConfigurationFaceGraph.same_face_of_reaches
    (n := 8) (by decide +kernel)
  adjacent := fun _ _ => Iff.rfl

def realization002 : Realization (cfmap cf002) table002 0 :=
  reference002 ▸
    ({ numbering := (index program002).symm
       map_eq := numbered002
       point_eq := by decide +kernel } : Realization (evaluate program002) table002 0)

def ring002 : List (Fin 46) := [5, 0, 21, 16, 26, 11, 6]
def boundary002 : List (Fin 11) := [6, 5, 4, 3, 2, 1, 0]

theorem cpring002 : table002.map.cpring 0 = ring002 := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem ringTrace002 (et : List Color) :
    (cfmap cf002).map.RingTrace (cfring cf002) et ↔
      ∃ k : graph002.Coloring Color, et = trace (boundary002.map k) := by
  rw [cfring, realization002.ringTrace, cpring002, faces002.ringTrace_iff]
  rfl

def vertex004 : Fin 50 → Fin 12 := lookup "FGFKFEDEDJDCEKEJHAHLHGGLGKBCBIBAAIALCJCILILKJKJIIK"
def representative004 : Fin 12 → Fin 50 := lookup "R[LGFABQ^JDT"

def graph004 : SimpleGraph (Fin 12) :=
  ConfigurationFaceGraph.graph table004.map vertex004
    (by decide +kernel) (by decide +kernel)

instance : DecidableRel graph004.Adj := by
  unfold graph004
  infer_instance

def faces004 : ConfigurationFaceGraph.Presentation table004.map graph004 where
  vertex := vertex004
  representative := representative004
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := ConfigurationFaceGraph.same_face_of_reaches
    (n := 8) (by decide +kernel)
  adjacent := fun _ _ => Iff.rfl

def realization004 : Realization (cfmap cf004) table004 0 :=
  reference004 ▸
    ({ numbering := (index program004).symm
       map_eq := numbered004
       point_eq := by decide +kernel } : Realization (evaluate program004) table004 0)

def ring004 : List (Fin 50) := [5, 0, 21, 16, 31, 26, 11, 6]
def boundary004 : List (Fin 12) := [3, 2, 1, 0, 7, 6, 5, 4]

theorem cpring004 : table004.map.cpring 0 = ring004 := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem ringTrace004 (et : List Color) :
    (cfmap cf004).map.RingTrace (cfring cf004) et ↔
      ∃ k : graph004.Coloring Color, et = trace (boundary004.map k) := by
  rw [cfring, realization004.ringTrace, cpring004, faces004.ringTrace_iff]
  rfl

def degree001 (v : Fin 10) : ℕ := entry "EEDEEDFFFF" v.val

def stars001 : Fin 10 → List (Fin 10) :=
  ConfigurationFaceGraph.star table001.map vertex001 representative001 degree001

theorem faceOrbit001 (v : Fin 10) :
    ConfigurationFaceGraph.faceCycle table001.map (representative001 v) (degree001 v) =
      orbitList table001.map.face (representative001 v) := by
  apply ConfigurationFaceGraph.faceCycle_eq_orbit
  · revert v; unfold IsCyclicChain; decide +kernel
  · revert v; decide +kernel
  · revert v; decide +kernel
  · revert v; decide +kernel

noncomputable def coloring001 : graph001.Coloring (Fin 4) ≃
    {k : (cfmap cf001).Dart → Color // (cfmap cf001).map.Coloring k} :=
  (SimpleGraph.recolorOfEquiv graph001 ConfigurationFaceGraph.colorEquiv).trans
    (faces001.coloringEquiv.trans realization001.coloringEquiv.symm)

def degree002 (v : Fin 11) : ℕ := entry "EDEDEEDGFFF" v.val

def stars002 : Fin 11 → List (Fin 11) :=
  ConfigurationFaceGraph.star table002.map vertex002 representative002 degree002

theorem faceOrbit002 (v : Fin 11) :
    ConfigurationFaceGraph.faceCycle table002.map (representative002 v) (degree002 v) =
      orbitList table002.map.face (representative002 v) := by
  apply ConfigurationFaceGraph.faceCycle_eq_orbit
  · revert v; unfold IsCyclicChain; decide +kernel
  · revert v; decide +kernel
  · revert v; decide +kernel
  · revert v; decide +kernel

noncomputable def coloring002 : graph002.Coloring (Fin 4) ≃
    {k : (cfmap cf002).Dart → Color // (cfmap cf002).map.Coloring k} :=
  (SimpleGraph.recolorOfEquiv graph002 ConfigurationFaceGraph.colorEquiv).trans
    (faces002.coloringEquiv.trans realization002.coloringEquiv.symm)

def degree004 (v : Fin 12) : ℕ := entry "EDEDEDEDGFGF" v.val

def stars004 : Fin 12 → List (Fin 12) :=
  ConfigurationFaceGraph.star table004.map vertex004 representative004 degree004

theorem faceOrbit004 (v : Fin 12) :
    ConfigurationFaceGraph.faceCycle table004.map (representative004 v) (degree004 v) =
      orbitList table004.map.face (representative004 v) := by
  apply ConfigurationFaceGraph.faceCycle_eq_orbit
  · revert v; unfold IsCyclicChain; decide +kernel
  · revert v; decide +kernel
  · revert v; decide +kernel
  · revert v; decide +kernel

noncomputable def coloring004 : graph004.Coloring (Fin 4) ≃
    {k : (cfmap cf004).Dart → Color // (cfmap cf004).map.Coloring k} :=
  (SimpleGraph.recolorOfEquiv graph004 ConfigurationFaceGraph.colorEquiv).trans
    (faces004.coloringEquiv.trans realization004.coloringEquiv.symm)


/-- The orientation consumed by classical reducibility. -/
theorem reducibilityTrace001 (et : List Color) :
    (cfmap cf001).map.RingTrace (cfring cf001).reverse et ↔
      ∃ k : graph001.Coloring Color, et = trace (boundary001.reverse.map k) := by
  rw [cfring, List.reverse_reverse, realization001.forwardRingTrace,
    cpring001, faces001.ringTrace_iff]
  rfl

/-- The orientation consumed by classical reducibility. -/
theorem reducibilityTrace002 (et : List Color) :
    (cfmap cf002).map.RingTrace (cfring cf002).reverse et ↔
      ∃ k : graph002.Coloring Color, et = trace (boundary002.reverse.map k) := by
  rw [cfring, List.reverse_reverse, realization002.forwardRingTrace,
    cpring002, faces002.ringTrace_iff]
  rfl

/-- The orientation consumed by classical reducibility. -/
theorem reducibilityTrace004 (et : List Color) :
    (cfmap cf004).map.RingTrace (cfring cf004).reverse et ↔
      ∃ k : graph004.Coloring Color, et = trace (boundary004.reverse.map k) := by
  rw [cfring, List.reverse_reverse, realization004.forwardRingTrace,
    cpring004, faces004.ringTrace_iff]
  rfl

/-- The common internal graph is the complete graph on four vertices with
the edge between vertices one and three deleted. -/
def diamondCore : SimpleGraph (Fin 4) where
  Adj i j := i ≠ j ∧ ¬ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel diamondCore.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ¬ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))))

/-- The remaining four vertices after the six ring vertices form the diamond. -/
theorem core001 : ∀ i j : Fin 4,
    graph001.Adj (i.natAdd 6) (j.natAdd 6) ↔ diamondCore.Adj i j := by
  decide +kernel

theorem core002 : ∀ i j : Fin 4,
    graph002.Adj (i.natAdd 7) (j.natAdd 7) ↔ diamondCore.Adj i j := by
  decide +kernel

theorem core004 : ∀ i j : Fin 4,
    graph004.Adj (i.natAdd 8) (j.natAdd 8) ↔ diamondCore.Adj i j := by
  decide +kernel

end FourColor.DiamondConfigurations
