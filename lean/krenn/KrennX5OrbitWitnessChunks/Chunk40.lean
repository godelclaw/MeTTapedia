import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk40

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨295, .swap23, .p021⟩, ⟨294, .swap23, .p021⟩, ⟨298, .swap23, .p021⟩, ⟨299, .swap23, .p021⟩, ⟨296, .swap23, .p021⟩, ⟨297, .swap23, .p021⟩, ⟨301, .swap23, .p021⟩, ⟨300, .swap23, .p021⟩, ⟨304, .swap23, .p021⟩, ⟨305, .swap23, .p021⟩, ⟨302, .swap23, .p021⟩, ⟨303, .swap23, .p021⟩,
    ⟨247, .swap24, .p021⟩, ⟨246, .swap24, .p021⟩, ⟨250, .swap24, .p021⟩, ⟨251, .swap24, .p021⟩, ⟨248, .swap24, .p021⟩, ⟨249, .swap24, .p021⟩, ⟨283, .swap24, .p021⟩, ⟨282, .swap24, .p021⟩, ⟨286, .swap24, .p021⟩, ⟨287, .swap24, .p021⟩, ⟨284, .swap24, .p021⟩, ⟨285, .swap24, .p021⟩,
    ⟨151, .swap24, .p021⟩, ⟨150, .swap24, .p021⟩, ⟨154, .swap24, .p021⟩, ⟨155, .swap24, .p021⟩, ⟨152, .swap24, .p021⟩, ⟨153, .swap24, .p021⟩, ⟨61, .swap24, .p021⟩, ⟨60, .swap24, .p021⟩, ⟨64, .swap24, .p021⟩, ⟨65, .swap24, .p021⟩, ⟨62, .swap24, .p021⟩, ⟨63, .swap24, .p021⟩,
    ⟨205, .cycle234, .p021⟩, ⟨204, .cycle234, .p021⟩, ⟨208, .cycle234, .p021⟩, ⟨209, .cycle234, .p021⟩, ⟨206, .cycle234, .p021⟩, ⟨207, .cycle234, .p021⟩, ⟨211, .swap23, .p021⟩, ⟨210, .swap23, .p021⟩, ⟨214, .swap23, .p021⟩, ⟨215, .swap23, .p021⟩, ⟨212, .swap23, .p021⟩, ⟨213, .swap23, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1920) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1920 ≤ case.val)
    (upper : case.val < 1968) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1920 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1921 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1922 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1923 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1924 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1925 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1926 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1927 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1928 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1929 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1930 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1931 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1932 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1933 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1934 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1935 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1936 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1937 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1938 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1939 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1940 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1941 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1942 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1943 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1944 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1945 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1946 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1947 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1948 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1949 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1950 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1951 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1952 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1953 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1954 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1955 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1956 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1957 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1958 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1959 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1960 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1961 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1962 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1963 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1964 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1965 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1966 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1967 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk40.correct

end Krenn.X5OrbitWitnessChunks.Chunk40
