import KrennX5OrbitWitness

namespace Krenn.X5OrbitWitnessChunks.Chunk41

open Krenn.X5Symmetry
open Krenn.X5OrbitWitness

set_option maxRecDepth 100000

def witnessTable : Array OrbitWitness :=
  #[
    ⟨175, .cycle234, .p021⟩, ⟨174, .cycle234, .p021⟩, ⟨178, .cycle234, .p021⟩, ⟨179, .cycle234, .p021⟩, ⟨176, .cycle234, .p021⟩, ⟨177, .cycle234, .p021⟩, ⟨193, .cycle234, .p021⟩, ⟨192, .cycle234, .p021⟩, ⟨196, .cycle234, .p021⟩, ⟨197, .cycle234, .p021⟩, ⟨194, .cycle234, .p021⟩, ⟨195, .cycle234, .p021⟩,
    ⟨61, .cycle234, .p021⟩, ⟨60, .cycle234, .p021⟩, ⟨64, .cycle234, .p021⟩, ⟨65, .cycle234, .p021⟩, ⟨62, .cycle234, .p021⟩, ⟨63, .cycle234, .p021⟩, ⟨31, .swap24, .p021⟩, ⟨30, .swap24, .p021⟩, ⟨34, .swap24, .p021⟩, ⟨35, .swap24, .p021⟩, ⟨32, .swap24, .p021⟩, ⟨33, .swap24, .p021⟩,
    ⟨115, .cycle234, .p021⟩, ⟨114, .cycle234, .p021⟩, ⟨118, .cycle234, .p021⟩, ⟨119, .cycle234, .p021⟩, ⟨116, .cycle234, .p021⟩, ⟨117, .cycle234, .p021⟩, ⟨121, .swap23, .p021⟩, ⟨120, .swap23, .p021⟩, ⟨124, .swap23, .p021⟩, ⟨125, .swap23, .p021⟩, ⟨122, .swap23, .p021⟩, ⟨123, .swap23, .p021⟩,
    ⟨85, .cycle234, .p021⟩, ⟨84, .cycle234, .p021⟩, ⟨88, .cycle234, .p021⟩, ⟨89, .cycle234, .p021⟩, ⟨86, .cycle234, .p021⟩, ⟨87, .cycle234, .p021⟩, ⟨103, .cycle234, .p021⟩, ⟨102, .cycle234, .p021⟩, ⟨106, .cycle234, .p021⟩, ⟨107, .cycle234, .p021⟩, ⟨104, .cycle234, .p021⟩, ⟨105, .cycle234, .p021⟩
  ]

theorem witnessTable_size : witnessTable.size = 48 := by
  decide

def witness (case : Fin 7776) : OrbitWitness :=
  witnessTable.getD (case.val - 1968) defaultOrbitWitness

theorem correct (case : Fin 7776) (lower : 1968 ≤ case.val)
    (upper : case.val < 2016) :
    actCase (witness case).leaf
        (witness case).colour
        (labelledCaseChoice case) =
      representativeChoice (witness case).representative := by
  interval_cases value : case.val
  · have equal : case = (1968 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1969 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1970 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1971 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1972 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1973 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1974 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1975 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1976 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1977 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1978 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1979 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1980 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1981 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1982 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1983 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1984 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1985 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1986 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1987 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1988 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1989 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1990 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1991 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1992 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1993 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1994 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1995 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1996 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1997 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1998 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (1999 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2000 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2001 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2002 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2003 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2004 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2005 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2006 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2007 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2008 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2009 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2010 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2011 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2012 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2013 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2014 : Fin 7776) := Fin.ext value
    subst case
    decide
  · have equal : case = (2015 : Fin 7776) := Fin.ext value
    subst case
    decide

#print axioms Krenn.X5OrbitWitnessChunks.Chunk41.correct

end Krenn.X5OrbitWitnessChunks.Chunk41
