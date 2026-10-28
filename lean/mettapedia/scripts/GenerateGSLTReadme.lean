import Mettapedia.DocText.GSLTReadmeCompositional

open Mettapedia.DocText.GSLTReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/GSLT/README.md" gsltReadmeMarkdown
