import Mettapedia.DocText.GSLTReadmeCompositional

open Mettapedia.DocText.GSLTReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "~/claude/lean-projects/mettapedia/Mettapedia/GSLT/README.md" gsltReadmeMarkdown
