import Mettapedia.DocText.GSLTReadmeCompositional

open Mettapedia.DocText.GSLTReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/Mettapedia/lean/mettapedia/Mettapedia/GSLT/README.md" gsltReadmeMarkdown
