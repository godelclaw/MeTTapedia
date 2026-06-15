import Mettapedia.DocText.CategoricalLogicReadmeCompositional

open Mettapedia.DocText.CategoricalLogicReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/Mettapedia/lean/mettapedia/Mettapedia/CategoricalLogic/README.md" categoricalLogicReadmeMarkdown
