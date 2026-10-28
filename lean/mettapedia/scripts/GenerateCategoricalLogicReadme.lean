import Mettapedia.DocText.CategoricalLogicReadmeCompositional

open Mettapedia.DocText.CategoricalLogicReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/CategoricalLogic/README.md" categoricalLogicReadmeMarkdown
