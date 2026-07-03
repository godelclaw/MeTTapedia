import Mettapedia.DocText.LanguagesReadmeCompositional

open Mettapedia.DocText.LanguagesReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "~/claude/lean-projects/mettapedia/Mettapedia/Languages/README.md" languagesReadmeMarkdown
