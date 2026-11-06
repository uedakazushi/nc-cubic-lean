import VersoManual
import VersoBlueprint.PreviewManifest
import NcCubicBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc NcCubicBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
