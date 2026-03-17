/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Renshaw, Jason Reed, Adaptation to Verso by Emilio J. Gallego Arias
-/

import Std.Data.HashMap
import VersoManual
import VersoBlueprint.Macros
import VersoBlueprint.PreviewManifest
import Contents

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

def htmlAssets : HtmlAssets where
  features := .all
  extraCss := {}
  extraJs := [tex_prelude_table_js%, include_str "static-web/math.js"]
  extraJsFiles := {}
  extraCssFiles := {}
  extraDataFiles := {}
  licenseInfo := {}

def htmlConfig : HtmlConfig where
  toHtmlAssets := htmlAssets
  htmlDepth := 1
  extraHead : Array Output.Html := #[]

def outputConfig : OutputConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately

def config : Config where
  toHtmlConfig := htmlConfig
  toOutputConfig := outputConfig

def renderConfig : RenderConfig where
  toConfig := config

private partial def filesBelow (root : System.FilePath) :
    IO (Array System.FilePath) := Prod.snd <$> StateT.run (go ".") #[]
where
  go (p : System.FilePath) := do
    for d in (← (root / p).readDir) do
      if ← d.path.isDir then
        go (p / d.fileName)
      else
        modify (·.push (p / d.fileName))

private def inlinePreviewTemplatePrefix : String :=
  "<template class=\"bp_inline_preview_tpl\" data-bp-preview-id=\""

private def labelPreviewTemplatePrefix : String :=
  "<template class=\"bp_label_preview_tpl\""

private def inlinePreviewTemplateIds (html : String) : List String :=
  (html.splitOn inlinePreviewTemplatePrefix).drop 1 |>.filterMap fun frag =>
    match frag.splitOn "\"" with
    | id :: _ =>
      if id.isEmpty then none else some id
    | [] => none

private def duplicateInlinePreviewTemplateIds (html : String) : List (String × Nat) :=
  let counts := (inlinePreviewTemplateIds html).foldl
    (init := ({} : HashMap String Nat))
    (fun m id =>
      let n := (m[id]?).getD 0
      m.insert id (n + 1))
  counts.toList.filter (fun (_id, n) => n > 1)

private def hasSubstr (s needle : String) : Bool :=
  (s.splitOn needle).length > 1

private def isIndexHtml (path : System.FilePath) : Bool :=
  let s := path.toString
  s == "index.html" || s.endsWith "/index.html"

private def checkSharedPreviewManifestMode : ExtraStep := fun mode logError cfg _st _text => do
  match mode with
  | .multi =>
      let htmlRoot := cfg.destination / "html-multi"
      if !(← htmlRoot.pathExists) then
        logError s!"Shared preview manifest check: output directory not found: {htmlRoot}"
      else
        let manifestFile := htmlRoot / "-verso-data" / Informal.PreviewManifest.manifestFilename
        if !(← manifestFile.pathExists) then
          logError s!"Shared preview manifest check: manifest file not found: {manifestFile}"
        let files ← filesBelow htmlRoot
        for rel in files do
          if !isIndexHtml rel then
            continue
          let full := htmlRoot / rel
          let html ← IO.FS.readFile full
          if hasSubstr html labelPreviewTemplatePrefix then
            logError s!"Shared preview manifest mode should strip label preview templates from {rel}"
  | .single => pure ()

private def checkInlinePreviewTemplateDedup : ExtraStep := fun mode logError cfg _st _text => do
  match mode with
  | .multi =>
      let htmlRoot := cfg.destination / "html-multi"
      if !(← htmlRoot.pathExists) then
        logError s!"Inline preview dedupe check: output directory not found: {htmlRoot}"
      else
        let files ← filesBelow htmlRoot
        for rel in files do
          if !isIndexHtml rel then
            continue
          let full := htmlRoot / rel
          let html ← IO.FS.readFile full
          let dup := duplicateInlinePreviewTemplateIds html
          if !dup.isEmpty then
            let sample := String.intercalate ", " <| (dup.take 5).map (fun (pid, n) => s!"{pid}×{n}")
            logError s!"Inline preview template duplicates found in {rel}: {sample}"
  | .single => pure ()

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := renderConfig)
    (extraSteps := [
      checkSharedPreviewManifestMode,
      checkInlinePreviewTemplateDedup
    ])
