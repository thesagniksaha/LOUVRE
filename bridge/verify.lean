/-
Harness invoked by `bridge/cli.py`. Reads a JSON policy from
`bridge/_pending.json`, attempts to construct a `CertifiedPolicy`, prints
`OK` or a counterexample, and exits with the corresponding code.

Run as:
  lake env lean bridge/Verify.lean
-/

import LOUVRE
import Lean.Data.Json

open Lean LOUVRE

partial def parseMatcher (j : Json) : Except String Matcher := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "literal" => do
      let v ← j.getObjValAs? String "value"
      return Matcher.literal v
  | "prefix" => do
      let v ← j.getObjValAs? String "value"
      return Matcher.prefix v
  | "contains" => do
      let v ← j.getObjValAs? String "value"
      return Matcher.contains v
  | "anyOf" => do
      let items ← j.getObjValAs? (Array Json) "items"
      let ms ← items.mapM parseMatcher
      return Matcher.anyOf ms.toList
  | "allOf" => do
      let items ← j.getObjValAs? (Array Json) "items"
      let ms ← items.mapM parseMatcher
      return Matcher.allOf ms.toList
  | "never"  => return Matcher.never
  | "always" => return Matcher.always
  | k => Except.error s!"unknown matcher kind: {k}"

-- parse a `RedactionPolicy` from JSON
def parsePolicy (j : Json) : Except String RedactionPolicy := do
  let src ← j.getObjVal? "source"
  let mat ← j.getObjVal? "matcher"
  let rep ← j.getObjValAs? String "replacement"
  let source ← parseMatcher src
  let matcher ← parseMatcher mat
  return { source := source, matcher := matcher, replacement := rep }

-- bounded subsumption check
structure VerifyResult where
  ok : Bool
  reason : String
  counterexample : Option String

def verifyPolicy (p : RedactionPolicy)
    (secretSamples benignSamples : List String) : VerifyResult :=
  -- safety check: every declared secret sample must trigger the matcher
  match secretSamples.find? (fun s => !accepts p.matcher s) with
  | some bad =>
      { ok := false
      , reason := "safety failure: matcher misses a declared secret sample"
      , counterexample := some bad }
  | none =>
    -- liveness check 1: the replacement must not itself match the source.
    if accepts p.source p.replacement then
      { ok := false
      , reason := "liveness failure: replacement is itself in the source class"
      , counterexample := some p.replacement }
    else
      -- liveness check 2: no benign sample should be matched by the matcher.
      match benignSamples.find? (accepts p.matcher) with
      | some bad =>
          { ok := false
          , reason := "liveness failure: matcher catches a declared benign sample"
          , counterexample := some bad }
      | none =>
          { ok := true, reason := "certified", counterexample := none }

-- read the pending JSON, verify, write a result JSON, exit 0/1
def main (args : List String) : IO UInt32 := do
  let inputPath := args.headD "bridge/_pending.json"
  let raw ← IO.FS.readFile inputPath
  match Json.parse raw with
  | .error e => do
      IO.eprintln s!"JSON parse error: {e}"
      return 2
  | .ok j =>
    let policyResult := parsePolicy j
    let secretSamples := (j.getObjValAs? (Array String) "secretSamples").toOption.getD #[] |>.toList
    let benignSamples := (j.getObjValAs? (Array String) "benignSamples").toOption.getD #[] |>.toList
    match policyResult with
    | .error e => do
        IO.eprintln s!"policy parse error: {e}"
        return 3
    | .ok p =>
      let result := verifyPolicy p secretSamples benignSamples
      let out : Json :=
        Json.mkObj
          [ ("ok", Json.bool result.ok)
          , ("reason", Json.str result.reason)
          , ("counterexample",
              match result.counterexample with
              | some s => Json.str s
              | none   => Json.null) ]
      IO.println (out.pretty)
      return (if result.ok then 0 else 1)
