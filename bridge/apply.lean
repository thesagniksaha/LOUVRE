/-
Runtime entry point: read text from stdin, apply one or more `RedactionPolicy`
JSONs in sequence, write the redacted text to stdout.

Usage:
  echo "Tweet: AKIAIOSFODNN7EXAMPLE today" \
    | lake env lean --run bridge/Apply.lean bridge/examples/aws.json

  # Or chain multiple policies (left-to-right application):
  cat msg.txt \
    | lake env lean --run bridge/Apply.lean policies/aws.json policies/email.json

This is the deployment-side companion to `Verify.lean`. `Verify.lean` certifies
a policy at synthesis time; `Apply.lean` runs the certified policy at request
time. For correctness, only run policies that have been certified by
`Verify.lean` (or whose certificates have been closed in Lean).
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

-- Parse a `RedactionPolicy` from JSON
def parsePolicy (j : Json) : Except String RedactionPolicy := do
  let src ← j.getObjVal? "source"
  let mat ← j.getObjVal? "matcher"
  let rep ← j.getObjValAs? String "replacement"
  let source ← parseMatcher src
  let matcher ← parseMatcher mat
  return { source := source, matcher := matcher, replacement := rep }

-- Apply a list of policies in sequence (left fold)
def applyPolicies (policies : List RedactionPolicy) (text : String) : String :=
  policies.foldl (fun acc p => redact p acc) text

-- Read the entire contents of stdin into a String
partial def readAllStdin (s : IO.FS.Stream) : IO String := do
  let line ← s.getLine
  if line.isEmpty then
    return ""
  else
    let rest ← readAllStdin s
    return line ++ rest

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Apply.lean: redact text against one or more JSON policies."
    IO.eprintln ""
    IO.eprintln "Usage:"
    IO.eprintln "  cat input.txt | lake env lean --run bridge/Apply.lean <policy.json> ..."
    IO.eprintln ""
    IO.eprintln "Each <policy.json> file should be a RedactionPolicy in the format"
    IO.eprintln "documented in bridge/prompts/policy_synthesis.txt."
    return 1
  let stdin ← IO.getStdin
  let text ← readAllStdin stdin
  -- Parse each policy file in argument order
  let mut policies : List RedactionPolicy := []
  for path in args do
    let raw? ← try
        let raw ← IO.FS.readFile path
        pure (some raw)
      catch e =>
        IO.eprintln s!"failed to read {path}: {e}"
        pure none
    let some raw := raw?
      | return 2
    match Json.parse raw with
    | .error e =>
        IO.eprintln s!"JSON parse error in {path}: {e}"
        return 3
    | .ok j =>
      match parsePolicy j with
      | .error e =>
          IO.eprintln s!"policy parse error in {path}: {e}"
          return 4
      | .ok p =>
          policies := policies ++ [p]
  -- Apply policies left-to-right and write to stdout
  let result := applyPolicies policies text
  IO.print result
  return 0
