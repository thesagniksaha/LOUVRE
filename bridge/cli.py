#!/usr/bin/env python3
"""LouVRE LLM bridge.

Calls OpenAI to synthesize a `RedactionPolicy` JSON for a natural-language
description of a secret class. Pipes the JSON through Lean's `Verify.lean`
harness. On verification failure, feeds the counterexample back to the LLM
and retries up to 3 times.

Usage:
    export OPENAI_API_KEY=sk-...
    python bridge/cli.py "redact AWS access keys"
    python bridge/cli.py --example bridge/examples/aws.json   # skip LLM, verify only
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PENDING = ROOT / "bridge" / "_pending.json"
PROMPT_PATH = ROOT / "bridge" / "prompts" / "policy_synthesis.txt"
VERIFY_LEAN = ROOT / "bridge" / "Verify.lean"

MAX_RETRIES = 3
MODEL = os.environ.get("LOUVRE_MODEL", "gpt-4.1-mini")


def call_openai(description: str, history: list[dict]) -> dict:
    """Call OpenAI Chat Completions with the synthesis prompt and history."""
    try:
        from openai import OpenAI
    except ImportError:
        sys.exit(
            "openai package not installed. Run: pip install openai"
        )

    client = OpenAI()
    system_prompt = PROMPT_PATH.read_text()
    user_messages = [
        {
            "role": "user",
            "content": f"Description of secrets to redact:\n{description}",
        }
    ]
    for entry in history:
        user_messages.append(
            {
                "role": "assistant",
                "content": json.dumps(entry["attempt"]),
            }
        )
        user_messages.append(
            {
                "role": "user",
                "content": (
                    f"That attempt failed verification.\n"
                    f"Reason: {entry['reason']}\n"
                    f"Counterexample: {entry.get('counterexample') or '(none)'}\n"
                    f"Revise and try again."
                ),
            }
        )

    resp = client.chat.completions.create(
        model=MODEL,
        messages=[{"role": "system", "content": system_prompt}, *user_messages],
        response_format={"type": "json_object"},
        temperature=0.2,
    )
    text = resp.choices[0].message.content
    return json.loads(text)


def lean_verify(policy: dict) -> tuple[bool, str, str | None]:
    """Run the Lean harness; return (ok, reason, counterexample)."""
    PENDING.write_text(json.dumps(policy, indent=2))
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(VERIFY_LEAN), str(PENDING)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
    )
    out = proc.stdout.strip()
    err = proc.stderr.strip()
    try:
        result = json.loads(out)
    except json.JSONDecodeError:
        return False, f"lean harness error (exit {proc.returncode}): {err or out}", None
    return result.get("ok", False), result.get("reason", ""), result.get("counterexample")


def synthesize(description: str) -> dict | None:
    history: list[dict] = []
    for attempt in range(1, MAX_RETRIES + 1):
        print(f"\n=== Attempt {attempt} / {MAX_RETRIES} ===")
        policy = call_openai(description, history)
        print("LLM proposed:")
        print(json.dumps(policy, indent=2))
        ok, reason, counterexample = lean_verify(policy)
        if ok:
            print(f"\n[CERTIFIED] {reason}")
            return policy
        print(f"\n[REJECTED] {reason}")
        if counterexample:
            print(f"  counterexample: {counterexample!r}")
        history.append(
            {"attempt": policy, "reason": reason, "counterexample": counterexample}
        )
    print("\nMax retries exhausted.")
    return None


def verify_only(path: Path) -> None:
    policy = json.loads(path.read_text())
    print(f"Verifying {path}")
    ok, reason, counterexample = lean_verify(policy)
    print(json.dumps({"ok": ok, "reason": reason, "counterexample": counterexample}, indent=2))
    sys.exit(0 if ok else 1)


def main() -> None:
    ap = argparse.ArgumentParser(description="LouVRE LLM bridge")
    ap.add_argument("description", nargs="?", help="natural-language secret description")
    ap.add_argument("--example", type=Path, help="verify a hand-curated example without calling the LLM")
    args = ap.parse_args()
    if args.example:
        verify_only(args.example)
    if not args.description:
        ap.error("either a description or --example is required")
    if not os.environ.get("OPENAI_API_KEY"):
        sys.exit("OPENAI_API_KEY not set")
    result = synthesize(args.description)
    sys.exit(0 if result else 1)


if __name__ == "__main__":
    main()
