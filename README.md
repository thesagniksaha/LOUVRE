# LOUVRE: Lean Output Verification & Redaction Engine

LOUVRE is a Lean 4 library that turns redaction policies for multi-agent AI systems into proof-carrying artefacts. A generator agent (LLM) proposes a redaction policy as JSON, Lean 4 checks that the policy satisfies a universally-quantified safety predicate and a liveness predicate, only certified policies are accepted by the publisher in the multi-agent pipeline. The library proves seven theorems, including a noninterference result and an n-ary compositional safety theorem.

This is a demonstration of proof-carrying redaction artefacts in a small multi-agent pipeline. The matcher language is a deliberately small fragment of regular expressions (literals, prefixes, substrings, Boolean combinations); extending to full regex is the natural next step.

## Origin

This project was built during the **LeanLang for Verified Autonomy Hackathon** (April 17–18 + online through May 1, 2026) at the **Indian Institute of Science (IISc), Bangalore**.
Sponsored by **[Emergence AI](https://www.emergence.ai)**. Organized by **[Emergence India Labs](https://east.emergence.ai)** in collaboration with **IISc Bangalore**.

## Description

We use redaction of an API key from a social-media broadcast as a motivating example.

Runtime regex filters are useful, but they do not prove that a proposed pattern covers the declared secret class, and over-defensive filters can destroy benign content. LOUVRE makes those trade-offs explicit in Lean.

The theorem-proving core works with full Lean proofs. The LLM bridge performs finite, corpus-based checks over declared samples so that an LLM can iterate quickly.

- `CertifiedPolicy` is the proof-carrying Lean artifact.
- `bridge/verify.lean` is a synthesis-time JSON harness that checks sample obligations and replacement cleanliness.

## Architecture

LOUVRE has two layers.

**Lean proof layer:** `core.lean`, `policy.lean`, `theorems.lean`, and `pipeline.lean` define the matcher DSL, redaction function, policy certificates, theorem library, and `SafeTrace` publish invariant.

**Bridge layer:** `bridge/cli.py` asks an OpenAI model for a JSON policy, `bridge/Verify.lean` checks the JSON against declared samples, and `bridge/Apply.lean` applies one or more JSON policies to runtime text after verification.

## Demos

The Lean demos live in `LOUVRE/demo/`.


| File                 | What it demonstrates                                                                                        | Verdict                 |
| -------------------- | ----------------------------------------------------------------------------------------------------------- | ----------------------- |
| `goodtrace.lean`     | AWS-style `prefix "AKIA"` policy, certified with `Subsumes.refl`; constructs `goodTrace_safe`.              | Passes                  |
| `emaildemo.lean`     | `contains "@"` policy with replacement `<email>`; constructs `emailTrace_safe`.                             | Passes                  |
| `compose.lean`       | AWS redaction followed by email redaction; instantiates `compose_seq_safe`.                                 | Passes                  |
| `weakredactor.lean`  | Source includes `sk_test_` and `sk_live_`, but matcher only catches `sk_test_`; proves `weak_not_subsumes`. | Rejected by proof       |
| `overdefensive.lean` | Replacement `AKIA-REDACTED` is itself in the AWS source language; proves liveness failure.                  | Rejected by proof       |
| `badtrace.lean`      | Publisher skips sanitizer; proves `¬ SafeTrace badTrace`.                                                   | Rejected by trace model |


## Quick start

From a fresh clone:

```bash
git clone https://github.com/thesagniksaha/louvre
cd louvre

# Build the Lean library.
lake build

# Build all demos.
lake build \
  LOUVRE.demo.goodtrace LOUVRE.demo.badtrace \
  LOUVRE.demo.weakredactor LOUVRE.demo.overdefensive \
  LOUVRE.demo.emaildemo LOUVRE.demo.compose

# Verify a curated JSON policy without calling an LLM.
lake env lean --run bridge/verify.lean bridge/examples/aws.json

# Apply a verified JSON policy to runtime text.
printf 'Tweet: AKIAIOSFODNN7EXAMPLE today\n' \
  | lake env lean --run bridge/apply.lean bridge/examples/aws.json
```

Expected output for the last command:

```text
Tweet: [REDACTED-AWS-KEY] today
```

## Using LOUVRE as a Lean library

Import the public API:

```lean
import LOUVRE

open LOUVRE
```

Define a policy:

```lean
def awsPolicy : RedactionPolicy where
  source      := Matcher.prefix "AKIA"
  matcher     := Matcher.prefix "AKIA"
  replacement := "[REDACTED-AWS-KEY]"
```

Prove the obligations:

```lean
theorem aws_safety : Subsumes awsPolicy.source awsPolicy.matcher :=
  Subsumes.refl _

theorem aws_liveness : CleanReplacement awsPolicy.source awsPolicy.replacement := by
  unfold CleanReplacement
  decide
```

Package the certificate:

```lean
def awsCertified : CertifiedPolicy :=
  ⟨awsPolicy, aws_safety, aws_liveness⟩
```

Use the theorem library:

```lean
example (f : String) :
    accepts awsCertified.source
      (if accepts awsCertified.matcher f then awsCertified.replacement else f)
    = false :=
  safe_field_redaction awsCertified f
```

For concrete policy proofs, see:

- `LOUVRE/demo/goodtrace.lean`
- `LOUVRE/demo/emaildemo.lean`
- `LOUVRE/demo/compose.lean`
- helper lemmas in `LOUVRE/tactic.lean`

## Using the JSON verifier

A bridge policy JSON has this shape:

```json
{
  "source": {"kind": "prefix", "value": "AKIA"},
  "matcher": {"kind": "prefix", "value": "AKIA"},
  "replacement": "[REDACTED-AWS-KEY]",
  "secretSamples": [
    "AKIAIOSFODNN7EXAMPLE",
    "AKIA1234567890ABCDEF"
  ],
  "benignSamples": [
    "Tweet",
    "launching",
    "today"
  ]
}
```

Run:

```bash
lake env lean --run bridge/Verify.lean bridge/examples/aws.json
```

Successful output is JSON:

```json
{"reason": "certified", "ok": true, "counterexample": null}
```

Failure output includes a reason and, when available, a counterexample. For example, `stripe-weak.json` fails because the matcher misses a declared live Stripe-key sample.

## Using the LLM bridge with the OpenAI API

Install the Python OpenAI client and set credentials:

```bash
pip3 install openai
export OPENAI_API_KEY=sk-...
export LOUVRE_MODEL=gpt-4o
```

Then ask the bridge to synthesize a policy:

```bash
python3 bridge/cli.py \
  "redact AWS access keys (AKIA prefix). Use over-approximate prefix matching."
```

The bridge loop is:

1. `bridge/cli.py` sends the natural-language request and `bridge/prompts/policy_synthesis.txt` to the model.
2. The model returns JSON only.
3. The JSON is written to `bridge/_pending.json`.
4. `bridge/Verify.lean` checks declared secret samples, replacement cleanliness, and declared benign samples.
5. On failure, the reason and counterexample are sent back to the model for up to three attempts.

Actual transcript from `bridge/transcripts/run1-aws.log`:

```text
=== Attempt 1 / 3 ===
LLM proposed:
{
  "source": {"kind": "prefix", "value": "AKIA"},
  "matcher": {"kind": "prefix", "value": "AKIA"},
  "replacement": "REDACTED",
  ...
}

[CERTIFIED] certified
```

`bridge/transcripts/run2-tokens.log` demonstrates the retry path: the first attempt listed `notasecret` as benign while using `contains "secret"` as the matcher, so the verifier rejected it and returned that counterexample; the second attempt removed the bad benign sample and passed.

## Applying policies at runtime

After verifying a JSON policy, apply it to text through `bridge/apply.lean`:

```bash
printf 'Contact hello@example.com with AKIAIOSFODNN7EXAMPLE\n' \
  | lake env lean --run bridge/Apply.lean \
      bridge/examples/aws.json bridge/examples/email.json
```

Policies are applied left-to-right. The runtime applier parses JSON `RedactionPolicy` values and computes `redact`; it does not itself construct a Lean `CertifiedPolicy`. For correctness, only apply policies that have passed `bridge/verify.lean` for the declared corpus or whose full Lean certificates are available in code.  
  
## Related work

- **Type-Checked Compliance:** [Type-Checked Compliance: Deterministic Guardrails for Agentic Financial Systems Using Lean 4 Theorem Proving](https://arxiv.org/abs/2604.01483)
- **Verified Multi-Agent Orchestration:** [A Plan-Execute-Verify-Replan Framework for Complex Query Resolution](https://arxiv.org/abs/2603.11445)
- **Lean 4 regex formalization:** Zhuchko, Veanes, and Ebner, *Lean Formalization of Extended Regular Expression Matching with Lookarounds* (CPP 2024).
- **Neural regex synthesis without formal verification:** Locascio et al., DeepRegex (EMNLP 2016); Ye et al., Sketch-Driven Regex Generation (TACL 2020).

## Acknowledgments

This project was made possible by:

- **Emergence AI** — Hackathon sponsor
- **Emergence India Labs** — Event organizer and research direction
- **Indian Institute of Science (IISc), Bangalore** — Academic partner, hackathon co-design, tutorials, and mentorship

## Links

- [Hackathon Page](https://east.emergence.ai/hackathon-april2026.html)
- [Emergence India Labs](https://east.emergence.ai)
- [Emergence AI](https://www.emergence.ai)

