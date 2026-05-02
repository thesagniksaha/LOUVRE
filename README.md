# LOUVRE: Lean Output Verification & Redaction Engine

LOUVRE is a Lean 4 library that turns redaction policies for multi-agent AI systems into proof-carrying artefacts. A generator agent (LLM) proposes a redaction policy as JSON, Lean 4 checks that the policy satisfies a universally-quantified safety predicate and a liveness predicate, only certified policies are accepted by the publisher in the multi-agent pipeline. The library proves seven theorems, including a noninterference result and an n-ary compositional safety theorem.

This is a demonstration of proof-carrying redaction artefacts in a small multi-agent pipeline. The matcher language is a deliberately small fragment of regular expressions (literals, prefixes, substrings, Boolean combinations); extending to full regex is the natural next step.

## Origin

This project was built during the **LeanLang for Verified Autonomy Hackathon** (April 17–18 + online through May 1, 2026) at the **Indian Institute of Science (IISc), Bangalore**.
Sponsored by **[Emergence AI](https://www.emergence.ai)**. Organized by **[Emergence India Labs](https://east.emergence.ai)** in collaboration with **IISc Bangalore**.

## Acknowledgments
This project was made possible by:
- **Emergence AI** — Hackathon sponsor
- **Emergence India Labs** — Event organizer and research direction
- **Indian Institute of Science (IISc), Bangalore** — Academic partner, hackathon co-design, tutorials, and mentorship

## Links
- [Hackathon Page](https://east.emergence.ai/hackathon-april2026.html)
- [Emergence India Labs](https://east.emergence.ai)
- [Emergence AI](https://www.emergence.ai)