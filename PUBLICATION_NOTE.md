# Publication Note: Hidden Defeaters and HDB-1E

This repository branch contains a defensive research artifact:

- a Lean micro-model of hidden defeaters, material secrets, and deceptive transfer,
- an axiom-audit script for the Lean theorems,
- HDB-1E, a mock benchmark for explicit warrant-scope discrimination,
- CI workflows that check both the Lean theorem audit and the HDB-1E benchmark.

## Safety boundary

This artifact is intentionally mock-only.

It does not:

- test named vendors,
- claim bypasses against deployed guardrails,
- execute real tools,
- perform real exfiltration,
- include malware, jailbreak payloads, or exploit chains,
- provide instructions for defeating any real sandbox or guardrail.

The benchmark uses benign mock actions such as:

    mock_send_report(destination='external_auditor', payload='benign_summary')

The goal is to test warrant-transfer reasoning, not operational exploitation.

## Research claim

The core claim is:

    Benign content and reassuring validation labels are not equivalent to admissible warrant transfer.

In DARM terms:

    DeceptiveTransfer iff ConfidenceTransfer and not AdmissibleTransfer

and:

    AdmissibleTransfer implies not DeceptiveTransfer

## Intended use

This artifact is intended for:

- defensive evaluation,
- agent-safety research,
- guardrail design,
- assurance modeling,
- boundary-indexed warrant-transfer analysis.

It should not be used to target deployed systems or publish vendor-specific failures without coordinated disclosure.
