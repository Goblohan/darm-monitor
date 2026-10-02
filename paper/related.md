# Related work

Sources are listed at the end. Each description keeps to what the cited work
itself states; DARM's position relative to it follows.

## Reference monitors and complete mediation

The reference monitor was introduced in Anderson's 1972 Computer Security
Technology Planning Study as a mechanism that enforces the authorized access
relationships between subjects and objects, implemented as a reference
validation mechanism, whose first realizations were security kernels [1].
Saltzer and Schroeder's design principles include complete mediation (every
access to every object is checked for authority) and fail-safe defaults [2].
DARM's broker is a reference monitor for an agent's tool use, and it states its
guarantees relative to complete mediation as an explicit assumption rather
than a property it proves. Two of its results sharpen what mediation can
deliver: the mediated domain is bounded by what the monitor records
(Section 4.2), and what any boundary can guarantee is bounded by what it
observes (Section 3).

## Tamper-evident logs

Kelsey and Schneier [3] and Crosby and Wallach [4] give logs whose tampering is
detectable. Crosby and Wallach's history tree makes insertion and auditing
logarithmic, under a threat model in which the logger itself may become
malicious, and stresses that tamper evidence detects misbehaviour rather than
preventing it, and requires auditing. DARM's log is a simpler hash chain with
signed checkpoints published to an external sink, suited to a single broker.
What is new is the log's role: it is the evidence that binds freshness. A file
restored with its genuine attestation is accepted by the attestation alone and
refused by the log (Sections 5.3 and 5.7).

## Verified systems and their trusted base

seL4 proves that a microkernel's C implementation follows its abstract
specification, assuming the correctness of the compiler, assembly code, boot
code and hardware [5]; later work validated the compiled binary against the C
semantics [6]. DARM's bridge has the same shape at a smaller scale: the
kernel's decision is the proved Lean definition, compiled, with the compiler and
runtime trusted (Section 7). Unlike seL4, DARM does not verify its whole
implementation. Its contribution here is to make the bridge from each theorem
to the running code explicit for every claim (construction, proved, tested or
assumed) and to have the build count them.

## Mutation analysis as evidence of test adequacy

Mutants, small artificial faults seeded into a program, are widely used as a
proxy for real faults. Just et al. found a statistically significant
correlation between a test suite's detection of mutants and its detection of
357 real faults, independent of code coverage, while also identifying real
faults not coupled to common mutants [7]. DARM uses mutation narrowly: each
mutation removes one load-bearing check, and the build requires that some test
then fails. The gate exposed checks that no test asserted, and a stress test
that passed without exercising the window it was written for (Section 7).

## System-level defenses for tool-using agents

CaMeL extracts the control and data flows from the trusted query, so untrusted
data cannot alter the program flow, and uses capabilities to enforce policies
when tools are called; it reports 77% of AgentDojo tasks solved with provable
security, against 84% for an undefended system [8]. FIDES presents a formal
model of agent planners, characterizes the properties enforceable by dynamic
taint-tracking, and tracks confidentiality and integrity labels [9]. Progent
enforces least privilege through a policy language applied at the level of tool
calls [10]. AgentSpec specifies runtime constraints as rules with a trigger,
predicate conditions and an enforcement [11]. Beurer-Kellner et al. propose
design patterns with provable resistance to prompt injection, deliberately
constraining what agents can do [12]. AgentDojo provides 97 realistic tasks and
629 security test cases for evaluating attacks and defenses [13].

These defenses act at the planner, the interpreter or the tool call. DARM acts
at execution and effect: it decides, executes, records, and verifies the state
of the world afterwards, which is why its central results (completeness of the
effect, execution identity, the chain to an attested state, attested reads
between stages) have no direct counterpart above. FIDES is closest in spirit to
Section 3: both ask what a mechanism can enforce given what it observes. FIDES
characterizes what dynamic taint-tracking can enforce; Section 3 characterizes
when an authorization can be complete, given what the boundary observes. The
composition results apply to these systems directly: a provenance or capability
layer and an execution boundary back each other up only in the dimensions both
check, from independent inputs. Evaluation is a stated gap: the systems above
are evaluated on AgentDojo, and DARM's evaluation is deterministic and
scenario-based.

## Sources

[1] J. P. Anderson, Computer Security Technology Planning Study, ESD-TR-73-51,
    US Air Force Electronic Systems Division, 1972.
[2] J. H. Saltzer and M. D. Schroeder, The Protection of Information in Computer
    Systems, 1975. https://www.cs.virginia.edu/~evans/cs551/saltzer/
[3] J. Kelsey and B. Schneier, secure audit logs, 1999 (exact title and venue to
    verify before submission).
[4] S. A. Crosby and D. S. Wallach, Efficient Data Structures for Tamper-Evident
    Logging, 18th USENIX Security Symposium, 2009.
[5] G. Klein et al., seL4: Formal Verification of an OS Kernel, 22nd ACM SOSP, 2009.
[6] Translation validation of seL4's binary against its C semantics (citation to
    complete before submission).
[7] R. Just, D. Jalali, L. Inozemtseva, M. D. Ernst, R. Holmes, G. Fraser, Are
    Mutants a Valid Substitute for Real Faults in Software Testing?, FSE 2014,
    pp. 654-665.
[8] Debenedetti et al., Defeating Prompt Injections by Design, arXiv:2503.18813.
[9] Costa et al., Securing AI Agents with Information-Flow Control, arXiv:2505.23643.
[10] Shi et al., Progent: Programmable Privilege Control for LLM Agents, arXiv:2504.11703.
[11] Wang et al., AgentSpec: Customizable Runtime Enforcement for Safe and
     Reliable LLM Agents, arXiv:2503.18666.
[12] Beurer-Kellner et al., Design Patterns for Securing LLM Agents against
     Prompt Injections, arXiv:2506.08837.
[13] Debenedetti et al., AgentDojo: A Dynamic Environment to Evaluate Prompt
     Injection Attacks and Defenses for LLM Agents, NeurIPS 2024.
