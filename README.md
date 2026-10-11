# axtypesystem

Isabelle/HOL mechanization of the metatheory of *Leakage Containment by
Typing*: a two-layer information-flow type system over axiomatic leakage
containment models.

## Repository structure

The development is the Isabelle session `LCM_Types` (base logic `HOL`),
defined in `ROOT`. The theories are layered bottom-up:

| File | Contents |
|---|---|
| `theories/LCM_Lattice.thy` | Two-point security lattice, pair types `⟨ℓA, ℓT⟩`, stability, and the componentwise type order and join. |
| `theories/LCM_Graph.thy` | Execution-graph model (`rf`, `rfx`, `data`, `addr`, `ctrl`), seed labels `base_val`/`base_addr`, well-formedness `wf_base`, and the rfx-subgraph order `⪯G`. |
| `theories/LCM_EventTyping.thy` | Event typing judgments `⊢A` and `⊢T`, the least event typing `Γ*`, the pair-type invariant, and rfx-independence and monotonicity. |
| `theories/LCM_ObsTyping.thy` | Observation typing `⊢O`, the observation type `obs_ty`, the refinement operator (`refine`, `robs_ty`), and their invariant and monotonicity lemmas. |
| `theories/LCM_Soundness.thy` | Refined containment, its monotonicity, the semantic locale `lcm_semantics`, the soundness theorem and its speculative-constant-time corollary, a consistency witness, and cache-observer flow completeness. |
| `theories/LCM_Least_Typing.thy` | `Γ*` satisfies the seed and propagation constraints and is their unique least solution (`gamma_star_solution`, `gamma_star_least`, `gamma_star_unique_least`). |
| `theories/LCM_Aspect_Soundness.thy` | The locale `lcm_aspect_semantics`, in which a memory event's own address or guard may mediate its payload divergence. The soundness theorem and its corollary are re-proved by ordering aspects within each event (guard, address, payload) lexicographically with fetch order. Every `lcm_semantics` instance is an instance (`aspect_semantics_instance`). |
| `theories/LCM_Execution_Bridge.thy` | Execution records with payloads, exact addresses, predicates, and execution flags; the four divergence predicates as field inequalities (`obs_div_execution_iff`); cache-line access traces; and the conditional trace result `cache_trace_noninterference` with its quantified form `cache_SCT_from_adequacy`. |
| `theories/LCM_Semantic_Examples.thy` | Interpreted instances: a public-table model whose read has event type `LL` and address type `LH` (containment fails at the address; the identity table makes payload and trace differ; the strict-event locale cannot interpret it), a `B(i) = 64·i` witness separating cache-line equality from exact-address equality, and a model with secret `HH`-typed internal data whose cache traces are shown equal through the general theorems. |

## Relation to the analysis tool

The event rules, observation rules, refinement operator, and the cache
observer's checked set are the ones the companion LLVM pass implements
(`src/axtypes/typecheck.cc` in the `clou-typesystem` repository). The pass
computes `Γ*` by fixpoint iteration; `LCM_Least_Typing` shows that this is the
least solution the inductive judgments define. The pass is not extracted from
the development.

## Scope

The semantic locales state the adequacy conditions of the paper (well-formed
seeds, flow completeness, the divergence-propagation clauses, and fact
soundness) as assumptions; the examples discharge them for their own
equations. The address-divergence predicate compares exact addresses, so
equality of cache lines alone does not justify a refinement fact. The
execution records are small deterministic models; the C/LLVM front-end, graph
and seed generation, refinement-fact discharge, and the analysis pass are
outside the mechanization.

## Building

Requires Isabelle2025-2. From the repository root:

    isabelle build -c -D .

This checks the entire `LCM_Types` session. `ROOT` sets
`quick_and_dirty = false`; the theories contain no `sorry`, `oops`, or
`axiomatization`.
