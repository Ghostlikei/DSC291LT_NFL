# NFL: No Free Lunch Theorems in Lean 4

A formalization of three No Free Lunch theorems for UCSD DSC 291 (Learning Theory), Spring 2026.

## Theorems

**Theorem 1 — Adversarial online NFL (deterministic).**
For any deterministic online learner `A` and any sequence of distinct queries `x₁, …, x_T`, there exists a target function `f : X → Bool` against which `A` errs on every round.

**Theorem 2 — Wolpert–Macready NFL (histogram form, 1997).**
For any two non-revisiting (possibly stochastic) search algorithms `A₁, A₂` on a finite domain `X` with finite codomain `Y`, budget `m ≤ |X|`, and any cost sequence `c ∈ Y^m`,
$$\sum_{f \in Y^X} \Pr[\mathrm{obs}(A_1, f) = c] \;=\; \sum_{f \in Y^X} \Pr[\mathrm{obs}(A_2, f) = c].$$

*Corollary (averaged performance).* For any cost-only performance measure `φ : Y^m → ℝ≥0∞`, the average of `E[φ(obs(A, f))]` over `f ∈ Y^X` is algorithm-independent.

**Theorem 3 — Batch stochastic NFL (Shalev-Shwartz & Ben-David, Thm 5.1).**
For any deterministic learning algorithm `A` on a finite domain `X` and any sample size `m` with `2m ≤ |X|`, there exists a distribution `D` over `X × Bool` such that
1. some target `f : X → Bool` attains zero risk under `D`, and
2. $\Pr_{S \sim D^m}[\mathrm{risk}_D(A(S)) \ge 1/8] \;\ge\; 1/7$.

## Layout

```
Project/
├── .gitignore
├── README.md                        # this file
├── .venv/                           # Python virtualenv (ignored)
└── NFL/                             # Lean 4 project
    ├── lakefile.toml                # project config
    ├── lean-toolchain               # pinned to leanprover/lean4:v4.29.1
    ├── lake-manifest.json           # exact Mathlib + deps revisions
    ├── README.md                    # lake-generated, kept for CI compatibility
    ├── .github/workflows/           # lean-action CI, mathlib-update, release-tag
    ├── NFL.lean                     # root module — imports all three theorems
    └── NFL/
        ├── Basic.lean               # shared header (currently empty)
        └── codex_full/              # completed proofs (0 sorry) — see Status below
            ├── OnlineAdversarial.lean   # Theorem 1
            ├── WolpertMacready.lean     # Theorem 2
            ├── BatchStochastic.lean     # Theorem 3
            ├── PROOF_WRITEUP.md         # proof write-up & roadmap
            └── ROADMAP.md
```

## Build

One-time setup:

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
```

From `Project/NFL/`:

```bash
lake exe cache get      # pre-fetch Mathlib oleans (~5–10 min, vs. hours from source)
lake build              # compile the project (~60 s cold, ~0 s warm)
```

## Status

All three theorems are **fully proved, 0 `sorry`**, in [`NFL/NFL/codex_full/`](NFL/NFL/codex_full/):

| File | Main theorem | Lines |
|---|---|---|
| [`OnlineAdversarial.lean`](NFL/NFL/codex_full/OnlineAdversarial.lean) | `exists_adversarial_target` | 82 |
| [`WolpertMacready.lean`](NFL/NFL/codex_full/WolpertMacready.lean) | `wolpert_macready` (+ `wolpert_macready_avg` corollary) | 898 |
| [`BatchStochastic.lean`](NFL/NFL/codex_full/BatchStochastic.lean) | `batch_stochastic_NFL` | 893 |

**Proved:** the theorem statements above, exactly as displayed in [Theorems](#theorems) — e.g. `batch_stochastic_NFL` derives, for any deterministic learner `A` and `2m ≤ |X|`, a distribution `D` with a zero-risk target *and* `failureProb D A m (1/8) ≥ 1/7`.

**Assumed:** standard typeclass hypotheses on the ambient types — `[Fintype X]`, `[Fintype Y]`, `[DecidableEq X]` throughout; `[Nonempty X]` and `[MeasurableSingletonClass X]` additionally for `batch_stochastic_NFL` (nonemptiness is essential — see `no_probability_measure_empty_prod_bool` in the same file); plus the algorithm-side hypotheses stated in each theorem (`Nodup` query sequence for Theorem 1, `NonRevisiting` algorithms for Theorem 2, deterministic `Learner` for Theorem 3). No extra axioms are introduced.

Imports are narrowed: each theorem file loads only the Mathlib modules it needs, keeping `lake build` to under a minute.

For the proof write-up/roadmap and the agent workflow used to produce these proofs, see [`PROOF_WRITEUP.md`](NFL/NFL/codex_full/PROOF_WRITEUP.md), [`ROADMAP.md`](NFL/NFL/codex_full/ROADMAP.md), and [`SKILL.md`](NFL/SKILL.md). For a narrative walkthrough, see [`full_presentation_note.html`](NFL/presentation/full_presentation_note.html) (report) or [`full_presentation_slides.html`](NFL/presentation/full_presentation_slides.html) (slides).

## References

- Wolpert & Macready (1997). *No Free Lunch Theorems for Optimization*. IEEE Trans. Evol. Comput. 1(1):67–82.
- Schumacher, Vose & Whitley (2001). *The No Free Lunch and Problem Description Length*. GECCO.
- Shalev-Shwartz & Ben-David. *Understanding Machine Learning: From Theory to Algorithms*. Ch. 5 (No Free Lunch and PAC).
