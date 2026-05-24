# Proof Timing And Attempt Logs

Source: reconstructed from the Codex session JSONL, Git history, file birth
times, and Lake build artifacts. All times below are Pacific time on
2026-05-19.

Raw session log:

`/home/tongle/.codex/sessions/2026/05/18/rollout-2026-05-18T22-57-33-019e3ecf-9bf2-7a23-8ad1-755d03e439fc.jsonl`

Commit containing the full proofs:

`39a2c78 first full proof`

---

## Summary

| Proof | Main request | First file timestamp | Final file timestamp | Final build artifact | Calendar time | Recorded active agent time |
|---|---:|---:|---:|---:|---:|---:|
| Wolpert-Macready | 13:17:33 | 13:19:59 | 14:05:39 | 14:05:53 | about 48m 20s to build, 51m 26s to final reply | about 40m 17s |
| Batch Stochastic | 14:16:07 | 14:07:55 | 14:56:51 | 14:57:17 | about 41m 10s from request to build, 41m 18s to final reply | about 41m 18s |

Notes:

- The Batch file was first created before the explicit Batch-continuation
  request, during the final sweep of the earlier `codex_full` turn.
- The active-agent time is computed from Codex task-completion durations.
- Git only has the final commit, so the detailed intermediate edit history is
  reconstructed from the Codex event log, not from Git commits.

---

## Git And File Evidence

The final commit was:

```text
39a2c78e066401b86e2aa366f2dea0c1af770a8f
AuthorDate: 2026-05-19 15:16:55 -0700
Subject: first full proof
```

Files added in that commit:

```text
893 lines  NFL/NFL/codex_full/BatchStochastic.lean
898 lines  NFL/NFL/codex_full/WolpertMacready.lean
77 lines   NFL/NFL/codex_full/ROADMAP.md
```

Filesystem timestamps:

```text
13:19:59 created  WolpertMacready.lean
14:05:39 modified WolpertMacready.lean
14:07:55 created  BatchStochastic.lean
14:56:51 modified BatchStochastic.lean
```

Lake build artifact timestamps:

```text
14:05:53 built NFL.codex_full.WolpertMacready
14:57:17 built NFL.codex_full.BatchStochastic
```

---

## Wolpert-Macready Timeline

### 13:17:33 - User request

Start the `codex_full` proof track, begin with Wolpert-Macready, and write a
roadmap plus code.

### 13:19:29 - Roadmap created

Created:

```text
NFL/NFL/codex_full/ROADMAP.md
```

The initial roadmap broke the Wolpert proof into:

1. trace recursion,
2. consistency of labelled traces,
3. counting compatible target functions,
4. proving algorithm-independent target sums,
5. deriving the expected-performance corollary.

### 13:19:59 - Wolpert file created

Created:

```text
NFL/NFL/codex_full/WolpertMacready.lean
```

Initial definitions included:

- `SearchAlg`
- `SearchAlg.NonRevisiting`
- `trace`
- `observations`
- early structural lemmas for traces and observations

### 13:20-13:30 - First proof pass

Main edits:

- Added support lemmas for trace length and consistency.
- Added no-repeat trace support under `NonRevisiting`.
- Added observation expansion and length-support facts.
- Added `Consistent`, `consistentTargets`, and `consistentCount`.
- Added first target-counting infrastructure.

Representative failed build diagnostics:

```text
13:20:16  Application type mismatch at WolpertMacready.lean:97
13:20:38  Application type mismatch at WolpertMacready.lean:149
13:21:01  Unknown identifier `hz_tail`
13:22:12  Unknown constant `List.mem_concat`
13:23:09  failed to synthesize Decidable (c = List.map Prod.snd h)
13:24:26  `rfl` failed after expanding PMF.map_apply
```

Representative successful checkpoints:

```text
13:21:28  Built NFL.codex_full.WolpertMacready
13:22:41  Built NFL.codex_full.WolpertMacready
13:26:18  Built NFL.codex_full.WolpertMacready
13:29:58  Built NFL.codex_full.WolpertMacready
```

### 13:30:43 - First Wolpert turn completed

Recorded active time:

```text
790.384 seconds = 13m 10s
```

At this point the roadmap and a substantial Wolpert scaffold compiled, but the
full theorem proof was not finished.

### 13:42:24 - User says to continue until finished

Main edits in this second pass:

- Added `traceFrom` and `observationsFrom` continuation processes.
- Added `queryTraceFrom` and `labelledTrace`.
- Added `queriedLabel` and uniqueness of labels in nodup histories.
- Added `extendFromComplement`.
- Added `consistentEquivComplement`.
- Proved `consistentCount_eq_pow_card`.
- Added `avgFuture`.
- Proved the main invariant `avgFuture_eq_pow`.
- Proved `wolpert_macready`.
- Added the expected-performance corollary `wolpert_macready_avg`.

Representative failed build diagnostics:

```text
13:45:50  build failed after adding continuation process
14:03:43  could not synthesize implicit argument `α`
14:04:13  Application type mismatch near final averaged theorem
```

Representative successful checkpoints:

```text
13:46:20  Built NFL.codex_full.WolpertMacready
13:49:10  Built NFL.codex_full.WolpertMacready
13:55:22  Built NFL.codex_full.WolpertMacready
13:59:12  Built NFL.codex_full.WolpertMacready
14:04:39  Built NFL.codex_full.WolpertMacready
14:05:54  Built NFL.codex_full.WolpertMacready
```

### Wolpert edit/build counts

For the full Wolpert interval, 13:17:33 to 14:08:59:

```text
30 apply_patch edits touching Wolpert/ROADMAP
  26 edits to WolpertMacready.lean
  4 edits to ROADMAP.md

26 relevant Wolpert build-result events
  11 successful
  15 failed

57 target-specific probe/search commands
```

### Wolpert finish

```text
14:05:39 final file modification
14:05:53 final Lake artifact for NFL.codex_full.WolpertMacready
14:08:59 final reply for the turn
```

Elapsed:

```text
13:17:33 -> 14:05:53 = 48m 20s to final build
13:17:33 -> 14:08:59 = 51m 26s to final reply
active Codex duration = 13m 10s + 27m 07s = 40m 17s
```

---

## Batch Stochastic Timeline

### 14:07:55 - Initial Batch file created

Created:

```text
NFL/NFL/codex_full/BatchStochastic.lean
```

This first version established the theorem interface and the zero-sample
edge-case style, then compiled during the Wolpert/full-track turn.

### 14:16:07 - User request

Continue the Batch Stochastic version, write the roadmap, and finish the proof.

### 14:16-14:26 - Setup and graph distribution

Main edits:

- Added graph embedding of target labels into `X × Bool`.
- Added `graphFinset`.
- Added finite-support PMF `graphPMF`.
- Proved the graph distribution is realizable by its target.

Successful checkpoint:

```text
14:26:26  Built NFL.codex_full.BatchStochastic
```

### 14:29-14:31 - Risk and sample-risk layer

Main edits:

- Added `supportRisk`.
- Related measure-theoretic risk to finite support risk.
- Added `supportSampleList`.
- Added `sampleRisk`.
- Added finite failure rate definitions.

Representative failed diagnostic:

```text
14:29:21  failed to prove positivity/nonnegativity/nonzeroness at BatchStochastic.lean:179
```

Successful checkpoints:

```text
14:29:48  Built NFL.codex_full.BatchStochastic
14:30:44  Built NFL.codex_full.BatchStochastic
```

### 14:33-14:38 - Abstract support combinatorics

Main edits:

- Added `splitAt`.
- Added `abstractSampleList`.
- Added `abstractRisk`.
- Proved label-pair loss identity.
- Added seen and unseen finite sets.
- Proved unseen-cardinality lower bound.

Representative failed diagnostics:

```text
14:33:40  `rfl` failed at BatchStochastic.lean:316
14:34:08  unsolved goals at BatchStochastic.lean:318
14:37:56  failed to rewrite using equation theorem for `unseenFinset`
```

Successful checkpoint:

```text
14:38:20  Built NFL.codex_full.BatchStochastic
```

### 14:38-14:49 - Averaging argument

Main edits:

- Proved fixed-sample lower bound by summing over all Boolean labelings.
- Defined `abstractBadSamples`.
- Defined `abstractFailureRate`.
- Proved piecewise-threshold averaging lemma.
- Proved existence of a labeling with failure rate at least the target bound.

Successful checkpoints:

```text
14:42:26  Built NFL.codex_full.BatchStochastic
14:47:36  Built NFL.codex_full.BatchStochastic
14:49:02  Built NFL.codex_full.BatchStochastic
```

### 14:54-14:57 - Transfer back to the measure theorem

Main edits:

- Related support traces to abstract sample lists.
- Related `supportRisk` to `abstractRisk`.
- Related `risk graphPMF` to abstract risk.
- Proved product-measure support facts for graph samples.
- Proved `abstractFailureRate_le_failureProb_graph`.
- Proved final `batch_stochastic_NFL`.

Successful checkpoints:

```text
14:54:01  Built NFL.codex_full.BatchStochastic
14:55:39  Built NFL.codex_full.BatchStochastic
14:56:18  Built NFL.codex_full.BatchStochastic
14:57:18  Built NFL.codex_full.BatchStochastic
```

### Batch edit/build counts

For the explicit Batch interval, 14:16:07 to 14:57:25:

```text
18 apply_patch edits to BatchStochastic.lean

16 relevant Batch build-result events
  12 successful
  4 failed

61 target-specific probe/search commands
```

If including the earlier 14:07 skeleton creation during the preceding turn:

```text
18 total Batch build-result events
  14 successful
  4 failed
```

### Batch finish

```text
14:56:51 final file modification
14:57:17 final Lake artifact for NFL.codex_full.BatchStochastic
14:57:25 final reply for the turn
```

Elapsed:

```text
14:16:07 -> 14:57:17 = 41m 10s to final build
14:16:07 -> 14:57:25 = 41m 18s to final reply
active Codex duration = 41m 18s
```

---

## Commit And Push

After both proofs compiled:

```text
15:16:55  committed `39a2c78 first full proof`
15:17:00  pushed to origin/proof_writedown
15:19:57  pushed to upstream/proof_writedown
```

The committed full-proof files were:

```text
NFL/NFL/codex_full/WolpertMacready.lean
NFL/NFL/codex_full/BatchStochastic.lean
NFL/NFL/codex_full/OnlineAdversarial.lean
NFL/NFL/codex_full/ROADMAP.md
```

