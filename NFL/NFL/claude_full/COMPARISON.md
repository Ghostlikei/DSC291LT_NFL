# Comparison: claude_full vs codex_full

This document compares the three proofs side by side at both the roadmap level
and the tactic/implementation level.

Line counts:

| File               | codex_full | claude_full |
|--------------------|:----------:|:-----------:|
| OnlineAdversarial  |     82     |     108     |
| WolpertMacready    |    898     |     536     |
| BatchStochastic    |    893     |     677     |
| **Total**          |  **1873**  |  **1321**   |

The claude_full files are shorter overall despite the online proof being longer,
because WolpertMacready and BatchStochastic omit extra scaffold lemmas that
codex_full develops.

---

## 1. OnlineAdversarial

### Roadmap level

Both proofs follow the same strategy: induction on `xs`, with adversarial label
`b := ¬A [] x`, shifted learner `A' h y := A ((x, b) :: h) y`, combined target
`f y := if y = x then b else g y`. The structure is identical.

### Implementation differences

**Base case (nil):**

Codex — explicit tactic chain:
```lean
refine ⟨fun _ => false, ?_⟩
intro t; unfold MistakeAt; intro h; cases h
```

Claude — one-line term-mode:
```lean
exact ⟨fun _ => false, fun t => fun h => absurd h (by simp)⟩
```

Both are correct. Claude is more compact; codex is more readable step-by-step.

**`hget_ne` proof (xs[t] ≠ x):**

Codex — explicit tactic:
```lean
have hget_ne : xs.get ⟨t, ht'⟩ ≠ x := by
  intro hget
  apply hx_not_mem
  rw [← hget]
  exact List.get_mem xs ⟨t, ht'⟩
```

Claude — one-line term-mode:
```lean
have hget_ne : xs.get ⟨t, ht'⟩ ≠ x :=
  fun heq => hx_not_mem (heq ▸ List.get_mem xs ⟨t, ht'⟩)
```

**Successor round closure:**

Codex separates `rw [hhist, List.get_cons_succ]` from the `simpa`. Claude wraps
both in a single `rw [...] ` followed by `change` + `simpa`. Functionally identical.

**Why claude_full is longer (108 vs 82 lines):**
The doc-comment block is longer (25 lines) and the successor-round intermediate
`change` annotation adds lines. The mathematical content is the same.

---

## 2. WolpertMacready

### Roadmap level

**Codex roadmap (from `PROOF_WRITEUP.md`):**
```
1. Define trace/observations + queryTraceFrom (target-independent process)
2. Prove support invariants for queryTraceFrom
3. Relate trace/observations to queryTraceFrom
4. Count compatible targets → consistentCount_eq_pow_card
5. Collapse algorithm-dependent PMF sum → avgFuture_eq_pow
```

**Claude roadmap (from file header):**
```
1. Define trace/observations + traceFrom/observationsFrom
2. Prove PMF composition lemmas
3. Prove avgFuture_eq_pow directly (no queryTraceFrom)
4. Prove trace-support length facts
5. Assemble wolpert_macready + wolpert_macready_avg
```

**The key structural difference:** codex_full introduces `queryTraceFrom`, a
target-independent query process driven by a fixed observation list. This object
appears in 200+ lines of infrastructure (`queryTraceFrom_support_length`,
`queryTraceFrom_support_nodup_disjoint`, `relabelTrace`, `consistentCount_relabel`).
Claude's proof skips `queryTraceFrom` entirely and proves `avgFuture_eq_pow`
directly. The codex approach makes the algorithm-independence more visible through
a concrete intermediate object; the Claude approach is shorter but less explanatory.

### Implementation differences

**`consistent_nil`:**

Codex — tactic mode:
```lean
theorem consistent_nil (f : X → Y) : Consistent f [] := by
  intro xy hxy; cases hxy
```

Claude — term mode:
```lean
theorem consistent_nil (f : X → Y) : Consistent f [] :=
  fun _ hxy => nomatch hxy
```

`cases hxy` and `nomatch hxy` are equivalent — both case-split on the impossible
membership. Term-mode is slightly more compact.

**`queriedLabel_eq_of_mem`:**

Codex introduces `let witness` and three separate `have` statements before `simp`.
Claude restructures into two `have`s using `Classical.choose_spec` and names them
`hwitness`/`h_eq`. Codex is slightly more verbose but easier to read linearly.

**`extendFromComplement_consistent`:**

Codex — explicit `have hx`:
```lean
theorem extendFromComplement_consistent ... : Consistent (extendFromComplement h g) h := by
  intro xy hxy
  unfold extendFromComplement
  have hx : xy.1 ∈ h.map Prod.fst := List.mem_map_of_mem hxy
  simp [hx, queriedLabel_eq_of_mem hh hxy]
```

Claude — inline `simp`:
```lean
theorem extendFromComplement_consistent ... : Consistent (extendFromComplement h g) h :=
  fun xy hxy => by
    unfold extendFromComplement
    simp [List.mem_map_of_mem hxy, queriedLabel_eq_of_mem hh hxy]
```

**`consistentEquivComplement.right_inv`:**

Codex:
```lean
right_inv g := by funext x; unfold extendFromComplement; simp [x.2]
```

Claude:
```lean
right_inv g := by funext x; simp [extendFromComplement, x.2]
```

Equivalent — `simp [extendFromComplement, ...]` unfolds the definition inline.

**`avgFuture_eq_pow` (the main lemma):**

The proof structure is essentially identical between both versions:
1. Base case: fold `consistentCount_eq_pow_card`.
2. Inductive step: apply `avgFuture_cons`, define constant `K`, show each
   nonzero term equals `K` via IH, pull `K` out of the PMF sum using
   `PMF.tsum_coe`.

Minor difference in `congr` steps: codex uses three separate `congr 1` lines;
Claude chains them as `congr 1; unfold K; congr 1; congr 1`.

**`wolpert_macready_avg` calc chain:**

After error-fixing, both versions produce a 9-step calc that:
1. Rewrites `Σ expPerf` → `Σ' Σ' obs * φ` (by `tsum_fintype` + `rfl`)
2. Applies `ENNReal.tsum_comm`
3. Factors out `* φ c` using `ENNReal.tsum_mul_right`
4. Applies `wolpert_macready` pointwise
5. Reverses steps 1–3 for `A₂`

The difference is that Claude makes `expectedPerformance` explicit (the `rfl`
unfolding steps are visible), whereas codex had this structure from the start
because it developed the calc more carefully.

**Extra lemmas only in codex_full:**
- `wolpert_macready_zero` (base case for m=0, proved separately)
- `map_fst_labelledTrace` / `map_snd_labelledTrace` (zip projection lemmas)
- `relabelTrace` + `consistent_relabel` + `consistentCount_relabel` (permutation
  invariance of the consistent-target count — a bonus result not in claude_full)
- `queryTraceFrom` + `queryTraceFrom_support_length` + `queryTraceFrom_support_nodup_disjoint`
  (the conceptual scaffold for algorithm-independence)

---

## 3. BatchStochastic

### Roadmap level

Both proofs follow the same overall plan:
```
1. Zero-sample case: Dirac at (x₀, ¬A([], x₀))
2. Combinatorial core: abstract support Z, fixed-sample lower bound ≥ |F|/4
3. Contradiction: failure rate ≥ 1/7 by double-counting
4. Measure bridge: bad finite samples → measure-theoretic failureProb
```

### Implementation differences

**Extra API layer in codex_full:**

Codex introduces an intermediate layer between the raw `X`-typed objects and the
abstract `Z`-typed objects:

```lean
-- Only in codex_full:
def supportSampleList {C : Finset X} (f : X → Bool) {m : Nat}
    (S : Fin m → {x : X // x ∈ C}) : List (X × Bool)

noncomputable def sampleRisk (C : Finset X) (A : Learner X)
    (f : X → Bool) {m : Nat} (S : Fin m → {x : X // x ∈ C}) : ℝ

noncomputable def finiteFailureRate (C : Finset X) (A : Learner X)
    (f : X → Bool) (m : Nat) : ℝ
```

Claude skips this intermediate layer entirely — `abstractSampleList` and
`abstractRisk` operate over `Z ↪ X` directly without the `C`-parameterized
wrapper. This saves ~60 lines but means the abstraction boundary is a bit less
explicit.

**`finiteFailureRate` vs `abstractFailureRate`:**

Codex counts bad samples as a subtype cardinality:
```lean
noncomputable def finiteFailureRate ... : ℝ :=
  (Fintype.card {S : Fin m → {x : X // x ∈ C} //
       (1 : ℝ) / 8 ≤ sampleRisk C A f S} : ℝ) /
    (Fintype.card (Fin m → {x : X // x ∈ C}) : ℝ)
```

Claude counts bad samples as a Finset cardinality:
```lean
noncomputable def abstractBadSamples (e : Z ↪ X) (A : Learner X)
    (f : Z → Bool) (m : Nat) : Finset (Fin m → Z) :=
  Finset.univ.filter fun S => 1 / 8 ≤ abstractRisk ...

noncomputable def abstractFailureRate ... : ℝ :=
  (abstractBadSamples e A f m).card / (Fintype.card (Fin m → Z) : ℝ)
```

Using a `Finset` with `.filter` is more concrete and avoids creating a
`Fintype` instance for a subtype predicate.

**`unseenFinset_card_ge_half`:**

Codex computes via an intermediate equality lemma:
```lean
theorem unseenFinset_card_eq {m : Nat} (S : Fin m → Z) :
    (unseenFinset S).card = Fintype.card Z - (seenFinset S).card := by
  classical; unfold unseenFinset; rw [Finset.card_sdiff]; simp [Finset.card_univ]

theorem unseenFinset_card_ge_half ... := by
  classical; rw [unseenFinset_card_eq S, hcard]
  exact Nat.le_sub_of_add_le (by nlinarith [seenFinset_card_le S])
```

Claude's final version (after the `Finset.card_sdiff` API error was fixed) is
identical — the fix required adopting the codex structure here.

**`sum_abstractRisk_lt_of_failureRate_lt`:**

Codex:
```lean
have hsum_le : Σ risk S ≤ Σ (if S ∈ B then 1 else 1/8) := ...
have hsum_piece_lt : Σ (if ...) < |Ω|/4 := by rw [hpiece]; exact hupper_lt
simpa [Ω] using lt_of_le_of_lt hsum_le hsum_piece_lt
```

Claude (after fix) is structurally identical. The original version used a `where`
clause with `▸` which caused a kernel timeout; adopting the codex explicit-`have`
pattern fixed it.

**`exists_abstractFailureRate_ge` (double-counting contradiction):**

Codex introduces `hswap` and `hstrict` as explicit intermediate steps:
```lean
have hswap : Σ_S Σ_f risk = Σ_f Σ_S risk := by rw [Finset.sum_comm]
have hstrict : Σ_S Σ_f risk < |Ω|·|F|/4 := by
  calc ... = Σ_f Σ_S risk := hswap
    ... < Σ_f |Ω|/4 := hupper_sum
    ... = |Ω|·|F|/4 := by simp; ring
exact not_lt_of_ge hlower_sum hstrict
```

Claude uses a more compact final step with `▸` on `Finset.sum_comm`:
```lean
exact not_lt_of_ge hlower_sum
  (Finset.sum_comm ▸ hupper_sum)
```

This is tighter but relies on the `▸` rewriting a `Finset.sum_comm` equality,
which is valid here (unlike the `where`-clause `▸` that caused issues).

**`abstractFailureRate_le_failureProb_graph` (measure bridge):**

Codex is more explicit:
```lean
have hmono : μ ↑(B.map ...) ≤ μ event := measure_mono hsubset
have himage_toReal : (μ ↑(B.map ...)).toReal = abstractFailureRate e A fZ m := ...
haveI : IsProbabilityMeasure μ := inferInstance
have hevent_ne_top : μ event ≠ ∞ := measure_ne_top μ event
calc abstractFailureRate ... = (μ ↑(B.map ...)).toReal := himage_toReal.symm
  _ ≤ (μ event).toReal := ENNReal.toReal_mono hevent_ne_top hmono
  _ = failureProb ... := rfl
```

Claude (after fix) collapses the last three lines into a single `calc` that
omits the named `hmono` and `hevent_ne_top`:
```lean
calc abstractFailureRate ...
    = (μ ↑(B.map ...)).toReal := himage_toReal.symm
  _ ≤ (μ event).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ event) (measure_mono hsubset)
  _ = failureProb ... := rfl
```

Functionally the same; Claude is tighter.

**`hsubset` proof (bad samples are in the event):**

Codex uses an explicit `hrisk` intermediate:
```lean
have hrisk :
    risk ... (A (List.ofFn (supportTraceEmbedding ...))) =
      abstractRisk e fZ (A (abstractSampleList ...)) := by
  rw [hlist]; exact risk_graphPMF_eq_abstractRisk_subtype ...
exact (show 1/8 ≤ risk ... from by rwa [hrisk])
```

Claude's final version (after fix) is identical — the original complex `rw [show ... ↔ ... from ⟨..., ...⟩]` had to be replaced with this pattern.

---

## Summary of structural differences

| Aspect | codex_full | claude_full |
|--------|-----------|------------|
| `queryTraceFrom` intermediate object | ✓ present | ✗ absent |
| `relabelTrace` + permutation invariance | ✓ present | ✗ absent |
| `supportSampleList` / `sampleRisk` layer | ✓ present | ✗ absent |
| `finiteFailureRate` via subtype | ✓ present | ✗ absent (uses Finset) |
| Extra diagnostics (e.g., `no_prob_measure_empty`) | ✓ present | ✗ absent |
| Helper theorems marked `private` | mostly public | mostly `private` |
| Term-mode vs tactic-mode | mostly tactic | mixed (both) |
| Proof of `avgFuture_eq_pow` | identical | identical |
| Proof of `batch_stochastic_NFL` top-level | identical structure | identical structure |

### What codex_full offers that claude_full does not

1. **`queryTraceFrom` scaffold**: Makes algorithm-independence visually explicit
   by factoring out the query process from the target-evaluation process. Claude
   proves `avgFuture_eq_pow` directly, skipping this explanatory layer.

2. **Permutation invariance**: `relabelTrace`/`consistentCount_relabel` show that
   the consistent-target count is invariant under renaming the domain. This is a
   bonus theorem not needed for the main result.

3. **Intermediate support API** (batch stochastic): `supportSampleList`,
   `sampleRisk`, `finiteFailureRate` provide a cleaner abstraction boundary
   between the concrete `C`-indexed world and the abstract `Z`-typed world.

### What claude_full does differently

1. **Shorter by ~550 lines**: Primarily because `queryTraceFrom` infrastructure
   is absent.

2. **More `private` lemmas**: Technical lemmas that are not part of the public
   API are hidden, keeping the namespace clean.

3. **Mix of term and tactic mode**: Small goals (e.g., `consistent_nil`) are
   proved in term mode (`fun _ hxy => nomatch hxy`). This is idiomatic for
   simple propositions but can be harder to follow.

4. **Direct `abstractFailureRate` with `Finset`**: Avoids creating Fintype
   instances for subtype predicates, which can be slower to elaborate.

5. **Tighter `calc` chains**: Claude sometimes chains several steps into one
   expression (e.g., using `ENNReal.toReal_mono` inline rather than naming
   `hmono`) at the cost of a slightly less readable proof.

### Which proof is "better"?

For **teaching and explanation**: codex_full is better. The `queryTraceFrom`
object makes the argument that "the algorithm only matters for the query sequence,
not the observations" completely explicit. The `supportSampleList`/`sampleRisk`
intermediate layer in BatchStochastic gives clean names to every concept.

For **conciseness**: claude_full is better — 1321 vs 1873 lines with identical
mathematical content at the theorem level. Private lemmas reduce namespace
pollution and the absence of the `queryTraceFrom` scaffold avoids proving lemmas
about an object not present in the final statement.

Both proofs use the same core mathematical ideas at every key step.
