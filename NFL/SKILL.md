# Claude Code Skills — NFL Lean Formalisation

Three custom Claude Code skills were developed during this project to enable AI-assisted formal proof writing in Lean 4. They form a pipeline: `/plan` → `/proof_write` → `/proof_check`.

---

## `/plan`

**Purpose:** Decompose a theorem into named sub-goals before writing any Lean code.

**Behaviour:**
- Reads the theorem statement and the informal proof source (paper, homework writeup)
- Identifies logical sub-goals: helper definitions, key lemmas, bridging steps
- Writes a structured roadmap markdown with `done` / `todo` markers for each sub-goal
- Saves a checkpoint of the current file state so future sessions can resume without re-deriving context

**Exit condition:** A complete roadmap file exists and all sub-goals are named.

**Why it matters:** Without a roadmap, AI generates `sorry`-filled fragments with no plan for completing them. The roadmap gives the AI a bounded local task at each step rather than an open-ended proof search.

---

## `/proof_write`

**Purpose:** Iteratively fill each `sorry` placeholder until `lake build` passes.

**Behaviour:**
- Takes the current `.lean` file (with `sorry` stubs placed by `/plan`)
- Enters a compilation loop:
  1. Attempt a proof for the current `sorry`
  2. Run `lake build` and capture diagnostics
  3. Read error messages and type mismatches
  4. Fix and repeat
- **Compilation = exit condition.** The loop stops when `lake build` reports zero errors for the current sub-goal.
- Proceeds sub-goal by sub-goal following the `/plan` roadmap

**When to use:** Immediately after `/plan` produces a roadmap. One invocation per sub-goal is typical.

---

## `/proof_check`

**Purpose:** Audit a completed Lean file for hidden `sorry`s, admitted axioms, and vacuous proofs.

**Behaviour:**
- Scans the file for `sorry`, `admit`, `native_decide` used as proof, and non-kernel axioms
- Reports each occurrence with file path and line number
- Flags any axiom beyond the standard Lean 4 kernel (`propext`, `funext`, `Classical.choice`, `Quot.sound`)
- Checks that no theorem has a proof body of `by exact?` or similar search placeholders left in

**When to use:** After `/proof_write` completes all sub-goals. Required before claiming a proof is formally verified.
