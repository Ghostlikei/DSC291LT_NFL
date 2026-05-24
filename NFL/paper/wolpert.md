# Reading Guide: Wolpert & Macready (1997), *No Free Lunch Theorems for Optimization*

**Audience**: Graduate Learning Theory peers who know PAC learning, bias–variance, and Bayesian priors.
**Goal**: Internalise the two NFL theorems well enough to present and defend them.

---

## Pass 1 — The one-paragraph version (read first, ~2 minutes)

Across the uniform distribution over all cost functions $f : \mathcal{X} \to \mathcal{Y}$, every black-box optimiser produces the same distribution over cost-value histories. Hill climbing, simulated annealing, evolutionary algorithms, and uniform random search are *indistinguishable on average*. Any algorithm's gain on one class of problems is exactly offset by losses elsewhere. The "skill" of a real-world optimiser is therefore not intrinsic — it is an alignment between the algorithm's inductive bias and the (non-uniform) prior $P(f)$ over problems actually encountered. This is the optimisation analogue of Wolpert's earlier NFL for supervised learning.

---

## Pass 2 — The framework you must be fluent in (read second, ~10 minutes)

Four objects do all the work. Be able to state these without notes.

1. **Sample**: $d_m = \{(x_1, y_1), \ldots, (x_m, y_m)\}$ — the time-ordered set of $m$ **distinct** points queried so far. The "distinct" qualifier is important: it removes the artefact of algorithms wastefully revisiting points, so two algorithms are compared on equal oracle budgets.
2. **Algorithm**: a deterministic map $a : d \mapsto x \notin d^x$. Given any sample, output the next previously-unvisited query. This covers SA, GAs, hill climbing, tabu search — anything that doesn't peek at $f$'s analytic structure. (Branch-and-bound is excluded.)
3. **Performance**: fully encoded by $P(d_m^y \mid f, m, a)$ — the probability the algorithm produces cost-value sequence $d_m^y$ on cost function $f$ after $m$ queries. Any scalar performance measure $\Phi(d_m^y)$ (best-so-far, mean, etc.) is a function of this.
4. **Prior**: $P(f)$ over $\mathcal{F} = \mathcal{Y}^{\mathcal{X}}$. The set $\mathcal{F}$ has $|\mathcal{Y}|^{|\mathcal{X}|}$ elements — large but finite.

**Why probability theory if the algorithm is deterministic?** Three reasons: (i) extends cleanly to stochastic algorithms, (ii) provides a clean proof framework, (iii) lets us encode our ignorance of $f$ as a prior even when $f$ is technically fixed.

---

## Pass 3 — The theorems and their proof intuitions (read third, ~20 minutes)

### Theorem 1 (Static NFL)

$$\sum_{f \in \mathcal{F}} P(d_m^y \mid f, m, a_1) = \sum_{f \in \mathcal{F}} P(d_m^y \mid f, m, a_2) \quad \text{for any } a_1, a_2.$$

**What it actually says**: fix a target cost-value sequence $d_m^y$ you'd like to obtain. The number of cost functions on which algorithm $a$ achieves exactly that sequence is the *same* for every $a$. Average over $f$ and all algorithms look identical.

**Proof sketch (Appendix A)** — induction on $m$.

- *Base case* ($m=1$): The algorithm's first query is some fixed $x_1$ (it has no sample yet). The event "$d_1^y = y$" requires $f(x_1) = y$, which fixes one coordinate of $f$ and leaves $|\mathcal{X}|-1$ coordinates free. So exactly $|\mathcal{Y}|^{|\mathcal{X}|-1}$ functions satisfy it, independent of which $x_1$ the algorithm chose.
- *Inductive step*: Decompose $P(d_{m+1}^y \mid f, m+1, a) = P(d_{m+1}^y(m+1) \mid d_m^y, f, m+1, a) \cdot P(d_m^y \mid f, m, a)$. The next query $x = a(d_m^x, d_m^y)$ depends only on $f$'s values **inside** $d_m^x$, while the new observation $d_{m+1}^y(m+1) = f(x)$ depends only on $f$'s value at a point **outside** $d_m^x$. Split the sum over $f$ into a product of independent sums over these two disjoint subsets of coordinates. The "outside" sum gives a constant $|\mathcal{Y}|^{|\mathcal{X}|-m-1}$ (independent of $a$), and the "inside" sum is the inductive hypothesis (independent of $a$).

**The core insight in one line**: any deterministic algorithm just picks coordinates of $f$ in some order; summing over all $f$ makes every order equivalent.

### Theorem 2 (Time-dependent NFL)

For cost functions evolving via a bijection $T : \mathcal{F} \times \mathbb{N} \to \mathcal{F}$ (so $f_{i+1} = T_i(f_i)$), averaging over **all** $T$ (rather than all $f$) for fixed initial $f_1$ gives the same algorithm-independence — under either of two definitions of the sample.

**Why bijection?** A non-bijective $T$ could funnel $f$ into a region favourable to particular algorithms — that would be an a priori bias, not NFL.

**Proof sketch (Appendix B)**: replace the single sum over $f$ with a chain of sums over $T_1, T_2, \ldots, T_{m-1}$. Each inner sum counts bijections mapping a fixed function to a target — a constant $(|\mathcal{F}|-1)!$, independent of $a$. The remaining algebra mirrors Theorem 1.

### Extension to stochastic algorithms (Section III-B)

Trivial: replace $a$ with a hyperparameter $\sigma$ specifying $P(d_{m+1}^x(m+1) \mid d_m, \sigma)$. The proof goes through identically.

### When NFL holds beyond uniform $P(f)$

This is critical for defending against the "but real problems aren't uniformly distributed" objection. NFL also holds for:

- Any factorisable prior $P(f) = \prod_x P'(f(x))$ — cost values at different points are i.i.d.
- Any prior closed under permutations of rank-ordered cost values.

So uniform $P(f)$ is *typical* among priors yielding NFL, not pathological. The mere *existence* of structure in $P(f)$ is not enough to justify any particular algorithm — the structure must be **known and exploited**.

---

## Pass 4 — The geometric picture (read fourth, ~5 minutes)

This is the most presentation-friendly part of the paper.

Define vectors in $|\mathcal{F}|$-dimensional space:
- $\vec{v}_{d_m^y, a, m}(f) \equiv P(d_m^y \mid f, m, a)$ — the algorithm's "behaviour vector".
- $\vec{p}(f) \equiv P(f)$ — the prior over problems.

Then $P(d_m^y \mid m, a) = \vec{v}_{d_m^y, a, m} \cdot \vec{p}$.

**NFL = all $\vec{v}$ have the same projection onto $\vec{1}$** (the uniform-prior diagonal). Different algorithms sit on a cone around the diagonal; their length is fixed (since $\sum_f P^2 = c(d_m^y, m)$), but their direction off the diagonal varies. An algorithm performs well on a problem class $\vec{p}$ iff $\vec{v}$ points in a similar direction to $\vec{p}$ — i.e., iff the algorithm is **aligned** with the true prior.

This reframes "good algorithm for problem class X" as a geometric matching condition, not an intrinsic property.

---

## Pass 5 — Calculational consequences (skim, return as needed)

You don't need to memorise these formulas for a presentation, but you should know they exist as evidence the framework is more than a curiosity.

- **Theorem 3**: fraction of $f$ giving histogram $\vec{c}$ is multinomial / $|\mathcal{Y}|^m$ — for large $m$, dominated by $\exp[m S(\vec{\alpha})]$ where $S$ is Shannon entropy. Information-theoretic quantities appear *because of* NFL: since the answer is algorithm-independent, you can pick the simplest algorithm (canonical-order enumeration) to compute it.
- **Theorem 4**: fraction of *algorithms* producing $\vec{c}$ on fixed $f$ (with value histogram $\vec{\beta}$) decays as $\exp[-m \, D_{KL}(\vec{\alpha} \| \vec{\beta})]$.
- **Theorems 5–7**: three benchmarks for whether your algorithm has actually beaten chance — (i) the $f$-averaged best-so-far, (ii) the random algorithm's performance, (iii) the fraction of all algorithms you've beaten on this $(f, m)$. If you're below the median on (iii), you've performed worse than half of all conceivable algorithms.

The takeaway: NFL is constructive, not just negative. It lets you compute baselines.

---

## Pass 6 — Subtleties to be ready for in Q&A

### "But surely SA beats random search on real problems?"
Yes — because real problems are not uniformly distributed. SA's bias toward local search aligns with the local-correlation structure of typical engineering problems. NFL says this alignment must be *paid for* by SA's poor performance on problems where local structure is misleading (deceptive functions, needle-in-haystack).

### "Doesn't NFL contradict the existence of universal learners?"
No. PAC-style universal learners assume restricted hypothesis classes or smoothness conditions on the target — they encode a non-uniform prior. NFL is consistent with all such results; it just says you cannot have universality *without* such restrictions.

### "Head-to-head minimax distinctions"
Section VI shows NFL does **not** preclude asymmetries on individual $f$. Example (Appendix F, $|\mathcal{X}|=|\mathcal{Y}|=3$): two algorithms where $a_1$ beats $a_2$ dramatically on some $f$ but never loses dramatically on any $f$. The averages still match because $a_2$ wins on many $f$ by tiny margins. **Theorem 9** rules this out when the two algorithms' sampled $x$-sets never overlap — relevant when comparing two hill climbers started far apart.

### "What about choosing procedures?"
Section VII / Theorems 10–11: even on a *fixed* $f$, picking between two algorithms based on their observed performance carries no a priori justification. The "rational" choosing procedure (use the one with the better sample so far) has the same expected future performance as the "irrational" one (use the worse one) when averaged over algorithm pairs. Past performance on $f$ does not predict future performance on $f$ without further assumptions linking the algorithms to $f$.

### "Is this a deep result or a tautology?"
Mathematically it is almost a counting argument — every $f$ appears once in the sum, every algorithm visits coordinates in some order, end of story. The depth is *conceptual*: it forces the field to abandon vague claims of algorithmic superiority and articulate what prior is being assumed.

---

## A 10-minute presentation outline

1. **Hook** (1 min): "Which is better — simulated annealing or random search? Trick question."
2. **Setup** (2 min): finite $\mathcal{X}, \mathcal{Y}$; the four objects; the "distinct queries" convention.
3. **Theorem 1 statement and intuition** (2 min): equation on slide; explain in words; sketch the inductive proof at the "split $f$ into inside/outside $d_m^x$" level.
4. **Geometric picture** (2 min): the cone diagram (Fig. 1); algorithms differ by where they point off the diagonal; performance = alignment with $\vec{p}$.
5. **Implications and caveats** (2 min): NFL extends to time-varying problems, stochastic algorithms, many non-uniform priors; head-to-head asymmetries still possible; choosing procedures gain you nothing a priori.
6. **Q&A** (1 min): the "but real problems" objection and the PAC-comparison are the two you should rehearse.

---

## Sections you can safely skip on first read

- Appendix B's algebra (the $D_m^y$ case) — know that Theorem 2 has two sample-definition variants and both yield NFL; the algebra is bookkeeping.
- Appendices C–H — only revisit if a peer asks about a specific theorem.
- The detailed discussion of $\Omega(\varepsilon)$ in Theorem 6 — the existence and form of the benchmark matters more than the closed-form expression.

---

## Connection to course themes (for framing)

NFL for optimisation is the direct analogue of Wolpert's earlier NFL for supervised learning ([Wolpert, 1996], reference [11] in the paper). Both say: averaged over all possible targets, all learners/optimisers are equivalent; learning/optimisation succeeds only via prior assumptions that align with the true distribution. This is the formal counterpart to the **inductive bias** discussion that pervades learning theory — VC dimension, regularisation, and structural risk minimisation are all ways of encoding such bias. NFL tells you why that encoding is mandatory, not optional.