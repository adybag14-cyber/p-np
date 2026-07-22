# Seventy-five P-versus-NP formulations

Each item has a Lean-checked logical or finite core. None is presented as a completed proof of `P = NP`.

## 1–15: direct search and residual compression

1. **Exhaustive witnesses** — exact, but the witness type has cardinality `2^m`.
2. **Prefix self-reduction** — reconstructs a witness with one extension query per bit; extension remains NP-hard.
3. **Random sampling** — exact counting of failures; sparse accepting sets defeat polynomial sampling.
4. **Isolation hashing** — injective hashing isolates witnesses; finding a uniformly small useful family is unresolved.
5. **Meet in the middle** — exact for separable predicates; cross-half constraints destroy independence.
6. **Separator DP** — exact when both halves factor through a small signature; signatures may be exponential.
7. **Symmetry quotient** — invariant representatives suffice; orbit canonicalization/count can be hard.
8. **Behavioural traces** — search may move from witnesses to traces; reachable trace count may be exponential.
9. **State merging** — search cost is bounded by distinct states; compact programs can still generate exponentially many.
10. **Arithmetization** — existential OR becomes a product-zero test; the product still has exponentially many factors.
11. **Monotonicity** — all-true decides monotone SAT; unrestricted SAT is not monotone.
12. **Low Boolean rank** — feature aggregation is exact; rank can be exponential.
13. **Kernelization** — exact if a polynomial kernel exists; unrestricted polynomial kernels are the missing claim.
14. **Candidate generators** — exact if generated candidates cover all accepting instances; polynomial coverage is the breakthrough.
15. **Residual automata** — exact DP over reachable residual states; general residual width can be exponential.

## 16–32: barriers, ordering, and certified dispatch

16. **Trivial acceptance quotient** — one-bit acceptance always factors, but constructing it already solves the instance.
17. **Equality-row lower bound** — recoverable encodings of equality rows must be injective.
18. **Distinguishable residuals** — pairwise-separated residuals force distinct machine states.
19. **Singleton hitting-set barrier** — hitting every possible singleton witness requires the full universe.
20. **Recoverable trace barrier** — a trace from which witnesses are recoverable cannot compress cardinality.
21. **Independent blocks** — independent existential blocks compose exactly; general formulas are coupled.
22. **Truth-table advice counting** — arbitrary Boolean functions require exponentially many advice descriptions.
23. **Black-box spike adversary** — an unseen witness can flip the existential answer while matching all queries.
24. **Residual-work accounting** — exact state-level work is levels times states; state count remains decisive.
25. **Compositional local residuals** — local residual models compose when interfaces stay small.
26. **Variable-order sensitivity** — a bad order can create exponential width while a paired order stays tiny.
27. **Frontier signatures** — equal frontier signatures imply equal residuals when factorization is valid.
28. **Shannon branching** — existential acceptance splits exactly on any chosen variable.
29. **Forced literals** — a certified forced bit removes one branch exactly.
30. **Symmetry isomorphism** — renaming-equivalent predicates have the same existential answer.
31. **Certified structural dispatch** — recognized instances may use a fast solver without compromising fallback correctness.
32. **Certified portfolios** — the first returned answer is sound when every partial solver is certified.

## 33–47: decomposition and canonical search

33. **Covered portfolio totality** — a certified portfolio becomes a total decider if every input is covered.
34. **Disjunctive decomposition** — an exact OR factorization reduces one search to two subsearches.
35. **Independent conjunction** — independent component satisfiability is the conjunction of component answers.
36. **Dominance pruning** — a residual whose solutions are contained in another may be deleted.
37. **Semantic normalization** — a semantics-preserving normalizer preserves existential acceptance.
38. **Canonical memoization** — equal canonical keys imply equal answers when semantics factors through the key.
39. **Backdoor search** — enumeration over a backdoor is exact when all solutions are covered.
40. **Polynomial backdoor budget** — explicitly isolates the required bound `2^k <= n^c`.
41. **Entailed learning** — adding a learned constraint entailed by the formula preserves satisfiability.
42. **Boolean resolution** — a resolvent follows from its two parent clauses.
43. **Preprocessing pipelines** — a list of semantics-preserving transforms preserves semantics end to end.
44. **Forced descent** — one unresolved child per level gives linear recurrence, versus `2^d` full branching.
45. **Representative families** — existence is preserved by a subset covering every good candidate.
46. **Decomposition trees** — tree acceptance is exactly the OR of leaf solver answers.
47. **Universal hybrid** — structural recognition and residual fallback compose into one exact decider.

## 48–55: affine structure and proof-carrying coverage

48. **Canonical 3-XOR encoding** — four clauses encode one three-variable parity equation exactly.
49. **Gaussian row addition** — replacing one Boolean linear equation by its XOR with another is reversible.
50. **Zero-row contradiction** — the equation `0 = 1` certifies inconsistency.
51. **Proof-carrying recognition** — a recognized reduced instance carries its own semantic equivalence proof.
52. **Affine dispatch** — a proof-carrying affine solver composes exactly with fallback.
53. **Polynomial cost certificates** — structural costs compose when each branch includes an explicit polynomial bound.
54. **Finite tractable union** — any covered member of a certified family has an exact family solver.
55. **Uniform certified-cover criterion** — a uniform polynomial certified cover yields `NP ⊆ P` abstractly.


## 56–58: exact class-level frontier

56. **Set-level collapse** — a uniform certified cover plus `P ⊆ NP` gives equality of the P and NP language sets.
57. **Exact decider criterion** — with explicit membership/decider bridges, `P = NP` iff every NP language has a polynomial decider.
58. **Obstruction localization** — if the classes differ, some NP language has no polynomial decider.

## 59–68: concrete SAT transformations and cost localization

59. **Separator conditioning** — existential search decomposes exactly after fixing the shared interface.
60. **Pure-literal elimination** — certified positive monotonicity removes the false branch.
61. **Subsumption** — a constraint implied by a stronger one can be deleted.
62. **Autarky pruning** — clauses satisfied by an isolated partial assignment can be removed.
63. **Davis–Putnam elimination** — eliminating a variable by all positive/negative resolvents preserves satisfiability.
64. **Elimination-width accounting** — at most `w²` resolvents arise when both polarities occur at most `w` times.
65. **Bounded elimination schedule** — total local work is at most the number of steps times `w²`.
66. **Three-budget composition** — polynomial preprocessing, polynomially many leaves, and polynomial leaf cost compose.
67. **Cost obstruction localization** — excessive total work forces an expensive leaf when preprocessing and leaf count are bounded.
68. **Logarithmic interfaces** — enumerating `2^k` interface assignments remains polynomial under an explicit `2^k ≤ n^c` certificate.

## 69–75: private-variable peeling and residual cores

69. **Private-variable elimination** — a locally solvable constraint with a private Boolean variable imposes no residual restriction.
70. **XOR leaf solvability** — a 3-XOR equation can always be solved for any selected one of its variables.
71. **XOR leaf peeling** — a private XOR equation can be removed exactly after existentially choosing its leaf variable.
72. **Peel-chain composition** — any finite chain of equisatisfiable peeling steps preserves the answer.
73. **Core localization** — satisfiability and unsatisfiability transfer exactly between the original instance and its residual core.
74. **Small-core budget** — polynomial peeling plus polynomially many core assignments and polynomial checking composes.
75. **Core obstruction** — when peeling is polynomial, excessive total work must reside in the residual core.

## 76-90: proof-carrying AND/OR DAGs

76. **AND/OR decision tree** - syntax for solved leaves, existential OR branches, and independent AND decompositions.
77. **Local validity** - local semantic certificates imply global tree correctness.
78. **Node accounting** - leaf count is bounded by total node count.
79. **Certified compiler** - compiling a valid root-preserving tree gives an exact decider.
80. **Polynomial tree compiler** - an explicit polynomial node bound is sufficient for compactness.
81. **Semantic memo key** - equal keys may reuse exact answers only when semantics factors through the key.
82. **Finite key-space bound** - reachable keys cannot exceed the key type cardinality.
83. **Certified OR branch** - exact branch answers compose by Boolean disjunction.
84. **Certified AND decomposition** - exact component answers compose by Boolean conjunction.
85. **DAG sharing** - processing each finite state once costs at most state count times per-state cost.
86. **Full branching recurrence** - unresolved binary branching has `2^(d+1)-1` nodes.
87. **Layered width** - total DAG nodes are bounded by depth times maximum layer width.
88. **Width-depth polynomial budget** - polynomial width and linear depth compose into a polynomial bound.
89. **Proof-carrying DAG compiler** - an exact bounded-state compiler yields an exact decider.
90. **DAG collapse criterion** - a uniform polynomial exact DAG cover yields `NP subset P` through the standard bridge.

## 91-105: concrete CNF proof trees

91. **Fixed-bit satisfiability** - SAT splits into the false-bit and true-bit cases.
92. **Bit overwrite** - construct an assignment with one selected bit replaced.
93. **Restricted clause avoidance** - clause restriction removes every occurrence of the selected variable.
94. **Restricted formula avoidance** - CNF restriction removes that variable from every residual clause.
95. **Unused-bit invariance** - changing an absent variable cannot change CNF evaluation.
96. **Fixed residual equivalence** - fixing an absent variable does not change satisfiability.
97. **Concrete Shannon theorem** - a CNF is satisfiable iff either Boolean restriction is satisfiable.
98. **Formula-local agreement** - assignments agreeing on all used variables evaluate identically.
99. **Disjoint assignment merge** - satisfying assignments for disjoint supports can be merged.
100. **Concrete AND decomposition** - disjoint CNF concatenation is satisfiable iff both components are.
101. **CNF proof-tree syntax** - concrete branch, conjunction, and solved-leaf certificates.
102. **CNF proof-tree validity** - valid concrete proof trees evaluate exactly.
103. **CNF proof-tree size** - depth is bounded by node count.
104. **Canonical CNF keys** - equal semantics-preserving normal forms safely share answers.
105. **Polynomial CNF certificate compiler** - a valid root-preserving polynomial proof-tree compiler decides SAT.

## 106-120: minimal semantic residual states

106. **Residual function** - each partial computation is represented by its map from completions to answers.
107. **Residual equivalence** - equality on all completions is reflexive, symmetric, and transitive.
108. **Exact state factorization** - a state key and decoder represent every residual answer.
109. **Collision safety** - equal exact states imply equal residual functions.
110. **Canonical residual state** - the residual function itself is an exact state.
111. **Residual and state images** - finite reachable images are materialized explicitly.
112. **Residual lower bound** - every exact state type has at least as many states as distinct residuals.
113. **Canonical optimality** - canonical residual keys achieve exactly the residual image.
114. **Reachable-state bound** - unreachable state values are only redundant overhead.
115. **Residual transitions** - extension transitions make canonical residual states executable.
116. **Layer-width lower bound** - each exact layer width is at least its residual image size.
117. **Residual obstruction** - too many residuals force every exact state space over the budget.
118. **Polynomial necessity** - polynomial exact states imply polynomial residual-image size.
119. **Polynomial residual sufficiency** - an executable exact residual compiler supplies a decider.
120. **Residual collapse criterion** - a uniform polynomial residual compiler yields `NP subset P` through the language bridge.


## 121-135: acceptable ordered-residual compiler skeleton

121. **Ordered witness machine** - an exact deterministic state machine reads one witness bit at a time.
122. **Path correctness** - every witness of the declared length is evaluated exactly.
123. **Residual-model conversion** - an ordered machine induces the previously verified residual model.
124. **Existential decision** - reachable accepting states decide whether any witness is accepted.
125. **Layer-width bound** - every reachable layer is bounded by the finite machine state count.
126. **Layer-work accounting** - depth-plus-one times state count bounds state visits.
127. **Polynomial layer budget** - polynomial witness depth and polynomial width give a polynomial work expression.
128. **Compiled witness family** - each input receives an exact machine plus explicit length, state, and construction bounds.
129. **Non-circular compiled language** - acceptance is defined only by existence of an accepted witness.
130. **Compiled exact decider** - the generated machine decides that witness language exactly.
131. **Compiled work bound** - reachable-state traversal has an explicit polynomial bound.
132. **Total certified cost** - construction cost and traversal cost remain separately visible and compose.
133. **Machine bridge** - an explicit conventional-machine theorem converts compiled families into membership in P.
134. **Collapse criterion** - a uniform compiler for every NP language, plus the standard bridge, proves `P = NP`.
135. **Compiler obstruction** - if `P != NP`, some NP language cannot admit any agreeing compiler of this certified form.

## Current frontier

The best surviving formulation is not “compress every witness set directly.” It is:

1. normalize the instance canonically;
2. learn only entailed constraints;
3. split independent or disjunctive structure;
4. recognize proof-carrying tractable families;
5. quotient isomorphic or behaviourally equal residuals;
6. prune dominated states;
7. use a residual solver only on uncovered leaves;
8. prove that the number and size of all leaves/states is polynomial for every NP instance.

Steps 1–7 are represented by checked components in the workspace. Step 8 is the unsolved global coverage theorem.


## 136-150: adaptive semantic-width branching

136. **Partial residual semantics** - acceptance is existential completion of a partial assignment.
137. **Single-variable assignment** - functional update fixes one selected bit.
138. **Extension characterization** - extending an updated partial assignment equals extending the old state plus matching the selected bit.
139. **Adaptive Shannon branching** - any currently unset variable may be selected, independently at every residual.
140. **Unassigned-variable set** - the exact remaining variable support is represented as a finite set.
141. **Rank decrease** - assigning an unset variable removes exactly one rank unit.
142. **Adaptive search tree** - each internal node stores its own residual-dependent variable choice.
143. **Adaptive validity** - locally certified branches and leaves imply global answer correctness.
144. **Adaptive depth bound** - valid depth is at most the number of unset variables at the root.
145. **Binary-tree ceiling** - an unshared adaptive tree still has the standard exponential ceiling.
146. **Completion equivalence** - equal completion sets are verifier-independent merge certificates.
147. **Semantic aliases** - verifier-specific residual equivalence is sufficient for memoization.
148. **Adaptive DAG budget** - total nodes are bounded by depth times maximum semantic layer width.
149. **Adaptive compiler** - exactness and polynomial node bounds are packaged without assuming the answer.
150. **Adaptive collapse criterion** - a uniform polynomial adaptive compiler family would yield class equality.

## 151-165: global policy optimization and safe baselines

151. **Finite policy result** - a policy exposes its reachable-state set and answer.
152. **State dominance** - reachable-set inclusion implies a cardinality cost bound.
153. **Safe global choice** - choose the smaller of two exact results without losing correctness.
154. **Ordered embedding** - every fixed-order model may be embedded into the adaptive model at equal cost.
155. **Adaptive baseline theorem** - a globally optimal adaptive candidate cannot be worse than any ordered baseline.
156. **Local/global mismatch** - a smaller local recurrence score need not imply a smaller shared graph.
157. **Shared-union identity** - union and intersection cardinalities exactly account for DAG sharing.
158. **Sharing upper bound** - shared expansion never costs more than separate child expansion.
159. **Strict sharing** - nonempty child-state overlap gives a strict cardinality saving.
160. **Improvement chains** - any chain of accepted nonincreasing moves remains below its initial cost.
161. **Search invariant** - accepted moves preserve exactness as well as cost monotonicity.
162. **Exact portfolio fold** - folding safe choices across candidate policies preserves correctness.
163. **Portfolio baseline** - the folded portfolio never exceeds its seed baseline.
164. **Polynomial portfolio accounting** - polynomially many polynomial-cost policies remain polynomial overall.
165. **Policy collapse criterion** - a uniform polynomial exact policy portfolio would yield P = NP.


## 166-180: overlap-aware global accounting

166. **Exact overlap accounting** - branch-union cost plus intersection credit equals the sum of child-state counts.
167. **Overlap upper bound** - overlap cannot exceed either child closure.
168. **Overlap monotonicity** - enlarging both closures cannot reduce their intersection.
169. **Common-core credit** - any certified common core gives a valid sharing discount.
170. **Equal-sum comparison** - with equal child sums, greater overlap cannot worsen union cost.
171. **Strict overlap saving** - strictly greater overlap with equal child sums strictly lowers union cost.
172. **Full reuse** - a candidate contained in existing states adds no new state.
173. **Zero-overlap accounting** - no intersection means union cost equals the child sum.
174. **Portfolio union** - defines the globally reachable state union of a policy portfolio.
175. **Portfolio-union bound** - global union size is at most the sum of individual sizes.
176. **Polynomial portfolio states** - polynomial policy count and polynomial policy width compose.
177. **Separator cross-product** - separator assignments times residual width has the explicit product bound.
178. **Branch potential certificate** - packages exact shared cost and overlap credit.
179. **Monotone potential search** - exact globally measured replacements preserve answers and never increase cost.
180. **Overlap-policy collapse criterion** - uniform polynomial overlap-aware policies imply `P = NP` abstractly.

## 181-195: canonical semantic states and contextual replacement

181. **Canonical representation** - injective exact state-to-node images have equal semantic and concrete cardinality.
182. **Cardinality sign transfer** - node `<` and `<=` comparisons are exactly state comparisons.
183. **Context partition** - separates unaffected graph nodes from old and replacement regions.
184. **Context subset safety** - a replacement-region subset cannot enlarge the total graph.
185. **Context strict saving** - proper total inclusion gives a strict node-count reduction.
186. **Disjoint context accounting** - when context and region do not overlap, local and global costs differ identically.
187. **Local-to-global strictness** - a smaller disjoint replacement region strictly lowers total graph size.
188. **Ancestor-cone budget** - replacement work is bounded by subtree size plus affected depth.
189. **Boundary fingerprint** - stable root key and answer preserve the exported interface.
190. **Intern-key reuse** - equal or already-present keys create no additional node.
191. **Canonical optimality** - a canonical representation attains any semantic lower bound on exact nodes.
192. **Exact delta transfer** - equality and additive node differences transfer to semantic-state differences.
193. **Polynomial state-to-node transfer** - a polynomial semantic-state bound is a polynomial node bound.
194. **Canonical compiler collapse** - uniform canonical polynomial compilers imply class equality.
195. **Canonical compiler obstruction** - class separation forces at least one NP language to lack such a compiler.

## 196-210: coherent least-policy closures

196. **Transition systems** - packages residual states, choices, and finite child transitions.
197. **Policy closure** - defines finite state sets closed under a global policy.
198. **Least closure certificate** - records rootedness, closure, and minimality.
199. **Closure uniqueness** - two least closures for the same root and policy are equal.
200. **Closure cardinality minimality** - the least closure is no larger than any closed rooted candidate.
201. **Policy agreement** - policies agreeing on a set preserve closure of that set.
202. **Finite-domain merge** - merges two policies according to membership in a finite left domain.
203. **Left merge agreement** - the merged policy equals the left policy on the left domain.
204. **Policy compatibility** - child policies must agree on every shared state.
205. **Right merge agreement** - compatibility makes the merged policy equal the right policy on its domain.
206. **Coherent union closure** - compatible closed child policies compose into a closed union.
207. **Coherent union root** - either rooted child makes the union rooted.
208. **Coherent composition certificate** - packages two closed compatible policies and their merged closure.
209. **Coherent composition cost** - merged closure receives the exact overlap discount.
210. **Coherent-policy collapse criterion** - uniform polynomial coherent closures imply `P = NP` abstractly.

## 211-225: dominance and exact-frontier pruning

211. **Policy candidate** - a candidate carries a finite closure and one global policy.
212. **Candidate compatibility** - policies agree on every state shared by their closures.
213. **Candidate dominance** - a smaller closure with identical retained choices dominates a larger one.
214. **Dominance reflexivity** - every candidate dominates itself.
215. **Dominance transitivity** - dominance composes.
216. **Compatibility transfer** - a dominating candidate preserves compatibility with every extension of the dominated candidate.
217. **Candidate union** - composition cost is measured by the union of closures.
218. **Union dominance** - dominance is preserved after union with an external candidate.
219. **Union cost nonworsening** - dominating candidates never increase future composed cost.
220. **Strict union saving** - proper composed inclusion gives strict cost improvement.
221. **Safe pruning** - a dominated candidate may be removed without losing compatible nonworse composition.
222. **Undominated frontier** - no two distinct members safely dominate one another.
223. **Pruning certificate** - records a frontier witness dominating a discarded candidate.
224. **Frontier product budget** - pairwise combination work is bounded by the product of frontier sizes.
225. **Polynomial-frontier collapse criterion** - uniform polynomial undominated frontiers imply `P = NP` abstractly.

## Approaches 226-330: radical representations

226. **Feature quotients preserve existential acceptance**
227. **Universally lossless feature maps cannot reduce cardinality**
228. **Accepted features recover witnesses when fibers have representatives**
229. **Sparse feature descriptions have linear total support cost**
230. **Polynomially many features with polynomial evaluation remain polynomial**
231. **Canonical orbit representatives preserve invariant predicates**
232. **Orbit representatives decide existential acceptance**
233. **Orbit images are bounded by the orbit type**
234. **Separator tensor products have explicit state cost**
235. **Low-rank feature factorizations reduce existential search to feature pairs**
236. **Deterministic isolation families cover all accepted witnesses**
237. **Unique isolation makes witness recovery unambiguous**
238. **Entailed learned constraints preserve the model set**
239. **Proof-trace checkers transfer correctness to compiled answers**
240. **A uniform radical representation cover yields class collapse**
241. **Bijective coordinate changes preserve existential acceptance**
242. **Coordinate transformations compose**
243. **A feature quotient is constant on every feature fiber**
244. **Distinguishable witnesses must receive different exact feature codes**
245. **Exact transformed machines decide the original relation**
246. **Finite transformed state budgets bound reachable images**
247. **Polynomially bounded affine coset counts remain polynomial**
248. **Sparse algebraic normal forms have sparse evaluation cost**
249. **Sparse spectral features need only their support image**
250. **Exact linear sketches may collide only on equal answers**
251. **A finite family of exact sketches has a union state bound**
252. **Proof-carrying radical certificates need only checker soundness**
253. **Polynomial hash families with polynomial checks remain polynomial**
254. **A radical portfolio may dispatch to any exact polynomial representation**
255. **Uniform transformed or sketched deciders yield P = NP**
256. **The unrestricted ordered linear-form search space is quadratic-exponential**
257. **All ordered n-tuples of Boolean linear-form masks have size 2^(n^2)**
258. **Any one-bit feature has at most two reachable feature states**
259. **A k-bit sketch has at most 2^k reachable states**
260. **Concrete parity is a one-bit witness feature**
261. **Parity therefore has at most two semantic feature states**
262. **Bijective basis changes preserve satisfiability before feature compression**
263. **A listed candidate family succeeds whenever it contains a good transform**
264. **Polynomial transform families with polynomial compilation remain polynomial**
265. **Independent linear equations reduce search to their syndrome image**
266. **A relation depending only on a syndrome is safely quotientable**
267. **A known parity coordinate gives a constant-size decision representation**
268. **Linear preprocessing cost plus bounded-state traversal composes additively**
269. **Exponential full-basis enumeration localizes the construction obstruction**
270. **Uniform polynomial linear-basis sketches would collapse P and NP**
271. **Canonicalization induces an equivalence relation**
272. **Canonical images never exceed the raw residual set**
273. **A genuine canonical collision gives strict compression**
274. **Invariant answers factor through canonical states**
275. **The full variable-renaming family has n! elements**
276. **A polynomial generator family avoids factorial enumeration**
277. **Relabeling by an equivalence preserves existential acceptance**
278. **Automorphism orbits safely merge invariant residuals**
279. **A checked canonicalizer transfers answers soundly**
280. **Polynomially many symmetry quotients have a polynomial union bound**
281. **Linear and symmetry features compose into product features**
282. **Product feature state counts multiply**
283. **Polynomial canonicalization and traversal costs compose**
284. **A finite radical portfolio is complete when one member covers each input**
285. **Uniform polynomial symmetry-linear portfolios yield P = NP**
286. **A covering restriction family preserves satisfiability**
287. **Exact residual solvers compose with a restriction cover**
288. **Polynomial restriction families with polynomial residual solvers remain polynomial**
289. **Fixing variables leaves the expected Boolean search ceiling**
290. **A polynomial residual-dimension bound gives polynomial enumeration**
291. **Switching certificates expose shallow residual decision trees**
292. **Polynomially bounded depth ceilings imply explicit leaf ceilings**
293. **A restriction ensemble of shallow trees has multiplicative cost**
294. **A common sunflower core is charged once across petals**
295. **Exact kernelization transfers decisions back to the source instance**
296. **Learned proof traces remain sound after restriction**
297. **Strict rank decrease bounds every restriction chain**
298. **Isolation and restriction certificates compose**
299. **A heterogeneous radical cover may choose restrictions, symmetry, or algebra**
300. **Uniform polynomial restriction covers would collapse P and NP**
301. **Every involution defines a reversible coordinate transform**
302. **Reversible gate networks compose into one exact transform**
303. **Reversible networks preserve existential acceptance**
304. **Reversible preprocessing preserves the number of assignments**
305. **A transformed relation may then be quotiented by a small feature**
306. **Linear gate-count and per-gate work compose multiplicatively**
307. **Polynomial preprocessing plus polynomial traversal stays polynomial**
308. **A polynomial portfolio of reversible networks has polynomial total work**
309. **Monotone network search never exceeds its seed representation**
310. **Seeding with an ordinary representation guarantees baseline dominance**
311. **Nonlinear feature collisions remain safe only under answer constancy**
312. **Reversibility alone cannot reduce assignment cardinality**
313. **Compression must therefore occur after the reversible transform**
314. **Checked reversible networks transfer answers soundly**
315. **Uniform polynomial reversible-feature compilers yield P = NP**
316. **Accepted witnesses can be counted exactly over a finite type**
317. **The accepted count is zero exactly when no witness is accepted**
318. **Positive accepted count is equivalent to an accepted witness**
319. **Accepted count is bounded by the witness-space cardinality**
320. **An n-bit witness language has at most 2^n accepted witnesses**
321. **Reduction modulo a larger modulus preserves the exact count**
322. **Under a large modulus, zero residue is equivalent to zero count**
323. **Modulus 2^n + 1 decides whether an n-bit witness exists**
324. **A nonzero large-modulus residue certifies existence**
325. **Counts multiply across independent witness components**
326. **Counts add across a disjoint separator partition**
327. **A width-w Boolean tensor table has 2^w entries**
328. **A polynomial tensor-table bound transfers directly to contraction work**
329. **Polynomial modular-residue compilers decide finite witness existence**
330. **Uniform polynomial exact-residue compilers would collapse P and NP**


## Approaches 331-345: certified learned reversible compilers

A331-A335 package exact candidates, identity baselines, globally measured improvement
steps, monotone chains, and baseline-retaining beam outputs. A336 counts depth-d gate
networks exactly as |Gate|^d. A337-A342 account for candidate enumeration, exact replay,
construction/evaluation cost, and certificate length. A343-A345 prove exact portfolio
selection and the conditional class collapse from a uniform polynomial learned compiler.

## Approaches 346-360: nonlinear observable quotients

A346 defines k-observable signatures. A347-A350 prove exact factorization through
noninjective signatures, existential reduction to the reachable image, the 2^k image
bound, and the distinction between decision-safe compression and lossless recovery.
A351-A358 prove refinement, product-feature, lower-bound, evaluation-cost, portfolio,
collision-certificate, and reachable-image lemmas. A359-A360 package the fully costed
nonlinear compiler and its conditional collapse theorem.

## Approaches 361-375: opposite-pair separation covers

A361-A368 identify opposite-label pairs as the exact collision obligations and prove
that complete feature separation is equivalent to fiber safety. A369-A372 establish
coverage monotonicity, union accounting, witness-pair cardinality, and checking cost.
A373 proves that the explicit pair universe for n-bit witnesses has size 2^(2n).
A374-A375 isolate structural separation certificates and the uniform polynomial-cover
collapse criterion.

## Approaches 376-390: baseline-safe transform-feature portfolios

A376-A380 prove transport of opposite pairs, arbitrary feature pullback, fiber safety,
and exact reachable-image cardinality through a bijection. A381-A388 prove that keeping
both original and transformed exact quotients cannot worsen the baseline, with explicit
network/feature/portfolio cost and certificate composition. A389-A390 package the
combined compiler and conditional P = NP theorem.
