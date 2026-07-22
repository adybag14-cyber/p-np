from pathlib import Path

import residual_search as r

SEED = 0x46524F4E54
r.rng.seed(SEED)

lines = ["Frontier-order experiment", f"seed={SEED}", ""]

eq_table = r.equality_halves_table(6)
eq_graph = r.matching_graph(6)
split = tuple(range(12))
paired = tuple(i for pair in zip(range(6), range(6, 12), strict=True) for i in pair)
lines.append(
    "equality-6+6: "
    f"split residual={r.width(eq_table, split)}, split frontier={r.frontier_width(split, eq_graph)}, "
    f"paired residual={r.width(eq_table, paired)}, paired frontier={r.frontier_width(paired, eq_graph)}"
)
lines.append("")

for index, clause_count in enumerate((24, 36, 48), start=1):
    formula, table = r.random_k_cnf(12, clause_count, 3)
    graph = r.primal_graph(12, formula)
    natural = tuple(range(12))
    direct_width, direct_order, direct_profile = r.tuned_width(table, restarts=2)
    graph_order, graph_frontier = r.tune_frontier_order(graph, restarts=64)
    graph_width = r.width(table, graph_order)
    lines.append(
        f"random-3CNF-{index}: clauses={clause_count}, satisfying={int(table.sum())}/4096, "
        f"natural-width={r.width(table, natural)}, natural-frontier={r.frontier_width(natural, graph)}, "
        f"direct-width={direct_width}, direct-frontier={r.frontier_width(direct_order, graph)}, "
        f"graph-width={graph_width}, graph-frontier={graph_frontier}, "
        f"direct-order={direct_order}, graph-order={graph_order}, direct-profile={direct_profile}"
    )

output = "\n".join(lines) + "\n"
print(output, end="")
Path("frontier-search-output.txt").write_text(output, encoding="utf-8")
