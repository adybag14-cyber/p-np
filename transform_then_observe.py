from __future__ import annotations

import itertools
import random
import time
from pathlib import Path

from nonlinear_observable_search import beam_features, feature_pool, verify_result
from optimal_obdd import best_obdd, function_table
from reversible_beam_search import beam_network_search
from reversible_transform_obdd import best_linear_seed, special_basis_for


def run() -> str:
    seed_value = 0x7A4F_0B5E
    rng = random.Random(seed_value)
    started = time.perf_counter()
    n = 6
    orders = tuple(itertools.permutations(range(n)))
    pool = feature_pool(n, nonlinear=True)

    functions: list[tuple[str, int]] = [
        ("parity-6", function_table(n, lambda bits: sum(bits) % 2 == 1)),
        ("majority-6", function_table(n, lambda bits: sum(bits) >= 3)),
        ("exact-one-6", function_table(n, lambda bits: sum(bits) == 1)),
        ("exact-two-6", function_table(n, lambda bits: sum(bits) == 2)),
        ("equality-halves-3+3", function_table(n, lambda bits: bits[:3] == bits[3:])),
        (
            "inner-product-3",
            function_table(
                n,
                lambda bits: sum(int(bits[i] and bits[i + 3]) for i in range(3)) % 2 == 1,
            ),
        ),
    ]
    functions.extend((f"random-6-{i + 1}", rng.getrandbits(1 << n)) for i in range(10))

    lines = [
        "Reversible-transform then nonlinear-observable experiment",
        f"seed={seed_value}",
        "Every transform is bijective and every learned feature partition is checked for constant truth value on each fiber.",
        "",
    ]

    for label, relation in functions:
        original_features = beam_features(relation, n, pool, width=96, max_features=6)
        verify_result(relation, n, original_features)

        ordinary = best_obdd(relation, n, orders)
        linear = best_linear_seed(
            relation,
            n,
            ordinary,
            rng,
            samples=350,
            special_bases=special_basis_for(label, n),
        )
        transformed = beam_network_search(
            relation,
            n,
            linear,
            beam_width=12,
            max_depth=4,
        )
        transformed_features = beam_features(
            transformed.table,
            n,
            pool,
            width=96,
            max_features=6,
        )
        verify_result(transformed.table, n, transformed_features)

        lines.append(
            f"{label}: original-k={len(original_features.selected)}, "
            f"original-image={original_features.image_size}, "
            f"transformed-k={len(transformed_features.selected)}, "
            f"transformed-image={transformed_features.image_size}, "
            f"network-gates={len(transformed.gates)}, obdd={ordinary.size}->{transformed.diagram.size}, "
            f"features=[{', '.join(feature.name for feature in transformed_features.selected)}]"
        )

    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("transform-then-observe-output.txt").write_text(output, encoding="utf-8")
