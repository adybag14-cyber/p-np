// Optional external validation against MEDDLY 0.18.1.
#include "meddly.h"
#include <cstdlib>
#include <iostream>
#include <vector>

using namespace MEDDLY;

static void run_case(int n, int modulus) {
    std::vector<int> bounds(n, 2);
    domain* d = domain::createBottomUp(bounds.data(), n);
    forest* f = forest::create(
        d, SET, range_type::INTEGER, edge_labeling::EVPLUS);

    dd_edge sum(f);
    f->createConstant(0L, sum);
    const rangeval terms[2] = {rangeval(0L), rangeval(1L)};

    for (int level = 1; level <= n; ++level) {
        dd_edge variable(f), next(f);
        f->createEdgeForVar(level, false, terms, variable);
        apply(PLUS, sum, variable, next);
        sum = next;
    }

    minterm assignment(f);
    rangeval result;
    const unsigned long long total = 1ULL << n;

    for (unsigned long long mask = 0; mask < total; ++mask) {
        long expected = 0;
        for (int level = 1; level <= n; ++level) {
            const int bit = int((mask >> (level - 1)) & 1ULL);
            assignment.setVar(level, bit);
            expected += bit;
        }

        sum.evaluate(assignment, result);
        const long actual = long(result);
        if (actual != expected || actual % modulus != expected % modulus) {
            std::cerr << "mismatch n=" << n << " q=" << modulus
                      << " mask=" << mask << " got=" << actual
                      << " expected=" << expected << '\n';
            std::exit(2);
        }
    }

    std::cout << modulus << ' ' << n << ' '
              << sum.getNodeCount() << ' ' << sum.getEdgeCount() << ' '
              << total << " verified\n";

    forest::destroy(f);
    domain::destroy(d);
}

int main() {
    initialize();
    std::cout << "q n nodes edges assignments status\n";
    for (int modulus : {2, 3, 4, 5, 7}) {
        for (int n : {1, 2, 4, 8, 12, 16}) {
            run_case(n, modulus);
        }
    }
    cleanup();
    return 0;
}
