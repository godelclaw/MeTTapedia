import unittest
from itertools import permutations

from v24_protected_mesh_gate import split_grid
from v24_split_grid_chain_gate import cut_sizes, longest_chain


class SplitGridChainTests(unittest.TestCase):
    def test_endpoint_constructors_and_colour_witness(self):
        for r in range(1, 7):
            _, _, graph = split_grid(r, r)
            def a(i, j):
                return 2*(i*r+j)
            typed = [(a(i, j), a(i, j)+1, 0) for i in range(r) for j in range(r)]
            typed += [(a(i, j)+1, a(i, j+1), 1) for i in range(r) for j in range(r-1)]
            typed += [(a(i, j)+1, a(i+1, j), 2) for i in range(r-1) for j in range(r)]
            self.assertEqual({tuple(sorted((u, v))) for u, v, _ in typed},
                             {(u, v) for u in graph for v in graph[u] if u < v})
            for v in graph:
                colours = [c for u, w, c in typed if v in (u, w)]
                self.assertEqual(len(colours), len(set(colours)))
                self.assertLessEqual(len(colours), 3)

    def test_boundary_recurrence_against_direct_edges(self):
        _, _, graph = split_grid(2, 2)
        edges = [(u, v) for u in graph for v in graph[u] if u < v]
        for s, size in enumerate(cut_sizes(graph)):
            self.assertEqual(size, sum(bool(s & (1 << u)) != bool(s & (1 << v))
                                       for u, v in edges))

    def test_all_small_validity_patterns_against_complete_orders(self):
        for pattern in range(256):
            valid = [bool(pattern & (1 << s)) for s in range(8)]
            best = 0
            for order in permutations(range(3)):
                s, score = 0, int(valid[0])
                for v in order:
                    s |= 1 << v
                    score += valid[s]
                best = max(best, score)
            self.assertEqual(longest_chain(valid), best)

    def test_skips_invalid_intermediate_states(self):
        self.assertEqual(longest_chain([True] + [False]*6 + [True]), 2)
        self.assertEqual(longest_chain([True]*8), 4)

    def test_partner_discrepancies_are_cut_edges(self):
        _, _, graph = split_grid(2, 2)
        for s, size in enumerate(cut_sizes(graph)):
            branches = sum(bool(s & (1 << (2*i))) for i in range(4))
            extra = sum(not s & (1 << (2*i)) and bool(s & (1 << (2*i+1)))
                        for i in range(4))
            self.assertLessEqual(extra, size)
            self.assertLessEqual(s.bit_count(), 2*branches+extra)

    def test_tower_comparison_without_materializing_tower(self):
        for k in range(1, 7):
            p = 4*k*k+2*k+1
            self.assertEqual(p < 2**(3**k), p.bit_length() <= 3**k)


if __name__ == '__main__':
    unittest.main()
