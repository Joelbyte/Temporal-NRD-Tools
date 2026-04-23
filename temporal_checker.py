"""
Temporal Pattern Preservation Checker
======================================

Setting: domain (Q, <) — the rationals with their natural order.
A temporal relation R of arity r is given as a finite set of orbit
representatives.  Each representative is a tuple of non-negative integers
encoding an order-type: e.g. (0,1,2) means x0 < x1 < x2, and (0,1,0)
means x0 = x2 < x1.  More precisely, a tuple (a0,...,a_{r-1}) encodes the
orbit {(q0,...,q_{r-1}) in Q^r : qi < qj iff ai < aj, qi = qj iff ai = aj}.

A pattern P of arity k is a set of identities.  Each identity has a template
(tuple of variable indices of length k) and an output position.  The induced
partial function f: Q^k -> Q is defined at (q0,...,q_{k-1}) iff the equality
constraints are satisfied, and returns q_i.

f preserves R iff: for all k-tuples of R-rows, whenever f is defined on
every column, the result tuple is in R.

Two approaches:
  1. Brute force: enumerate all types on the k*r matrix positions
  2. SAT: encode order variables with transitivity constraints
"""

from itertools import product as iproduct
import time
import sys


# ============================================================================
#  Linear preorders (types / order-types)
# ============================================================================

def canonical(t):
    """Canonicalise a tuple so ranks are contiguous from 0, preserving order.
    E.g. (3,1,3,5) -> (1,0,1,2) because 1<3<5 maps to 0<1<2."""
    mapping = {}
    # Preserve ORDER among values, not first-appearance order.
    # We want: if t[i] < t[j] then result[i] < result[j].
    vals = sorted(set(t))
    rank = {v: i for i, v in enumerate(vals)}
    return tuple(rank[v] for v in t)

def to_orbits(tuples):
    """Convert a list of tuples to deduplicated canonical orbit representatives."""
    return sorted(set(canonical(t) for t in tuples))

def is_valid_type(t):
    """Check that t is a canonical type: values are {0,...,max}, min is 0."""
    if not t:
        return True
    return set(range(max(t) + 1)) == set(t)


def enumerate_types(n):
    """Yield all linear preorders on n positions (ordered Fubini numbers).

    Strategy: enumerate all partitions of {0,...,n-1} into blocks (via
    restricted growth strings), then for each partition with m blocks,
    enumerate all m! orderings of the blocks.  Each yields a type
    (tuple of ranks in {0,...,m-1})."""
    if n == 0:
        yield ()
        return
    from itertools import permutations

    def _rgs(pos, max_val):
        """Generate restricted growth strings (partition encodings)."""
        if pos == n:
            yield ()
            return
        for v in range(max_val + 2):
            for rest in _rgs(pos + 1, max(max_val, v)):
                yield (v,) + rest

    for rgs in _rgs(0, -1):
        m = max(rgs) + 1
        for perm in permutations(range(m)):
            yield tuple(perm[rgs[j]] for j in range(n))


def type_restricts_to(full_type, positions):
    """Extract the sub-type at given positions and canonicalise."""
    sub = tuple(full_type[p] for p in positions)
    return canonical(sub)


def type_consistent_with_orbit(full_type, row_positions, orbit):
    """Check if the type restricted to row_positions matches the orbit."""
    return type_restricts_to(full_type, row_positions) == canonical(orbit)


# ============================================================================
#  Pattern representation
# ============================================================================

def pattern_equalities(template):
    """Given a template (tuple of variable indices), return the set of
    (i, j) pairs with i < j that must have equal values."""
    eqs = set()
    k = len(template)
    for i in range(k):
        for j in range(i + 1, k):
            if template[i] == template[j]:
                eqs.add((i, j))
    return eqs


def pattern_to_equalities(identities, k):
    """Collect all equality constraints from all identities in a pattern.
    Returns: set of (i, j) pairs with i < j on {0,...,k-1}."""
    eqs = set()
    for template, out_pos in identities:
        eqs |= pattern_equalities(template)
    return eqs


# ============================================================================
#  Approach 3: Brute-force type enumeration
# ============================================================================

def check_column_equality(matrix_type, k, r, col, i1, i2):
    """In the k*r matrix with given type, check if entry (i1, col) and
    (i2, col) have the same value.  Matrix is stored row-major:
    position of (row, col) = row * r + col."""
    return matrix_type[i1 * r + col] == matrix_type[i2 * r + col]


def identity_satisfied_at_column(matrix_type, k, r, col, template):
    """Check if an identity's equality constraints are satisfied at column col.
    template is a tuple of length k; positions with equal template values
    must have equal matrix values at that column."""
    for i1 in range(k):
        for i2 in range(i1 + 1, k):
            if template[i1] == template[i2]:
                if matrix_type[i1 * r + col] != matrix_type[i2 * r + col]:
                    return False
    return True


def compute_output_at_column(matrix_type, k, r, col, template, out_pos):
    """If the identity is satisfied at column col, the output value is
    the matrix entry at (out_pos, col)."""
    return matrix_type[out_pos * r + col]


def preserves_temporal_brute(identities, k, R, r):
    """
    Brute-force check: does the pattern (given as identities) preserve
    temporal relation R?

    R is a list of orbit representatives (tuples of ints encoding order-types).

    We enumerate all types on the k*r matrix, filter to those where each
    row belongs to some orbit in R, then check the pattern.

    Returns (True, None) or (False, counterexample_dict).
    """
    n = k * r  # total positions in the matrix
    R_set = set(tuple(canonical(orb)) for orb in R)

    for matrix_type in enumerate_types(n):
        # Check: each row's order-type must be in R
        row_ok = True
        for i in range(k):
            row_positions = [i * r + j for j in range(r)]
            row_type = type_restricts_to(matrix_type, row_positions)
            if row_type not in R_set:
                row_ok = False
                break
        if not row_ok:
            continue

        # For each column, determine if f is defined and what the output is.
        # f is defined at column j if SOME identity's constraints are satisfied.
        # If multiple identities are satisfied, they must agree on the output.
        col_outputs = []
        f_defined_everywhere = True
        conflict = False

        for j in range(r):
            output_val = None
            defined = False
            for template, out_pos in identities:
                if identity_satisfied_at_column(matrix_type, k, r, j, template):
                    val = compute_output_at_column(matrix_type, k, r, j, template, out_pos)
                    if output_val is not None and val != output_val:
                        conflict = True
                        break
                    output_val = val
                    defined = True
            if conflict:
                break
            if not defined:
                f_defined_everywhere = False
                break
            col_outputs.append(output_val)

        if conflict:
            continue  # conflicting pattern at this type — skip
        if not f_defined_everywhere:
            continue

        # Check: result order-type must be in R
        result_type = canonical(tuple(col_outputs))
        if result_type not in R_set:
            return False, {
                'matrix_type': matrix_type,
                'k': k, 'r': r,
                'row_types': [type_restricts_to(matrix_type, [i*r+j for j in range(r)])
                              for i in range(k)],
                'col_outputs': col_outputs,
                'result_type': result_type,
            }

    return True, None


# ============================================================================
#  Approach 2: SAT-based check
# ============================================================================

def preserves_temporal_sat(identities, k, R, r):
    """
    SAT-based check: does the pattern preserve temporal relation R?

    Encodes the NEGATION: exists a k*r matrix of rationals such that each
    row is in R, the pattern is defined on every column, and the result
    is NOT in R.

    Order variables: for each pair of matrix positions (a, b), encode
    their relative order as {<, =, >} using two Booleans:
      lt[a][b] = "value at a < value at b"
      eq[a][b] = "value at a = value at b"
    (gt is implied by ¬lt ∧ ¬eq)

    Returns (True, None) or (False, counterexample_dict).
    """
    n = k * r  # matrix positions
    # Position (row i, col j) -> index i*r + j

    # We also need r result positions (the output tuple).
    # Total positions: n + r = k*r + r
    # Result position j -> index n + j
    total = n + r

    vc = 0
    def nv():
        nonlocal vc; vc += 1; return vc

    # For each ordered pair (a, b) with a < b:
    #   lt[a,b] = "pos a < pos b"
    #   eq[a,b] = "pos a = pos b"
    # For a > b: lt[b,a] means "pos b < pos a" i.e. "pos a > pos b"
    lt = {}
    eq = {}
    for a in range(total):
        for b in range(a + 1, total):
            lt[(a, b)] = nv()
            eq[(a, b)] = nv()

    cl = []

    # ---- Trichotomy: exactly one of <, =, > ----
    # lt[a,b] ∨ eq[a,b] ∨ gt[a,b]   where gt = ¬lt ∧ ¬eq
    # Actually: at least one of {lt, eq, gt} is automatic (gt is the default).
    # We need: at most one of {lt, eq}.  And "gt" means ¬lt ∧ ¬eq.
    # But we also need: ¬(lt ∧ eq).
    for a in range(total):
        for b in range(a + 1, total):
            cl.append([-lt[(a, b)], -eq[(a, b)]])  # not both lt and eq

    # ---- Transitivity ----
    # For all triples (a, b, c):
    #   a < b ∧ b < c → a < c
    #   a < b ∧ b = c → a < c
    #   a = b ∧ b < c → a < c
    #   a = b ∧ b = c → a = c
    # We need helper functions to get the right literal for any pair.

    def get_lt(a, b):
        """Return literal for 'pos a < pos b'."""
        if a == b:
            return None  # never true
        if a < b:
            return lt[(a, b)]
        else:
            # a > b: "a < b" means "b > a" means ¬lt[b,a] ∧ ¬eq[b,a]
            # This isn't a single literal. We need an auxiliary.
            return None  # handle separately

    def get_eq(a, b):
        if a == b:
            return None  # always true
        if a < b:
            return eq[(a, b)]
        else:
            return eq[(b, a)]

    # To handle transitivity properly with our encoding, we introduce
    # for each ordered pair (a,b) the "gt" case explicitly.
    gt = {}
    for a in range(total):
        for b in range(a + 1, total):
            g = nv()
            gt[(a, b)] = g
            # gt[a,b] ↔ ¬lt[a,b] ∧ ¬eq[a,b]
            # gt → ¬lt ∧ ¬eq
            cl.append([-g, -lt[(a, b)]])
            cl.append([-g, -eq[(a, b)]])
            # ¬lt ∧ ¬eq → gt  (equivalently: lt ∨ eq ∨ gt)
            cl.append([lt[(a, b)], eq[(a, b)], g])

    def lit_lt(a, b):
        """Literal for a < b."""
        if a == b: return None
        if a < b: return lt[(a, b)]
        return gt[(b, a)]  # a > b means b < a is false; a < b means gt[b,a]... no
        # If a > b: "a < b" is the same as "b > a" which is gt[(b, a)] since b < a.
        # Wait: gt[(b,a)] means "pos b > pos a" which means "pos a < pos b". Yes!

    def lit_eq(a, b):
        if a == b: return None
        if a < b: return eq[(a, b)]
        return eq[(b, a)]

    def lit_gt(a, b):
        """Literal for a > b."""
        if a == b: return None
        return lit_lt(b, a)

    # Transitivity constraints for all triples of distinct positions
    for a in range(total):
        for b in range(total):
            if b == a: continue
            for c in range(total):
                if c == a or c == b: continue
                # a < b ∧ b < c → a < c
                la = lit_lt(a, b); lb = lit_lt(b, c); lc = lit_lt(a, c)
                if la is not None and lb is not None and lc is not None:
                    cl.append([-la, -lb, lc])
                # a < b ∧ b = c → a < c
                la = lit_lt(a, b); eb = lit_eq(b, c)
                if la is not None and eb is not None and lc is not None:
                    cl.append([-la, -eb, lc])
                # a = b ∧ b < c → a < c
                ea = lit_eq(a, b); lb = lit_lt(b, c)
                if ea is not None and lb is not None and lc is not None:
                    cl.append([-ea, -lb, lc])
                # a = b ∧ b = c → a = c
                ea = lit_eq(a, b); eb = lit_eq(b, c); ec = lit_eq(a, c)
                if ea is not None and eb is not None and ec is not None:
                    cl.append([-ea, -eb, ec])

    # ---- Row constraints: each row's order-type is in R ----
    # For row i, positions are i*r, i*r+1, ..., i*r+r-1.
    # The order-type must match one of the orbits in R.
    R_canonical = [canonical(orb) for orb in R]

    for i in range(k):
        pos = [i * r + j for j in range(r)]
        # Disjunction: one of the orbits must match
        orbit_match_vars = []
        for orb in R_canonical:
            ov = nv()
            orbit_match_vars.append(ov)
            # ov → (order-type of row i matches orb)
            # For each pair (j1, j2) with j1 < j2 in 0..r-1:
            for j1 in range(r):
                for j2 in range(j1 + 1, r):
                    a, b = pos[j1], pos[j2]
                    if orb[j1] < orb[j2]:
                        cl.append([-ov, lit_lt(a, b)])
                    elif orb[j1] == orb[j2]:
                        cl.append([-ov, lit_eq(a, b)])
                    else:  # orb[j1] > orb[j2]
                        cl.append([-ov, lit_gt(a, b)])
        cl.append(orbit_match_vars)  # at least one orbit matches

    # ---- Pattern constraints on columns ----
    # For each column j, for each identity, check if equality constraints
    # are satisfied.  If ANY identity is satisfied, f is defined, and the
    # output is determined.
    #
    # Result position for column j is at index n + j.
    #
    # For identity (template, out_pos):
    #   satisfied at col j iff for all (i1, i2) with template[i1]==template[i2]:
    #     matrix(i1, j) == matrix(i2, j)
    #   output at col j: matrix(out_pos, j)
    #
    # "f defined at col j" = disjunction over identities of "identity satisfied at col j"
    # When satisfied, result[j] = matrix[out_pos, j], i.e. eq(n+j, out_pos*r+j).

    for j in range(r):
        res_pos = n + j

        id_sat_vars = []  # one per identity: "this identity is satisfied at col j"
        for template, out_pos in identities:
            sv = nv()
            id_sat_vars.append((sv, out_pos))

            # sv → all equality constraints of this identity at column j
            eqs = pattern_equalities(template)
            for (i1, i2) in eqs:
                a, b = i1 * r + j, i2 * r + j
                cl.append([-sv, lit_eq(a, b)])

            # sv → result[j] equals matrix[out_pos, j]
            out_matrix_pos = out_pos * r + j
            if res_pos != out_matrix_pos:
                e = lit_eq(res_pos, out_matrix_pos)
                if e is not None:
                    cl.append([-sv, e])

        # f must be defined at every column: at least one identity satisfied
        cl.append([sv for sv, _ in id_sat_vars])

    # ---- Result NOT in R ----
    # For each orbit in R, the result order-type must NOT match it.
    res_positions = [n + j for j in range(r)]
    for orb in R_canonical:
        # NOT (result matches orb)
        # = for some pair (j1, j2), the order relation doesn't match
        block_lits = []
        for j1 in range(r):
            for j2 in range(j1 + 1, r):
                a, b = res_positions[j1], res_positions[j2]
                if orb[j1] < orb[j2]:
                    # Matching requires a < b; blocking: ¬(a < b) = eq or gt
                    block_lits.append(lit_eq(a, b))
                    block_lits.append(lit_gt(a, b))
                elif orb[j1] == orb[j2]:
                    block_lits.append(lit_lt(a, b))
                    block_lits.append(lit_gt(a, b))
                else:
                    block_lits.append(lit_lt(a, b))
                    block_lits.append(lit_eq(a, b))
        cl.append([l for l in block_lits if l is not None])

    # ---- Solve ----
    sol = _solve_sat(cl, vc)
    if sol is None:
        return True, None

    # Extract counterexample by reading pairwise order variables directly
    row_types = []
    for i in range(k):
        positions = [i * r + j for j in range(r)]
        row_types.append(_extract_subset_type(sol, lt, eq, positions))

    result_positions = [n + j for j in range(r)]
    result_type = _extract_subset_type(sol, lt, eq, result_positions)

    return False, {
        'k': k, 'r': r,
        'row_types': row_types,
        'result_type': result_type,
    }


def _extract_subset_type(sol, lt, eq, positions):
    """Extract the order-type of a subset of positions from a SAT solution.

    Reads the pairwise lt/eq variables directly for the given positions
    and returns a canonical type tuple.
    """
    n = len(positions)
    if n == 0:
        return ()

    # Determine pairwise order among positions
    # order[i][j] = -1 (pos_i < pos_j), 0 (equal), +1 (pos_i > pos_j)
    order = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            a, b = positions[i], positions[j]
            # Ensure a < b for dict lookup
            if a < b:
                if sol.get(eq[(a, b)], False):
                    order[i][j] = 0
                    order[j][i] = 0
                elif sol.get(lt[(a, b)], False):
                    order[i][j] = -1
                    order[j][i] = 1
                else:
                    order[i][j] = 1
                    order[j][i] = -1
            else:
                # a > b (shouldn't normally happen since positions are usually sorted, but handle it)
                if sol.get(eq[(b, a)], False):
                    order[i][j] = 0
                    order[j][i] = 0
                elif sol.get(lt[(b, a)], False):
                    order[i][j] = 1   # b < a means a > b means i > j
                    order[j][i] = -1
                else:
                    order[i][j] = -1
                    order[j][i] = 1

    # Group equal positions
    assigned = [False] * n
    groups = []
    for i in range(n):
        if assigned[i]:
            continue
        group = [i]
        assigned[i] = True
        for j in range(i + 1, n):
            if not assigned[j] and order[i][j] == 0:
                group.append(j)
                assigned[j] = True
        groups.append(group)

    # Sort groups: group A < group B if order[a][b] < 0 for a in A, b in B
    # NOTE: must use sorted() not groups.sort() because the key function
    # references `groups`, and list.sort() temporarily empties the list
    # during sorting in CPython, making the key function see an empty list.
    def sort_key(g):
        count = 0
        for g2 in groups:
            if g2 is g:
                continue
            if order[g[0]][g2[0]] < 0:
                count -= 1
        return count

    groups = sorted(groups, key=sort_key)

    # Assign ranks
    result = [0] * n
    for rank, group in enumerate(groups):
        for idx in group:
            result[idx] = rank
    return tuple(result)


# ============================================================================
#  SAT Wrapper (same as in pattern_checker.py)
# ============================================================================

def _solve_sat(clauses, num_vars):
    solver = None
    for SolverClass in _solver_classes():
        try:
            solver = SolverClass(bootstrap_with=clauses)
            break
        except Exception:
            continue
    if solver is None:
        raise RuntimeError("No SAT solver found. pip install python-sat")
    try:
        if not solver.solve():
            return None
        model = solver.get_model()
        result = {}
        for lit in model:
            result[abs(lit)] = (lit > 0)
        for v in range(1, num_vars + 1):
            if v not in result:
                result[v] = False
        return result
    finally:
        solver.delete()


def _solver_classes():
    from pysat.solvers import Solver
    try:
        from pysat.solvers import Cadical153
        yield Cadical153
    except ImportError:
        pass
    try:
        from pysat.solvers import Glucose4
        yield Glucose4
    except ImportError:
        pass
    try:
        from pysat.solvers import Minisat22
        yield Minisat22
    except ImportError:
        pass


# ============================================================================
#  Convenience: describe patterns and identities
# ============================================================================

def describe_identities(identities, k):
    vc = "xyzwuvabcdefghijklmnopqrst"
    parts = []
    for tpl, out in identities:
        args = ",".join(vc[tpl[j] % len(vc)] for j in range(k))
        parts.append(f"f({args})={vc[tpl[out] % len(vc)]}")
    return " ∧ ".join(parts)


# ============================================================================
#  Tests
# ============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("Test: basic type enumeration")
    print("=" * 60)
    for n in range(1, 5):
        types = list(enumerate_types(n))
        print(f"  n={n}: {len(types)} types")
    print()

    # Betweenness relation: Betw = {012, 210}
    # i.e. {(a,b,c) : a < b < c or a > b > c}
    BETW = [(0, 1, 2), (2, 1, 0)]

    # Pattern: f(x, x) = x (idempotent, arity 2)
    # This is a projection, should trivially preserve everything.
    idem = [((0, 0), 0)]
    print("=" * 60)
    print("Test: f(x,x)=x preserves Betw (trivial)")
    print("=" * 60)
    t0 = time.time()
    res_b, cex_b = preserves_temporal_brute(idem, 2, BETW, 3)
    t1 = time.time()
    print(f"  Brute: {res_b} ({t1-t0:.3f}s)")

    # Pattern: f(x,y,x)=y ∧ f(x,x,y)=y  (the minority-like pattern)
    minority_pattern = [((0, 1, 0), 1), ((0, 0, 1), 2)]
    print()
    print("=" * 60)
    print("Test: minority-like pattern preserves Betw?")
    print(f"  Pattern: {describe_identities(minority_pattern, 3)}")
    print("=" * 60)
    t0 = time.time()
    res_b, cex_b = preserves_temporal_brute(minority_pattern, 3, BETW, 3)
    t1 = time.time()
    print(f"  Brute: {res_b} ({t1-t0:.3f}s)")
    if cex_b:
        print(f"    Counterexample: rows={cex_b['row_types']}, result={cex_b['result_type']}")

    # Test SAT approach on the same examples
    print()
    print("=" * 60)
    print("Test: SAT approach")
    print("=" * 60)

    t0 = time.time()
    res_s, cex_s = preserves_temporal_sat(idem, 2, BETW, 3)
    t1 = time.time()
    print(f"  f(x,x)=x preserves Betw: {res_s} ({t1-t0:.3f}s)")

    t0 = time.time()
    res_s2, cex_s2 = preserves_temporal_sat(minority_pattern, 3, BETW, 3)
    t1 = time.time()
    print(f"  minority-like preserves Betw: {res_s2} ({t1-t0:.3f}s)")
    if cex_s2:
        print(f"    Counterexample: rows={cex_s2['row_types']}, result={cex_s2['result_type']}")

    # Cross-validate brute vs SAT on a few patterns
    print()
    print("=" * 60)
    print("Cross-validation: brute vs SAT")
    print("=" * 60)

    # Separation relation: Sep = {0102, 1021, ...} — all interleaving orders
    # Actually let's use simpler relations.
    # Linear order: LO = {01}  (i.e. {(a,b) : a < b})
    LO = [(0, 1)]

    test_patterns = [
        ("f(x,x)=x", [((0, 0), 0)], 2),
        ("f(x,y,x)=y", [((0, 1, 0), 1)], 3),
        ("f(x,x,y)=y ∧ f(x,y,x)=y", [((0, 0, 1), 2), ((0, 1, 0), 1)], 3),
        ("3-cube", [
            ((0,0,0,0,0,1,1,1), 5),  # xxxxxyyy=y
            ((0,0,1,1,1,0,0,1), 2),  # xxyyyxxy=y
            ((0,1,0,0,1,0,1,0), 1),  # xyxxyxyx=y
        ], 8),
    ]

    test_rels = [
        ("Betw", BETW, 3),
        ("LO", LO, 2),
        ("≠", [(0, 1), (1, 0)], 2),
    ]

    all_ok = True
    for pname, pids, pk in test_patterns:
        for rname, rel, rr in test_rels:
            # Brute-force is infeasible for large pattern arity * relation arity
            n_positions = pk * rr
            skip_brute = (n_positions > 9)  # Fubini(9) ~ 7 million

            if not skip_brute:
                t0 = time.time()
                rb, _ = preserves_temporal_brute(pids, pk, rel, rr)
                tb = time.time() - t0
            else:
                rb, tb = None, 0.0

            t0 = time.time()
            rs, _ = preserves_temporal_sat(pids, pk, rel, rr)
            ts = time.time() - t0

            if skip_brute:
                print(f"  {pname} preserves {rname}: sat={rs}({ts:.3f}s) [brute skipped, {n_positions} positions]")
            else:
                match = rb == rs
                tag = "✓" if match else "✗"
                print(f"  {pname} preserves {rname}: brute={rb}({tb:.3f}s) sat={rs}({ts:.3f}s) {tag}")
                if not match:
                    all_ok = False

    print()
    if all_ok:
        print("All tests passed!")
    else:
        print("SOME TESTS FAILED!")
        sys.exit(1)
