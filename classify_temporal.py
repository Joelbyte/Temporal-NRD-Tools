"""
Classify all 2^13 = 8192 ternary temporal relations into the hierarchy:

  1. Preserved by Maltsev
  2. Preserved by 3-NU but NOT by Maltsev
  3. Preserved by 3-EDGE but NOT by 3-NU
  4. Preserved by 3-CUBE but NOT by 3-EDGE
  5. NOT preserved by 3-CUBE

For each level, prints the count and lists the relations.

Requires: temporal_checker.py in the same directory.

Usage:
    python classify_hierarchy.py
"""

from temporal_checker import (
    preserves_temporal_sat, canonical, enumerate_types, describe_identities,
)
import time


# ============================================================================
#  Orbits and display
# ============================================================================

ALL_TERNARY_ORBITS = sorted(enumerate_types(3))
N_ORBITS = len(ALL_TERNARY_ORBITS)
assert N_ORBITS == 13


def orbit_to_str(orb):
    return "".join(chr(ord('a') + v) for v in orb)


def orbit_description(orb):
    names = ['x₁', 'x₂', 'x₃']
    n_distinct = len(set(orb))
    if n_distinct == 1:
        return "x₁=x₂=x₃"
    elif n_distinct == 2:
        if orb[0] == orb[1]:
            return f"x₁=x₂{'<' if orb[0]<orb[2] else '>'}x₃"
        elif orb[0] == orb[2]:
            return f"x₁=x₃{'<' if orb[0]<orb[1] else '>'}x₂"
        else:
            return f"x₂=x₃{'<' if orb[1]<orb[0] else '>'}x₁"
    else:
        order = sorted(range(3), key=lambda i: orb[i])
        return "<".join(names[i] for i in order)


def relation_to_str(R):
    if not R:
        return "∅"
    return "{" + ", ".join(orbit_to_str(orb) for orb in R) + "}"


# ============================================================================
#  Pattern definitions
# ============================================================================

# Maltsev: xxy=y, yxx=y
MALTSEV = [
    ((0, 0, 1), 2),  # xxy=y
    ((0, 1, 1), 0),  # yxx=y
]

# 3-NU: xxy=x, xyx=x, yxx=x
THREE_NU = [
    ((0, 0, 1), 0),  # xxy=x
    ((0, 1, 0), 0),  # xyx=x
    ((0, 1, 1), 1),  # yxx=x
]

# 3-EDGE: xxyy=y, xyxy=y, yyyx=y
THREE_EDGE = [
    ((0, 0, 1, 1), 2),  # xxyy=y
    ((0, 1, 0, 1), 1),  # xyxy=y
    ((0, 0, 0, 1), 0),  # yyyx=y
]

# 3-CUBE: xxxxyyy=y, xxyyxxy=y, xyxyxyx=y
THREE_CUBE = [
    ((0, 0, 0, 0, 1, 1, 1), 4),  # xxxxyyy=y
    ((0, 0, 1, 1, 0, 0, 1), 2),  # xxyyxxy=y
    ((0, 1, 0, 1, 0, 1, 0), 1),  # xyxyxyx=y
]


# ============================================================================
#  Classification
# ============================================================================

def classify_hierarchy(verbose=True):
    """
    Classify all ternary temporal relations into the 5-level hierarchy.

    Returns
    -------
    levels : dict mapping level (1..5) to list of relations (each a list of orbits)
    """
    total = 2 ** N_ORBITS

    # Pattern arities
    arity_maltsev = len(MALTSEV[0][0])
    arity_3nu = len(THREE_NU[0][0])
    arity_3edge = len(THREE_EDGE[0][0])
    arity_3cube = len(THREE_CUBE[0][0])

    levels = {1: [], 2: [], 3: [], 4: [], 5: []}

    t_start = time.time()

    for mask in range(total):
        R = [ALL_TERNARY_ORBITS[i] for i in range(N_ORBITS) if mask & (1 << i)]

        if len(R) == 0:
            # Empty relation is preserved by everything
            levels[1].append(R)
            continue

        # Test from strongest to weakest; stop at the first that preserves R
        pres_maltsev, _ = preserves_temporal_sat(MALTSEV, arity_maltsev, R, 3)
        if pres_maltsev:
            levels[1].append(R)
            continue

        pres_3nu, _ = preserves_temporal_sat(THREE_NU, arity_3nu, R, 3)
        if pres_3nu:
            levels[2].append(R)
            continue

        pres_3edge, _ = preserves_temporal_sat(THREE_EDGE, arity_3edge, R, 3)
        if pres_3edge:
            levels[3].append(R)
            continue

        pres_3cube, _ = preserves_temporal_sat(THREE_CUBE, arity_3cube, R, 3)
        if pres_3cube:
            levels[4].append(R)
            continue

        levels[5].append(R)

        if verbose and (mask + 1) % 500 == 0:
            elapsed = time.time() - t_start
            print(f"  ... checked {mask+1}/{total} ({elapsed:.1f}s)", flush=True)

    elapsed = time.time() - t_start

    if verbose:
        print(f"  Classification complete in {elapsed:.2f}s")

    return levels, elapsed


def print_hierarchy(levels, elapsed):
    """Pretty-print the classification results."""
    total = sum(len(v) for v in levels.values())

    level_names = {
        1: "Preserved by Maltsev",
        2: "Preserved by 3-NU but NOT by Maltsev",
        3: "Preserved by 3-EDGE but NOT by 3-NU",
        4: "Preserved by 3-CUBE but NOT by 3-EDGE",
        5: "NOT preserved by 3-CUBE",
    }

    print("=" * 70)
    print("Ternary temporal relation hierarchy classification")
    print(f"  Total relations: {total}")
    print(f"  Time: {elapsed:.2f}s")
    print("=" * 70)
    print()

    # Summary
    print("Summary:")
    for lvl in range(1, 6):
        print(f"  Level {lvl}: {len(levels[lvl]):5d}  ({level_names[lvl]})")
    print()

    # Details for each level
    for lvl in range(1, 6):
        print("-" * 70)
        print(f"Level {lvl}: {level_names[lvl]}  ({len(levels[lvl])} relations)")
        print("-" * 70)

        rels = sorted(levels[lvl], key=lambda R: (len(R), R))
        for R in rels:
            if not R:
                print(f"  ∅")
            else:
                orbits_str = relation_to_str(R)
                descs = ", ".join(orbit_description(o) for o in R)
                print(f"  {orbits_str:50s}  ({descs})")

        print()


# ============================================================================
#  Main
# ============================================================================

if __name__ == "__main__":
    print("Classifying all 8192 ternary temporal relations...")
    print()
    levels, elapsed = classify_hierarchy(verbose=True)
    print_hierarchy(levels, elapsed)
