__all__ = [
    "lit_var",
    "lit_sign",
    "lit_pair",
    "pair_lit",
    "read_cnf_file",
    "read_solution",
]


def lit_var(l):
    assert l != 0
    return l - 1 if l > 0 else -l - 1


def lit_sign(l):
    assert l != 0
    return l > 0


def lit_pair(l):
    assert l != 0
    return (l - 1, True) if l > 0 else (-l - 1, False)


def pair_lit(p):
    return p[0] + 1 if p[1] else -p[0] - 1


def read_cnf_file(f):
    num_vars, num_clauses = -1, -1
    clauses = []

    for line in f:
        line = line.strip()
        if not line:
            continue
        if line.startswith("c"):
            continue
        if line.startswith("p cnf"):
            assert num_vars == -1
            assert num_clauses == -1
            line = line.split()
            num_vars = int(line[2])
            num_clauses = int(line[3])
            assert num_vars >= 0
            assert num_clauses >= 0
            continue
        line = line.split()
        new_clause = list(map(int, line))
        assert new_clause[-1] == 0
        new_clause = new_clause[:-1]
        for lit in new_clause:
            assert lit_var(lit) < num_vars
        clauses.append(new_clause)

    assert len(clauses) == num_clauses

    return num_vars, num_clauses, clauses


def read_solution(f):
    results = []
    for line in f:
        line = line.strip()
        if not line:
            continue
        if line[0] == "v":
            line = line.split()
            assert line[0] == "v"
            line = map(int, line[1:])
            for val in line:
                if val == 0:
                    break
                results.append(val > 0)
                assert abs(val) == len(results)
    return results or None
