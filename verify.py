
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

def read_cnf_file(f, s):
    num_vars, num_clauses = -1, -1
    clauses = 0

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
        c = set(new_clause).intersection(s)
        clauses += 1
        if len(c) == 0:
            assert False

    assert clauses == num_clauses

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
                results.append(val)
                assert abs(val) == len(results)
    return results or None


import os
import tqdm

problem_folder = "/home/zwj/data/satrandomdata/eval"
output_folder = "/home/zwj/satsource_random/run_seed/yalsat_p_1"

COUTN = 0

t = tqdm.tqdm(os.listdir(output_folder))

for f in t:
    t.desc = f
    s = read_solution(open(os.path.join(output_folder, f)))
    if s is None:
        continue
    s = set(s)
    _, _, p = read_cnf_file(open(os.path.join(problem_folder, f)), s)

    COUTN += 1


print(COUTN)