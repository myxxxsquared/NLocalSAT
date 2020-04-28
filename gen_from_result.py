import argparse
import gzip
import multiprocessing
import os
import pickle
import random
import sys
import traceback

import numpy as np
import tqdm

from satfuncs import read_cnf_file, read_solution

import itertools


def process_file(parameters):
    input_folder, solution_folder, output_folder, fname = parameters
    try:
        num_vars, num_clauses, clauses = read_cnf_file(
            open(os.path.join(input_folder, fname))
        )
        solution = read_solution(open(os.path.join(solution_folder, fname)))
        if solution:
            assert num_vars == len(solution)
            return num_vars, num_clauses, clauses, solution
        else:
            print(f"NOSOLUTION: {fname}", file=sys.stderr)
            return None
    except Exception:
        print(f"FAILD: {fname}", file=sys.stderr)
        traceback.print_exc()


def add_val(l0, val):
    return l0 + val if l0 > 0 else l0 - val


class SATOutput:
    def __init__(self, output_folder, max_size=10000, max_max_size=20000, clause_max_size=100000, max_clause_size=200000, counter=itertools.count()):
        self.num_vars = 0
        self.clauses = []
        self.solutions = []

        self.max_size = max_size
        self.max_max_size = max_max_size

        self.curid = counter
        self.output_folder = output_folder

    def save(self):
        if self.num_vars == 0:
            return

        num_vars = self.num_vars
        num_clauses = len(self.clauses)
        num_edges = sum(map(len, self.clauses))
        edges = np.empty(shape=(num_edges, 2), dtype=np.int32)
        curindex = 0
        for i, cluase in enumerate(self.clauses):
            for lit in cluase:
                edges[curindex] = (i, lit - 1 if lit > 0 else -lit - 1 + num_vars)
                curindex += 1
        solutions = np.array(self.solutions, dtype=np.int64)

        currentid = next(self.curid)
        outputname = os.path.join(self.output_folder, f"{currentid:08d}.gz")
        output_file = gzip.open(outputname, "w")
        pickle.dump((num_vars, num_clauses, solutions, edges), output_file)

        self.num_vars = 0
        self.clauses = []
        self.solutions = []

    def process(self, cnf):
        num_vars, num_clauses, clauses, solution = cnf
        if (
            num_vars + self.num_vars >= self.max_max_size
            or self.num_vars >= self.max_size
        ):
            self.save()
        self.clauses.extend(
            ([add_val(lit, self.num_vars) for lit in clause] for clause in clauses)
        )
        self.solutions.extend(solution)
        self.num_vars += num_vars


def main(input_folder, solution_folder, output_folder, min_size, max_size):
    os.makedirs(output_folder, exist_ok=True)
    os.makedirs(solution_folder, exist_ok=True)

    files = os.listdir(input_folder)
    file_solution = set(os.listdir(solution_folder))
    files = [
        (input_folder, solution_folder, output_folder, fname)
        for fname in files
        if fname in file_solution
    ]
    random.shuffle(files)
    counter = itertools.count()
    output = SATOutput(output_folder, min_size, max_size, counter)
    output2 = SATOutput(output_folder, min_size, max_size, counter)
    for file in tqdm.tqdm(files, ascii=True):
        file = process_file(file)
        if file:
            num_vars, num_clauses, clauses, solution = file
            if num_vars >= min_size:
                output2.process(file)
                output2.save()
            else:
                output.process(file)
    output.save()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input_folder", required=True)
    parser.add_argument("-s", "--solution_folder", required=False, default=None)
    parser.add_argument("-o", "--output_folder", required=False, default=None)
    parser.add_argument("--min_size", type=int, default=10000)
    parser.add_argument("--max_size", type=int, default=20000)
    args = parser.parse_args()

    input_folder = args.input_folder.rstrip("/")
    solution_folder = args.solution_folder or input_folder + "-solution"
    output_folder = args.output_folder or input_folder + "-data"
    min_size = args.min_size
    max_size = args.max_size

    main(input_folder, solution_folder, output_folder, min_size, max_size)
