import argparse
import itertools
import multiprocessing
import os
import shutil
import signal
import subprocess
import sys
import time

import tqdm


def run_process(args):
    fname, problem_folder, solution_folder, tmp_folder, solver_base, solvers, timeout = (
        args
    )

    problem_file = os.path.join(problem_folder, fname)
    output_file = os.path.join(solution_folder, fname)

    if os.path.exists(output_file):
        return

    processes = []
    files = []

    for solver in solvers:
        tmp_proof = os.path.join(tmp_folder, fname, solver)
        os.makedirs(tmp_proof, exist_ok=True)
        tmp_solution = os.path.join(tmp_folder, fname, solver, "cnf.out")
        tmp_solution = open(tmp_solution, "w")
        files.append(tmp_solution)
        solver_path = os.path.join(solver_base, solver, "bin", "starexec_run_default")
        solver_cwd = os.path.join(solver_base, solver, "bin")
        process = subprocess.Popen(
            [solver_path, problem_file, tmp_proof],
            cwd=solver_cwd,
            stdout=tmp_solution,
            stderr=tmp_solution,
        )
        process._myname = solver
        processes.append(process)

    starttime = time.time() + timeout
    should_run = True
    finish_name = None

    while should_run:
        for process in processes:
            try:
                process.communicate(timeout=1)
                finish_name = process._myname
                should_run = False
            except subprocess.TimeoutExpired:
                pass
        if time.time() > starttime:
            should_run = False

    for process in processes:
        process.send_signal(signal.SIGTERM)
        process.wait()

    for f in files:
        f.close()

    # print(fname, finish_name)
    if finish_name:
        tmp_solution = os.path.join(tmp_folder, fname, finish_name, "cnf.out")
        shutil.copy(tmp_solution, output_file)


def main(problem_folder, solution_folder, tmp_folder, solver_base, solvers, timeout, nprocess):
    os.makedirs(problem_folder, exist_ok=True)
    os.makedirs(solution_folder, exist_ok=True)
    os.makedirs(tmp_folder, exist_ok=True)

    problems = [fname for fname in os.listdir(problem_folder) if fname.endswith(".cnf")]
    problems = sorted(problems)

    problems = [
        (
            fname,
            problem_folder,
            solution_folder,
            tmp_folder,
            solver_base,
            solvers,
            timeout,
        )
        for fname in problems
    ]

    pool = multiprocessing.Pool(nprocess)
    for _ in tqdm.tqdm(pool.imap_unordered(run_process, problems), total=len(problems), ascii=True):
        pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input_folder", required=True, type=str)
    parser.add_argument("-o", "--output_folder", default=None, type=str)
    parser.add_argument("-m", "--tmp_folder", default=None, type=str)
    parser.add_argument("-b", "--solver_base", required=True, type=str)
    parser.add_argument("-s", "--solver_names", required=True, type=str, nargs="+")
    parser.add_argument("-t", "--timeout", type=int, default=600)
    parser.add_argument("-N", '--nprocess', type=int, default=10)
    args = parser.parse_args()
    problem_folder = args.input_folder.rstrip("/")
    solution_folder = args.output_folder or problem_folder + "-solution"
    tmp_folder = args.tmp_folder or problem_folder + "-tmp"
    solver_base = args.solver_base
    solvers = list(args.solver_names)
    timeout = args.timeout
    nprocess = args.nprocess

    main(problem_folder, solution_folder, tmp_folder, solver_base, solvers, timeout, nprocess)
