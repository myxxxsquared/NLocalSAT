import argparse
import gzip
import os
import pickle
import queue
import threading
import traceback
from multiprocessing.pool import ThreadPool

import tqdm

import satutils

satutils.init_boost_numpy()


def load_work(args):
    filename, solutionname = args
    if not os.path.exists(solutionname):
        return None

    try:
        p = satutils.Problem()
        p.load(filename)
        p.load_solution(solutionname)
        return p
    except Exception as ex:
        if not isinstance(ex, RuntimeError) or str(ex) != "no solution":
            print(f"load failed: {filename}")
            traceback.print_exc()


def filter_same(prob_iter):
    before_len = set()
    for p in prob_iter:
        if not p:
            continue
        pair = p.get_num_vars(), p.get_num_clauses()
        if pair not in before_len:
            before_len.add(pair)
            yield p


def split_work_maker(split_size):
    def split_work(problem):
        return problem.split(split_size)

    return split_work


def split_chain(prob_iter):
    for p in prob_iter:
        for p_gen in p:
            if p_gen.get_num_clauses() >= p_gen.get_num_vars() * 2:
                yield p_gen


def gen_worker(problem_queue, indexing_queue, output_folder, split_size):
    batch_gen = satutils.BatchGenerator()
    while True:
        p = problem_queue.get()
        if p is None:
            break
        if p.get_num_vars() >= split_size:
            batch_gen_full = satutils.BatchGenerator()
            batch_gen_full.append(p, 0)
            data = batch_gen_full.save()
            print("Size", data[0])
            dataid = indexing_queue()
            pickle.dump(
                data, gzip.open(os.path.join(output_folder, f"{dataid:08d}.gz"), "wb")
            )
            continue
        batch_gen.append(p, 0)
        if batch_gen.n_vars() > split_size:
            data = batch_gen.save()
            dataid = indexing_queue()
            pickle.dump(
                data, gzip.open(os.path.join(output_folder, f"{dataid:08d}.gz"), "wb")
            )
            print("Size", data[0])
            batch_gen = satutils.BatchGenerator()


class counter:
    def __init__(self):
        self.val = 0
        self.lock = threading.Lock()

    def __call__(self):
        try:
            self.lock.acquire()
            print(self.val)
            self.val += 1
            return self.val
        finally:
            self.lock.release()


def main(input_folder, solution_folder, output_folder, nthread=8, split_size=2000):
    loaded_len = set()

    os.makedirs(output_folder, exist_ok=True)

    p = ThreadPool(nthread)
    p2 = ThreadPool(nthread)

    files = [
        [os.path.join(input_folder, f), os.path.join(solution_folder, f)]
        for f in os.listdir(input_folder)
        if f.endswith(".cnf")
    ]
    prob_iter = p.imap_unordered(load_work, files)
    prob_iter = filter_same(prob_iter)
    prob_iter = p2.imap_unordered(split_work_maker(split_size), prob_iter)
    prob_iter = split_chain(prob_iter)

    prob_queue = queue.Queue(1)
    c = counter()

    threads = [
        threading.Thread(
            target=gen_worker, args=(prob_queue, c, output_folder, split_size)
        )
        for i in range(3)
    ]
    for t in threads:
        t.start()

    for p in prob_iter:
        prob_queue.put(p)

    for t in threads:
        prob_queue.put(None)
    for t in threads:
        t.join()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input_folder", required=True, type=str)
    parser.add_argument("-s", "--solution_folder", type=str, default=None)
    parser.add_argument("-o", "--output_folder", type=str, default=None)
    parser.add_argument("-n", "--num_threads", type=int, default=3)
    parser.add_argument("-S", "--size", type=int, default=2000)
    args = parser.parse_args()

    input_folder = args.input_folder.rstrip("/")
    solution_folder = args.solution_folder or input_folder + "-solution"
    output_folder = args.output_folder or input_folder + "-data"
    num_threads = args.num_threads
    size = args.size

    main(input_folder, solution_folder, output_folder, num_threads, size)
