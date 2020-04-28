import argparse
import gzip
import multiprocessing
import os
import pickle
import random
import time

from solution_space_generator import generate_data

q = multiprocessing.Queue(10000)


def generate_random_int():
    return random.randint(0, 2147483647)


def gendata_process(seed, args):
    while True:
        if q.empty():
            break
        i = q.get()
        if i is None:
            break
        filename = f"{i:08x}.gz"
        fullname = os.path.join(args.save_path, filename)
        try:
            gen = generate_data(
                i,
                args.num_total,
                args.num_each_min,
                args.num_each_max,
                args.rate_clauses_min,
                args.rate_clauses_max,
                args.rate_three,
                verbose=True,
            )
            foutput = gzip.open(fullname, "wb")
            pickle.dump(gen, foutput)
            foutput.close()
            print(filename)
        except:
            try:
                os.remove(fullname)
            except:
                pass
            raise


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("save_path", type=str)
    parser.add_argument("-N", "--nprocess", type=int, default=10)
    parser.add_argument("--num_total", type=int, default=10000)
    parser.add_argument("--num_each_min", type=int, default=10)
    parser.add_argument("--num_each_max", type=int, default=30)
    parser.add_argument("--rate_clauses_min", type=float, default=2.0)
    parser.add_argument("--rate_clauses_max", type=float, default=6.0)
    parser.add_argument("--rate_three", type=float, default=0.8)
    parser.add_argument("--larger_than", type=int, default=0)
    parser.add_argument("--no_random", action="store_true")
    args = parser.parse_args()

    os.makedirs(args.save_path, exist_ok=True)
    random.seed()

    processes = []

    for _ in range(args.nprocess):
        p = multiprocessing.Process(
            target=gendata_process, args=(generate_random_int(), args)
        )
        p.start()
        processes.append(p)

    if args.no_random:
        for i in range(args.num_total):
            q.put(i, True)
        for _ in range(args.nprocess):
            q.put(None, True)
    else:
        for _ in range(args.num_total):
            i = generate_random_int()
            while i < args.larger_than:
                i = generate_random_int()
            q.put(i, True)
        for _ in range(args.nprocess):
            q.put(None, True)

    for p in processes:
        p.join()


if __name__ == "__main__":
    main()
