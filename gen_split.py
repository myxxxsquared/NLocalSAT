import csv
import multiprocessing.pool
import os
import sys
import traceback
import argparse
import random

import numpy as np
import tqdm

import satutils


def process_file(args):
    satutils.split_cnf(*args)


def main(
    input_folders,
    no_traversal,
    output_folder,
    each_len,
    min_len,
    log_file=None,
    nprocess=16,
    solution_path=None
):
    if isinstance(log_file, str):
        log_file = open(log_file, "w", newline='')
        log_file = csv.writer(log_file)

    if log_file:
        log_file.writerow(('src', 'dst'))

    input_files = []

    if no_traversal:
        for input_folder in input_folders:
            for fname in os.listdir(input_folder):
                if fname.endswith(".cnf"):
                    input_files.append(os.path.join(input_folder, fname))
    else:
        for input_folder in input_folders:
            for dirpath, _, filenames in os.walk(input_folder):
                for fname in filenames:
                    if fname.endswith(".cnf"):
                        input_files.append(os.path.join(dirpath, fname))

    runargs = []
    for i, file in enumerate(input_files):
        output_fileprefix = os.path.join(output_folder, f"{i:04d}")
        runargs.append(
            (file, output_fileprefix, each_len, random.randint(0, 2147483647), min_len, True)
        )
        if log_file:
            log_file.writerow((file, output_fileprefix))

    os.makedirs(output_folder, exist_ok=True)

    pool = multiprocessing.pool.ThreadPool(nprocess)
    for _ in tqdm.tqdm(
        pool.imap_unordered(process_file, runargs), ascii=True, total=len(runargs)
    ):
        pass


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input_folders", nargs="+", required=True, type=str)
    parser.add_argument("--no_traversal", action="store_true")
    parser.add_argument("-o", "--output_folder", required=True, type=str)
    parser.add_argument("-e", "--each_len", type=int, default=50000)
    parser.add_argument("-m", "--min_len", type=float, default=1.0)
    parser.add_argument("-l", "--log_file", type=str, default=None)
    parser.add_argument("-N", "--nprocess", type=int, default=16)
    parser.add_argument("-s", "--solution_folder", type=str, default=None)
    args = parser.parse_args()

    input_folders = args.input_folders
    no_traversal = args.no_traversal
    output_folder = args.output_folder
    each_len = args.each_len
    min_len = args.min_len
    log_file = args.log_file
    nprocess = args.nprocess
    solution_folder = args.solution_folder

    main(input_folders, no_traversal, output_folder, each_len, min_len, log_file, nprocess, solution_folder)
