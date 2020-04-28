import argparse
import csv
import itertools
import multiprocessing.pool
import os
import random
import shutil

import tqdm


def run_command(params):
    cmdline, fname = params
    result = os.system(cmdline)
    if result != 0:
        print(f"Failed to process. Code:{result} File:{fname}")


def main(
    input_folders,
    output_folder,
    copy,
    num_process,
    precent_eval=0.2,
    no_traversal=False,
    log_file=None,
    suffix=".cnf",
    train_folder_name="train",
    eval_folder_name="eval"
):
    input_files = []

    s = set()

    if no_traversal:
        for input_folder in input_folders:
            for fname in os.listdir(input_folder):
                if suffix and fname.endswith(suffix):
                    if fname in s:
                        print(f'dup: {fname}')
                        continue
                    s.add(fname)
                    input_files.append(os.path.join(input_folder, fname))
    else:
        for input_folder in input_folders:
            for dirpath, _, filenames in os.walk(input_folder):
                for fname in filenames:
                    if suffix and fname.endswith(suffix):
                        if fname in s:
                            print(f'dup: {fname}')
                            continue
                        s.add(fname)
                        input_files.append(os.path.join(dirpath, fname))

    os.makedirs(os.path.join(output_folder, train_folder_name), exist_ok=True)
    os.makedirs(os.path.join(output_folder, eval_folder_name), exist_ok=True)

    if isinstance(log_file, str):
        log_file = open(log_file, "w", newline="")
    if log_file:
        csv_writer = csv.writer(log_file)
        csv_writer.writerow(("type", "dst", "src"))

    random.shuffle(input_files)

    
    total_num = len(input_files)

    if precent_eval != 0:
        eval_num = int(precent_eval * total_num)
        train_num = total_num - eval_num

        eval_files = input_files[:eval_num]
        train_files = input_files[eval_num:]

        tasks = []

        for i, fin in enumerate(train_files):
            fname = f"{i:04d}{suffix}"
            tasks.append(
                (
                    fin,
                    os.path.join(output_folder, train_folder_name, fname),
                    os.path.join(train_folder_name, fname),
                )
            )
            if log_file:
                csv_writer.writerow((train_folder_name, fname, fin))

        for i, fin in enumerate(eval_files):
            fname = f"{i:04d}{suffix}"
            tasks.append(
                (
                    fin,
                    os.path.join(output_folder,  eval_folder_name, fname),
                    os.path.join(eval_folder_name, fname),
                )
            )
            if log_file:
                csv_writer.writerow(("eval", fname, fin))

        taskslen = len(tasks)
        tasks = ((f"'{copy}' '{fin}' '{fout}'", fname) for fin, fout, fname in tasks)

    else:
        tasks = []
        for i, fin in enumerate(input_files):
            fname = f"{i:04d}{suffix}"
            tasks.append(
                (
                    fin,
                    os.path.join(output_folder, fname),
                    os.path.join(fname),
                )
            )
            if log_file:
                csv_writer.writerow(("train", fname, fin))
        taskslen = len(tasks)
        tasks = ((f"'{copy}' '{fin}' '{fout}'", fname) for fin, fout, fname in tasks)


    pool = multiprocessing.pool.ThreadPool(num_process)
    for _ in tqdm.tqdm(
        pool.imap_unordered(run_command, tasks), ascii=True, total=total_num
    ):
        pass


def restricted_float(x):
    x = float(x)
    if x < 0.0 or x > 1.0:
        raise argparse.ArgumentTypeError("%r not in range [0.0, 1.0]" % (x,))
    return x


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input_folders", nargs="+", required=True, type=str)
    parser.add_argument("--no_traversal", action="store_true")
    parser.add_argument("-o", "--output_folder", required=True, type=str)
    parser.add_argument("-T", "--train_folder_name", type=str, default="train")
    parser.add_argument("-E", "--eval_folder_name", type=str, default="eval")
    parser.add_argument("-l", "--log_file", type=str, default=None)
    parser.add_argument("-p", "--percent_eval", type=restricted_float, default=0.2)
    parser.add_argument("-e", "--copy", type=str, default="cp")
    parser.add_argument("-N", "--num_process", default=4, type=int)
    parser.add_argument("-s", "--suffix", default=".cnf", type=str)
    args = parser.parse_args()

    main(
        args.input_folders,
        args.output_folder,
        args.copy,
        args.num_process,
        args.percent_eval,
        args.no_traversal,
        args.log_file,
        args.suffix,
        args.train_folder_name,
        args.eval_folder_name
    )
