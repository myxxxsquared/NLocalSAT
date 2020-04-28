import os
import argparse
import queue
import multiprocessing
import subprocess
import shlex
import time
import signal
import sys
import tqdm
import psutil

sys.path.append(os.getcwd())

# import runsat
import stat_result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-S", "--solver", required=True, type=str)
    parser.add_argument("-I", "--input_folder", required=True, type=str)
    parser.add_argument("-O", "--output_folder", required=True, type=str)
    parser.add_argument("-N", "--num_processes", default=1, type=int)
    parser.add_argument("-T", "--timeout", default=60, type=int)
    parser.add_argument("-W", "--wait_timeout", default=10, type=int)
    parser.add_argument("-P", "--problems", default=None, type=str)
    parser.add_argument("-p", "--predict_folder", default="", type=str)
    parser.add_argument('-s', "--random_seed", default=1997, type=int)
    args = parser.parse_args()

    if args.problems:
        with open(args.problems) as filelist:
            files = [x.strip() for x in filelist.readlines()]
    else:
        files = sorted(
            filter(lambda x: x.endswith(".cnf"), os.listdir(args.input_folder))
        )
    os.makedirs(args.output_folder, exist_ok=True)

    multiprocessing.set_start_method("fork")

    q = multiprocessing.Queue()
    q_back = multiprocessing.Queue()

    def run():
        while True:
            filename = q.get()
            q_back.put(None)
            if filename is None:
                break
            # print(filename, file=sys.stderr)
            inputfilename = os.path.join(args.input_folder, filename)
            outputfilename = os.path.join(args.output_folder, filename)
            predictfilename = os.path.join(args.predict_folder, filename)
            with open(outputfilename, "wb") as outputfile:
                t0 = time.time()

                istimeout = 0
                isexittimeout = 0
                try:
                    cmdline = args.solver.format(problem=inputfilename, predict=predictfilename, filename=filename, seed=args.random_seed)
                    # print(f'+ {cmdline}')
                    subp = subprocess.Popen(
                        shlex.split(cmdline),
                        stdout=outputfile,
                    )
                    subp.communicate(timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    istimeout = 1
                    os.kill(subp.pid, signal.SIGINT)
                    try:
                        subp.communicate(timeout=args.wait_timeout)
                    except subprocess.TimeoutExpired:
                        try:
                            curp = psutil.Process(pid=subp.pid)
                            children = curp.children(recursive=True)
                            for child in children:
                                try:
                                    os.kill(child.pid, signal.SIGKILL)
                                except Exception:
                                    pass
                        except Exception:
                            pass
                        try:
                            os.kill(subp.pid, signal.SIGKILL)
                        except Exception:
                            pass
                        isexittimeout = 1

                outputfile.write(
                    "\nt {} {} {}\n".format(
                        istimeout, isexittimeout, time.time() - t0
                    ).encode("utf-8")
                )

    processes = [multiprocessing.Process(target=run) for _ in range(args.num_processes)]
    for p in processes:
        p.start()
    for f in files:
        q.put(f)
    for _ in processes:
        q.put(None)
    q.close()
    q.join_thread()
    for _ in tqdm.tqdm([None] * len(files), ascii=True):
        q_back.get()
    for p in processes:
        p.join()

    csvfile = args.output_folder.rstrip("/") + ".csv"
    outputfile = open(csvfile, "wt")
    stat_result.stat_result(args.output_folder, outputfile)


if __name__ == "__main__":
    main()
