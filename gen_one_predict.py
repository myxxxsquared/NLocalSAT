import argparse
import os
import time

import tqdm

import sat_predict
import satutils


def main(input_file, output_file, load_model, gpu_list, logfile):
    satutils.init_boost_numpy()
    predict = sat_predict.SATPredict(gpu_list, load_model)

    if logfile:
        logfile = open(logfile, "a")

    t0 = time.time()
    p = satutils.Problem()
    p.load(input_file)
    num_vars, num_clauses, edges = p.to_data()
    if logfile:
        print(input_file, num_vars, num_clauses, edges.shape[0], file=logfile)
        logfile.flush()
    labels = predict.model.run_predict(num_vars, num_clauses, edges)
    with open(output_file, "w") as foutput:
        deltat = time.time() - t0
        foutput.write(f"{num_vars} {num_clauses} {deltat}\n\n")
        for l in labels:
            foutput.write(f"{l}\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input_file", required=True, type=str)
    parser.add_argument("-o", "--output_file", required=True, type=str)
    parser.add_argument("-l", "--load_model", required=True, type=str)
    parser.add_argument("-g", "--gpu_list", type=str, default=" ")
    parser.add_argument("--logfile", type=str, default=None)

    args = parser.parse_args()

    main(
        args.input_file, args.output_file, args.load_model, args.gpu_list, args.logfile
    )
