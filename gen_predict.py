import argparse
import os
import time

import tqdm

import sat_predict
import satutils


def main(input_folder, output_folder, load_model, gpu_list, logfile, input_file=None):
    satutils.init_boost_numpy()
    predict = sat_predict.SATPredict(gpu_list, load_model)

    if not input_file:
        problems = os.listdir(input_folder)
        problems = sorted(problems)
    else:
        problems = [input_file]

    os.makedirs(output_folder, exist_ok=True)

    if logfile:
        logfile = open(logfile, "a")

    for problem in tqdm.tqdm(problems, ascii=True):
        t0 = time.time()
        p = satutils.Problem()
        p.load(os.path.join(input_folder, problem))
        num_vars, num_clauses, edges = p.to_data()
        # if num_vars > 1000000 or edges.shape[0] > 10000000:
        #     print("no", problem, num_vars, num_clauses, edges.shape[0], file=logfile)
        #     continue
        if logfile:
            print(problem, num_vars, num_clauses, edges.shape[0], file=logfile)
            logfile.flush()
        labels = predict.model.run_predict(num_vars, num_clauses, edges)
        with open(os.path.join(output_folder, problem), "w") as foutput:
            deltat = time.time() - t0
            foutput.write(f"{num_vars} {num_clauses} {deltat}\n\n")
            for l in labels:
                foutput.write(f"{l}\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--input_folder", required=True, type=str)
    parser.add_argument("-o", "--output_folder", default=None, type=str)
    parser.add_argument("-l", "--load_model", required=True, type=str)
    parser.add_argument("-g", "--gpu_list", type=str, default=" ")
    parser.add_argument("--logfile", type=str, default=None)
    parser.add_argument("--input_file", type=str, default=None)

    args = parser.parse_args()

    output_folder = args.output_folder or args.input_folder.rstrip("/") + "-predict"
    main(
        args.input_folder,
        output_folder,
        args.load_model,
        args.gpu_list,
        args.logfile,
        args.input_file,
    )
