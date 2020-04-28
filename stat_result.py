import argparse
import itertools
import os
import re
import sys

predictre = re.compile("p (\\d )+")
resultre = re.compile("v (-?\\d+ )*-?\\d+")
timere = re.compile("t [01] [01] ([\\d\\.]+)")
sameratere = re.compile("s ([\\d\\.]+)")
stpesre = re.compile("c solveSteps = (-?\\d+) tries \\+ (-?\\d+) steps.*")
varsre = re.compile("c Instance: Number of variables = (\\d+)")
clausesre = re.compile("c Instance: Number of clauses = (\\d+)")
solvetimere = re.compile("c solveTime = ([\\d.]+)")


def stat_result(stat_dir, outputfile):
    def processfile(filename):
        predicted = []
        result = []
        t = 0
        samerate = 0
        steps = 0
        tries = 0
        numvars = 0
        clauses = 0
        tsolving = 0

        with open(filename, "rt") as cnffile:
            for line in cnffile:
                line = line.strip()

                if predictre.match(line):
                    predicted = [int(x) for x in line.split(" ")[1:]]
                    continue

                if resultre.match(line):
                    line = [int(x) for x in line.split(" ")[1:]]
                    line = [x > 0 for x in line if x != 0]
                    result.extend(line)
                    continue

                match = timere.match(line)
                if match:
                    t = float(match[1])
                    continue

                match = sameratere.match(line)
                if match:
                    samerate = float(match[1])
                    continue

                match = stpesre.match(line)
                if match:
                    tries = int(match[1])
                    steps += int(match[2])
                    continue

                match = varsre.match(line)
                if match:
                    numvars = int(match[1])
                    continue

                match = clausesre.match(line)
                if match:
                    clauses = int(match[1])
                    continue

                match = solvetimere.match(line)
                if match:
                    tsolving = float(match[1])

                if line == "o":
                    steps += 2 ** 63

        if result and predicted:
            zeroall = sum((x == 0 for x in predicted))
            zerocorr = sum((x == 0 and not y for x, y in zip(predicted, result)))

            if not len(result) == len(predicted):
                print(len(result), len(predicted), file=sys.stderr)
                corr = 0
                sumcount = 1
                truecount = 0
            else:
                corr = sum(
                    map(lambda x: int((x[0] == 1) == x[1]), zip(predicted, result))
                )
                sumcount = len(result)
                truecount = sum(map(int, result))
        else:
            corr = 0
            sumcount = 1
            truecount = 0
            zerocorr = 0
            zeroall = 1

        if zeroall == 0:
            zeroall = 1

        if predicted:
            numvars = numvars or len(predicted)

        print(
            os.path.split(filename)[1],
            numvars,
            clauses,
            bool(result),
            tries,
            steps,
            corr / sumcount,
            truecount / sumcount,
            samerate,
            t,
            zerocorr / zeroall,
            tsolving,
            sep=",",
            file=outputfile,
        )

    files = map(
        lambda x: os.path.join(stat_dir, x),
        filter(lambda x: x.endswith(".cnf"), os.listdir(stat_dir)),
    )

    print(
        "file, vars, clauses, solved, tries, steps, corr, true, samerate, time, zerocorr, solving",
        file=outputfile,
    )
    list(map(processfile, files))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("folder")
    parser.add_argument("--output", default=None)
    args = parser.parse_args()
    folder = args.folder.rstrip('/')
    foutput = args.output or folder + ".csv"

    foutput = open(foutput, "wt")
    stat_result(folder, foutput)
