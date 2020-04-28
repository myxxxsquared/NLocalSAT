import os
import pickle
import sys
import time

import tensorflow as tf

import sat

if not hasattr(sys, "argv"):
    sys.argv = [""]


class predict_config:
    is_evaluate = True


class SATPredict:
    def __init__(self, gpu_list, load_model):
        t0 = time.time()
        # os.environ["CUDA_DEVICE_ORDER"] = "PCI_BUS_ID"
        os.environ["CUDA_VISIBLE_DEVICES"] = gpu_list
        self.model = sat.SATModel(predict_config)
        self.model.load_model(load_model)
        deltat = time.time() - t0
        print(f"inittime: {deltat}", file=sys.stderr)

    def __call__(self, num_vars, num_clauses, edges, argmax=True):
        return self.model.run_predict(num_vars, num_clauses, edges)
