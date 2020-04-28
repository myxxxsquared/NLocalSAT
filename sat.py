import argparse
import gzip
import multiprocessing
import os
import pickle
import random
import struct
import sys
import time

import numpy as np
import tensorflow as tf
import tqdm

from network import sat_infer, sat_loss

import datetime

# log_number = open('log_number', 'a')
# print(file=log_number)
# print(datetime.datetime.now(), file=log_number)
# log_number.flush()

class SATModel:
    def __init__(self, config):
        self.config = config

        self._build_network()
        self.global_step = tf.get_variable(
            "global_step",
            initializer=tf.constant_initializer(0, dtype=tf.int32),
            shape=(),
            trainable=False,
        )
        self.increase_global_step = tf.assign_add(self.global_step, 1)

        self.saver = tf.train.Saver(
            tf.trainable_variables() + [self.global_step],
            keep_checkpoint_every_n_hours=0.3,
        )
        if not self.config.is_evaluate:
            self.writer = tf.summary.FileWriter(
                os.path.join(self.config.logdir, "train")
            )
            self.writer_eval = tf.summary.FileWriter(
                os.path.join(self.config.logdir, "eval")
            )
        tfconfig = tf.ConfigProto()
        tfconfig.allow_soft_placement = True
        tfconfig.gpu_options.allow_growth = True
        self.sess = tf.Session(config=tfconfig)
        self.sess.run(tf.global_variables_initializer())
        if not self.config.is_evaluate:
            self.writer.add_graph(self.sess.graph)

        self.train_data = iter(self._fetch_train_data())
        self.eval_data = iter(self._fetch_eval_data())

    def _fetch_train_data(self):
        while True:
            files = os.listdir(self.config.train_data)
            random.shuffle(files)
            for f in files:
                try:
                    finput = gzip.open(os.path.join(self.config.train_data, f))
                    num_vars, num_clauses, labels, edges = pickle.load(finput)
                    if num_clauses > 20000 or edges.shape[0] > 100000:
                        continue
                    # log_number.write(f'train {f} {num_vars} {num_clauses} {edges.shape}\n')
                    # log_number.flush()
                    print(f'Train num_clauses: {num_clauses}, edges: {edges.shape[0]}')
                    yield {
                        self.input_num_vars: num_vars,
                        self.input_num_clauses: num_clauses,
                        self.input_labels: labels,
                        self.input_edges: edges,
                    }
                except Exception as e:
                    print(f"Load ERROR {f}: {e}")

    def _fetch_eval_data(self):
        while True:
            files = os.listdir(self.config.eval_data)
            for f in files:
                try:
                    finput = gzip.open(os.path.join(self.config.eval_data, f))
                    num_vars, num_clauses, labels, edges = pickle.load(finput)
                    print(f'Eval num_clauses: {num_clauses}, edges: {edges.shape[0]}')
                    if num_clauses > 20000 or edges.shape[0] > 100000:
                        continue
                    # log_number.write(f'eval {f} {num_vars} {num_clauses} {edges.shape}\n')
                    # log_number.flush()
                    yield {
                        self.input_num_vars: num_vars,
                        self.input_num_clauses: num_clauses,
                        self.input_labels: labels,
                        self.input_edges: edges,
                    }
                except Exception as e:
                    print(f"Load ERROR {f}: {e}")

    def _build_network(self):
        with tf.name_scope("train_data"):
            num_vars = self.input_num_vars = tf.placeholder(
                tf.int64, shape=[], name="input_num_vars"
            )
            num_clauses = self.input_num_clauses = tf.placeholder(
                tf.int64, shape=[], name="input_num_clauses"
            )
            labels = self.input_labels = tf.placeholder(
                tf.int64, shape=[None], name="input_labels"
            )
            edges = self.input_edges = tf.placeholder(
                tf.int64, shape=[None, 2], name="input_edges"
            )

            edges = tf.SparseTensor(
                indices=edges,
                values=tf.ones(shape=[tf.shape(edges)[0]]),
                dense_shape=[num_clauses, num_vars * 2],
            )
            edges = tf.sparse.reorder(edges)
            sum0 = tf.math.sqrt(tf.sparse.reduce_sum(edges, 0, keepdims=True)) + 1e-6
            sum1 = tf.math.sqrt(tf.sparse.reduce_sum(edges, 1, keepdims=True)) + 1e-6
            edges = edges / sum0 / sum1
        with tf.name_scope("train_infer"):
            self.dropout_rate = tf.get_variable(
                "dropout_rate",
                initializer=tf.constant_initializer(0, dtype=tf.float32),
                shape=(),
                trainable=False,
            )
            self.infer = infer = sat_infer(
                num_vars, num_clauses, edges, self.dropout_rate
            )
            self.softmax_infer = tf.nn.softmax(infer, -1)
        with tf.name_scope("train_loss"):
            self.loss = loss = sat_loss(infer, labels)
        if not self.config.is_evaluate:
            with tf.name_scope("train_optimize"):
                optimizer = tf.train.AdamOptimizer(self.config.learning_rate)
                grads = optimizer.compute_gradients(
                    loss, colocate_gradients_with_ops=True
                )
                grads = [
                    (tf.clip_by_norm(grad, self.config.clip_norm), var)
                    for grad, var in grads
                ]
                self.optimize = optimizer.apply_gradients(grads)
            with tf.name_scope("train_summary"):
                self.summary_ph = tf.placeholder(dtype=tf.float32, shape=[])
                self.summary = tf.summary.scalar("loss", self.summary_ph)
                self.summary_percision = tf.summary.scalar("percision", self.summary_ph)
                histogram_list = []
                for var in tf.trainable_variables():
                    histogram_list.append(tf.summary.histogram(var.name, var))
                self.histogramsum = tf.summary.merge(histogram_list)

    def train(self, steps):
        while steps > 0:
            self.change_dropout(0.1)
            for _ in tqdm.tqdm(list(range(self.config.train_length)), ascii=True):
                _, loss, _, step = self.sess.run(
                    [
                        self.optimize,
                        self.loss,
                        self.increase_global_step,
                        self.global_step,
                    ],
                    feed_dict=next(self.train_data),
                )
                summary = self.sess.run(self.summary, {self.summary_ph: loss})
                self.writer.add_summary(summary, step)
                steps -= 1
                if steps <= 0:
                    break
            histogramsum = self.sess.run(self.histogramsum)
            self.writer.add_summary(histogramsum, step)
            self.saver.save(
                self.sess,
                os.path.join(self.config.logdir, "debug"),
                global_step=self.global_step,
            )
            self.writer.flush()
            self.evaluate(self.config.eval_data_size)

    def evaluate(self, steps):
        self.change_dropout(0)

        totalloss = 0
        correct = 0
        total = 0

        for _ in tqdm.tqdm(list(range(steps)), ascii=True):
            infer, labels, num_nodes, loss = self.sess.run(
                [self.softmax_infer, self.input_labels, self.input_num_vars, self.loss],
                feed_dict=next(self.eval_data),
            )
            totalloss += loss

            infer = np.argmax(infer, -1)
            correct += int(np.sum(infer == labels))
            total += int(num_nodes)

        totalloss /= steps

        if self.config.is_evaluate:
            print(f"percision: {correct / total}")
        else:
            summary = self.sess.run(self.summary, {self.summary_ph: totalloss})
            self.writer_eval.add_summary(summary, self.sess.run(self.global_step))
            summary = self.sess.run(
                self.summary_percision, {self.summary_ph: correct / total}
            )
            self.writer_eval.add_summary(summary, self.sess.run(self.global_step))
            self.writer_eval.flush()

    def load_model(self, file):
        self.saver.restore(self.sess, file)

    def change_dropout(self, val):
        self.sess.run(tf.assign(self.dropout_rate, val))

    def run_predict(self, num_vars, num_clauses, edges):
        self.change_dropout(0)
        infer = self.sess.run(
            self.infer,
            feed_dict={
                self.input_num_vars: num_vars,
                self.input_num_clauses: num_clauses,
                self.input_edges: edges,
            },
        )
        infer = np.argmax(infer, -1).astype(np.int32)
        return infer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--queue_max_size", type=int, default=128)
    parser.add_argument("--num_threads", type=int, default=48)
    parser.add_argument("--logdir", type=str, default="train")
    parser.add_argument("--learning_rate", type=float, default=0.001)
    parser.add_argument("--clip_norm", type=float, default=0.65)
    parser.add_argument("--gpu_list", type=str, default="")

    parser.add_argument("--gen_num_total", type=int, default=5000)
    parser.add_argument("--gen_num_each_min", type=int, default=30)
    parser.add_argument("--gen_num_each_max", type=int, default=50)
    parser.add_argument("--gen_rate_clauses_min", type=float, default=3.5)
    parser.add_argument("--gen_rate_clauses_max", type=float, default=5.5)
    parser.add_argument("--gen_rate_three", type=float, default=1.0)

    parser.add_argument("--train_steps", type=int, default=1000000)

    parser.add_argument("--load_model", type=str)
    parser.add_argument("--is_evaluate", type=bool, default=False)

    parser.add_argument("--save_data_path", type=str, default=None)

    parser.add_argument("--eval_output", type=str, default="evalresult.pkl")

    parser.add_argument("--train_data", type=str, default=None)
    parser.add_argument("--eval_data", type=str, default=None)

    parser.add_argument("--eval_data_size", type=int, default=20)
    parser.add_argument("--train_length", type=int, default=1000)

    config = parser.parse_args()

    os.environ["CUDA_DEVICE_ORDER"] = "PCI_BUS_ID"
    os.environ["CUDA_VISIBLE_DEVICES"] = config.gpu_list

    model = SATModel(config)

    if config.load_model:
        model.load_model(config.load_model)

    if config.is_evaluate:
        model.evaluate(config.eval_data_size)
    else:
        model.train(config.train_steps)


if __name__ == "__main__":
    main()
