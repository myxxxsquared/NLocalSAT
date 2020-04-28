import tensorflow as tf


def _sat_linear(input_, nin, nout, scope=None):
    with tf.variable_scope(
        scope, "sat_linear", initializer=tf.truncated_normal_initializer()
    ):
        weight = tf.get_variable("weight", shape=(nin, nout), dtype=tf.float32)
        bias = tf.get_variable(
            "bias", shape=(nout), dtype=tf.float32, initializer=tf.zeros_initializer()
        )
        return tf.nn.bias_add(tf.matmul(input_, weight), bias)


def sat_infer(num_vars, num_clauses, edges, dropout_rate, name=None):

    OUTPUT_ND = 64

    keep_probe = 1 - dropout_rate

    with tf.variable_scope(name, "sat_infer"):
        lits = tf.get_variable(
            "lits", shape=(1, OUTPUT_ND), initializer=tf.random_normal_initializer()
        )
        clauses = tf.get_variable(
            "clauses", shape=(1, OUTPUT_ND), initializer=tf.random_normal_initializer()
        )

        num_vars_32 = tf.cast(num_vars, tf.int32)
        num_clauses_32 = tf.cast(num_clauses, tf.int32)

        lits = tf.tile(lits, tf.convert_to_tensor([num_vars_32 * 2, 1]))
        clauses = tf.tile(clauses, tf.convert_to_tensor([num_clauses_32, 1]))

        lits = tf.contrib.rnn.LSTMStateTuple(
            h=lits,
            c=tf.zeros(
                tf.convert_to_tensor([num_vars_32 * 2, OUTPUT_ND], dtype=tf.int32)
            ),
        )
        clauses = tf.contrib.rnn.LSTMStateTuple(
            h=clauses,
            c=tf.zeros(
                tf.convert_to_tensor([num_clauses_32, OUTPUT_ND], dtype=tf.int32)
            ),
        )

        for i in range(16):
            with tf.variable_scope(
                tf.get_variable_scope(), reuse=tf.AUTO_REUSE  # if i == 0 else True
            ):
                with tf.variable_scope("layers"): #"layer_%d" % (i,)):
                    lits_msg = tf.nn.relu(
                        _sat_linear(lits.h, OUTPUT_ND, OUTPUT_ND, "lits_msg_1")
                    )
                    lits_msg = tf.nn.dropout(lits_msg, keep_probe)
                    lits_msg = _sat_linear(lits_msg, OUTPUT_ND, OUTPUT_ND, "lits_msg_2")
                    lits_msg = tf.sparse_tensor_dense_matmul(edges, lits_msg)
                    _, clauses = tf.contrib.rnn.LayerNormBasicLSTMCell(OUTPUT_ND)(
                        inputs=lits_msg, state=clauses, scope="clauses_layer"
                    )
                    clauses_msg = tf.nn.relu(
                        _sat_linear(clauses.h, OUTPUT_ND, OUTPUT_ND, "clauses_msg_1")
                    )
                    clauses_msg = tf.nn.dropout(clauses_msg, keep_probe)
                    clauses_msg = _sat_linear(
                        clauses_msg, OUTPUT_ND, OUTPUT_ND, "clauses_msg_2"
                    )
                    clauses_msg = tf.sparse_tensor_dense_matmul(
                        edges, clauses_msg, adjoint_a=True
                    )

                    flipinfo = tf.concat(
                        [
                            lits.h[num_vars_32 : num_vars_32 * 2],
                            lits.h[0:num_vars_32, :],
                        ],
                        axis=0,
                    )
                    allinfo = tf.concat([clauses_msg, flipinfo], axis=1)

                    _, lits = tf.contrib.rnn.LayerNormBasicLSTMCell(OUTPUT_ND)(
                        inputs=allinfo, state=lits, scope="lits_layer"
                    )

        varoutput = tf.concat(
            [lits.h[0:num_vars_32, :], lits.h[num_vars_32 : num_vars_32 * 2]], axis=1
        )

        varoutput = tf.nn.relu(
            _sat_linear(varoutput, OUTPUT_ND * 2, 512, "output_linear_1")
        )
        varoutput = tf.nn.dropout(varoutput, keep_probe)
        varoutput = _sat_linear(varoutput, 512, 2, "output_linear_5")

        return varoutput


def sat_loss(infer, output_labels, name=None):
    with tf.variable_scope(name, "sat_loss"):
        output_labels = tf.one_hot(output_labels, 2)
        return tf.losses.softmax_cross_entropy(
            onehot_labels=output_labels, logits=infer
        )
