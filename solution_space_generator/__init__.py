try:
    from ._satgenerator import _generate_data  # pylint: disable=E0611
except ImportError as err:
    import sys

    print(
        "ImportError: cannot import extension library, try to rebuild the library using make.sh",
        file=sys.stderr,
    )
    raise


def generate_data(
    run_id,
    num_total=1000,
    num_each_min=10,
    num_each_max=20,
    rate_clauses_min=2.0,
    rate_clauses_max=8.0,
    rate_three=0.8,
    verbose=False,
):
    """Generate SAT Data

    Arguments:
        run_id {int} -- random seed
        num_total {int} -- total sat nodes
        num_each_min {int} -- nodes in each problem
        num_each_max {int} -- nodes in each problem
        rate_clauses_min {float} -- clauses over nodes
        rate_clauses_max {float} -- clauses over nodes
        rate_three {float} -- the probality of three nodes

    Returns:
        ( num_vars, num_clauses, labels, weights, edges )
    """

    return _generate_data(
        num_total,
        num_each_min,
        num_each_max,
        rate_clauses_min,
        rate_clauses_max,
        rate_three,
        run_id,
        verbose,
    )
