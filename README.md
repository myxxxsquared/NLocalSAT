
# NLocalSAT; Boosting Local Search with Solution Prediction

Published in IJCAI-2020, [https://arxiv.org/abs/2001.09398](https://arxiv.org/abs/2001.09398)

The boolean satisfiability problem is a famous NP-complete problem in computer science. An effective way for this problem is the stochastic local search (SLS). However, in this method, the initialization is assigned in a random manner, which impacts the effectiveness of SLS solvers. To address this problem, we propose NLocalSAT. NLocalSAT combines SLS with a solution prediction model, which boosts SLS by changing initialization assignments with a neural network. We evaluated NLocalSAT on five SLS solvers (CCAnr, Sparrow, CPSparrow, YalSAT, and probSAT) with problems in the random track of SAT Competition 2018. The experimental results show that solvers with NLocalSAT achieve 27%~62% improvement over the original SLS solvers.

Please see `scripts/expenvs` and `scripts/04_train.sh` to run the code.
