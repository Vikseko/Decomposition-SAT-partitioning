# Parallel Scripts for building estimates of boolean formulas hardness w.r.t. SAT partitioning.


Script for Input decomposition:

mpirun -n [number of cores] python3 path/to/LEC_input_decompose_mpi.py -n path/to/cnf.cnf -ld [decomposition_type] -s path/to/solver -lim [sample_size]

Script for Decomposition on Balanced Cubes:

mpirun -n [number of cores] python3 path/to/LEC_balanced_cubes_checker.py -n path/to/cnf.cnf -mn path/to/json/with/balance/information -bs [decomposition_type] -s path/to/solver -tlim [sample_size]
