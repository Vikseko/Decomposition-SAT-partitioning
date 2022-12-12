# InputDecomposition

A parallel script that uses MPI to build estimates of the decompositional hardness of boolean formulas.



Usage:
mpirun -n [number of cores] python3 path/to/LEC_input_decompose_mpi.py -n path/to/cnf.cnf -ld [chunk_size_for_decomposition] -s path/to/solver -lim [sample_size]
