#!/usr/bin/env python3.8

import time
import sys
import os
import argparse
import random
import copy
import signal
import json
import pprint
import itertools
import functools
import subprocess
#import tempfile
#import shutil
from mpi4py import MPI
from functools import reduce
from threading import Timer
from itertools import combinations, product
print = functools.partial(print, flush=True)
from statistics import mean, median, variance, pvariance




#Parser
def createParser ():
  parser = argparse.ArgumentParser()
  parser.add_argument('-cn', '--cnfname', nargs='?', default = './cnfs/cnf_BvP_3_3_fraag-ktmiter.cnf')
  parser.add_argument('-mn', '--metaname', nargs='?', default = './meta/meta_BvP_3_3_fraag-ktmiter.json')
  parser.add_argument('-bs', '--bucketsize', nargs='?', type = str, default = 5)
  parser.add_argument('-tlim', '--tasklimit', nargs='?', type = int, default = 10000)
  parser.add_argument('-s', '--solver', nargs='?', type = str, default = 'kissat201', help = 'SAT Solvers: cadical, glucose3, glucose41, kissat201, kissatSC2020, MapleLCMDistChrBt-DL-v3, minisat, rokk')
  return parser

def enum(*sequential, **named):
  enums = dict(zip(sequential, range(len(sequential))), **named)
  return type('Enum', (), enums)

def getCNF(from_file):
  dimacs = open(from_file).readlines()
  clauses = []
  header = None
  inputs = None
  vars_first = None
  outputs_first = None
  vars_second = None
  outputs_second = None
  miter_vars = None
  mut_gate = None
  mut_var = None
  for i in range(len(dimacs)):
    if dimacs[i][0] == 'p':
      header = dimacs[i][:-1] if dimacs[i][-1] == '\n' else dimacs[i]
    elif dimacs[i][0] == 'c':
      if 'inputs' in dimacs[i]:
        inputs = list(map(int, dimacs[i].split(':')[1].split()))
      elif 'variables for gates in first scheme' in dimacs[i]:
        vars_first = [x for x in range(int(dimacs[i].split()[-3]), int(dimacs[i].split()[-1])+1)]
      elif 'outputs first scheme' in dimacs[i]:
        outputs_first = list(map(int, dimacs[i].split(':')[1].split()))
      elif 'variables for gates in second scheme' in dimacs[i]:
        vars_second = [x for x in range(int(dimacs[i].split()[-3]), int(dimacs[i].split()[-1])+1)]
      elif 'outputs second scheme' in dimacs[i]:
        outputs_second = list(map(int, dimacs[i].split(':')[1].split()))
      elif 'miter variables' in dimacs[i]:
        miter_vars = list(map(int, dimacs[i].split(':')[1].split()))
    elif dimacs[i][-1] == '\n':
      clauses.append(list(map(int,dimacs[i].split()[:-1])))
  return header, inputs, vars_first, outputs_first, vars_second, outputs_second, miter_vars, clauses

def make_pairs(*lists):
  for t in combinations(lists, 2):
      for pair in product(*t):
          yield pair

def make_lenghts_input_chunks(lenghdecompose):
  if ';' in lenghdecompose:
    len_inp_chunks = lenghdecompose.split(';')
    for i in range(len(len_inp_chunks)):
      if '+' in len_inp_chunks[i]:
        len_inp_chunks[i] = list(map(int,len_inp_chunks[i].split('+')))
      else:
        len_inp_chunks[i] = [int(len_inp_chunks[i])]
  elif '+' in lenghdecompose:
    len_inp_chunks = list(map(int,lenghdecompose.split('+')))
  else:
    len_inp_chunks = int(lenghdecompose)
  return len_inp_chunks


# !FIXME надо переписать с другой логикой, ведь 
def make_inputs_decompositions(inputs, len_inp_chunks):
  nof_layers = 1
  if type(len_inp_chunks) == int:
    #one layer, no combination
    input_decompose = list(chunks(inputs, len_inp_chunks))
    input_decompose[-1] = inputs[-len_inp_chunks:]
  elif type(len_inp_chunks) == list:
    input_decompose = []
    if all(isinstance(n, int) for n in len_inp_chunks) == True:
      #one layer, combination of chunk's len
      for chunk_len in len_inp_chunks:
        input_decompose_ = list(chunks(inputs, chunk_len))
        input_decompose_[-1] = inputs[-chunk_len:]
        input_decompose.append(input_decompose_)
    elif all(isinstance(n, list) for n in len_inp_chunks) == True:
      nof_layers = len(len_inp_chunks)
      for layer_len_inp_chunks in len_inp_chunks:
        layer_inp_dec = []
        for chunk_len in layer_len_inp_chunks:
          input_decompose_ = list(chunks(inputs, chunk_len))
          input_decompose_[-1] = inputs[-chunk_len:]
          layer_inp_dec.append(input_decompose_)
        input_decompose.append(layer_inp_dec)
    else:
      raise 'Multiple chunks: len_inp_chunks should be all ints or all lists'
  else:
    raise 'Single chunks: len_inp_chunks should be int or list'
  return input_decompose, nof_layers

def make_inputs_decomposition(inputs, len_inp_chunks):
  nof_layers = 1
  if type(len_inp_chunks) == int:
    #one layer, no combination
    input_decompose = list(chunks(inputs, len_inp_chunks))
    input_decompose[-1] = inputs[-len_inp_chunks:]
  else:
    raise 'Single chunks: len_inp_chunks should be int or list'
  return input_decompose

def chunks(lst, n):
  for i in range(0, len(lst), n):
    yield lst[i:i + n]


# !FIXME тут остановился
def make_binary_vectors(nof_layers,len_inp_chunks, nof_inputs, inputs):
  binary_vectors = []
  total_tasks = 1
  if nof_layers == 1:
    if len(len_inp_chunks) == 1:
      #one layer, no combination
      binary_vectors = list(itertools.product([0, 1], repeat=len_inp_chunks))
      total_tasks = len(binary_vectors)
    else:
      # one layer, combination
      for chunk_len in len_inp_chunks:
        binary_vector_ = list(itertools.product([0, 1], repeat=chunk_len))
        binary_vectors.append(binary_vector_)
        total_tasks *= len(binary_vector_)
  else:
    layer = 0
    dec = inputs
    while layer < nof_layers:
      dec_ = []
      for len_dec in layer:
        dec_ += list(chunks(dec, len_dec))
      dec = dec_
      layer += 1
    binary_vectors = list(itertools.product([0, 1], repeat=len(dec)))
  return binary_vectors





def create_and_solve_CNF(clauses, new_clauses, max_var, solver):
  cnf_str = create_str_CNF(clauses, new_clauses, max_var)
  result = solve_CNF(cnf_str, solver)
  answer = 'INDET'
  time = None
  conflicts = None
  for line in result:
    if len(line) > 0 and line[0] == 's':
      if 'UNSAT' in line:
        answer = 'UNSAT'
      elif 'SAT' in line:
        answer = 'SAT'
    elif ('c process-time' in line and solver == 'kissat201') or ('c total process time' in line and solver == 'cadical'):
      time = float(line.split()[-2])
    elif ('c conflicts:' in line and solver == 'kissat201') or ('c conflicts:' in line and solver == 'cadical'):
      conflicts = int(line.split()[-4])
  return answer, time, conflicts


def create_str_CNF(clauses, new_clauses, max_var):
  lines = []
  header_ = 'p cnf ' + str(max_var) + ' ' + str(len(clauses)+len(new_clauses))
  lines.append(header_)
  lines.extend([' '.join(list(map(str,clause))) + ' 0' for clause in clauses])
  lines.extend([' '.join(list(map(str,clause))) + ' 0' for clause in new_clauses])
  cnf = '\n'.join(lines)
  #pprint.pprint(cnf)
  return cnf


def solve_CNF(cnf, solver):
  solver = subprocess.run(["/home/vkondratev/data/Solvers/Binaries/" + solver], capture_output=True, text=True, input = cnf)
  result = solver.stdout.split('\n')
  errors = solver.stderr
  if len(errors) > 0:
    print(errors)
  return result


def solve_vector(binaryvector, buckets, clauses, max_var, solver):
  if len(binaryvector) == len(buckets):
    new_clauses = []
    current_var = max_var
    for bit, var in zip(binaryvector, buckets):
      if bit == 1:
        new_clauses.append([var])
      elif bit == 0:
        new_clauses.append([-var])
    answer, time, conflicts = create_and_solve_CNF(clauses, new_clauses, current_var, solver)
    return time, conflicts
  else:
    raise 'len(binaryvector) != len(buckets)'

######################################################################################################
##-----------------------------------------------MAIN-----------------------------------------------##
######################################################################################################


if __name__ == "__main__":
  # Define MPI message tags
  tags = enum('READY', 'START', 'DONE', 'EXIT')
  comm = MPI.COMM_WORLD
  rank = comm.Get_rank()
  size = comm.size
  status = MPI.Status()
  if rank == 0:
    start_time = MPI.Wtime()
    parser = createParser()
    namespace = parser.parse_args (sys.argv[1:])
    filename = namespace.cnfname
    cnf_name = ''.join(filename.split('/')[-1].split('.')[:-1])
    tasklimit = namespace.tasklimit
    metaname = namespace.metaname
    solver = namespace.solver
    if '+' in namespace.bucketsize:
      bucketsize_right = int(namespace.bucketsize.split('+')[-1])
      bucketsize_left = int(namespace.bucketsize.split('+')[0])
    else:
      bucketsize_right = bucketsize_left = int(namespace.bucketsize)
    solvers_list = ['cadical', 'glucose3', 'glucose41', 'kissat201', 'kissatSC2020', 'MapleLCMDistChrBt-DL-v3', 'minisat', 'rokk']
    if solver not in solvers_list:
      raise 'Unknown SAT solver'

    # Считываем LEC КНФ из файла
    header, inputs, vars_first, outputs_first, vars_second, outputs_second, miter_vars, clauses = getCNF(from_file = filename)
    max_var = int(header.split()[2])
    miter_and_clause = clauses[-1]
    max_var_no_miter = min(miter_and_clause) - 1
    miter_len = len(miter_and_clause)
    miter_xor_clauses = clauses[len(clauses)-1-4*miter_len:-1]
    cnf_no_miter = clauses[:len(clauses)-1-4*miter_len]
    str_cnf_no_miter = [' '.join(list(map(str,clause))) + ' 0' for clause in cnf_no_miter]


    # Читаем файл метаданных
    metadata = json.load(open(metaname,'r'))
    inputs = metadata['inputs']
    outputs_first = metadata['outputsLeft']
    outputs_second = metadata['outputsRight']
    miter_vars = metadata['xors']
    metadata_gates = metadata['gates']
    list_vars_right = [[x['variable'],x['p']] for x in metadata_gates if x['schema'] == 'right']
    list_vars_right.sort(key = lambda x: abs(0.5 - x[1]))
    list_vars_left = [[x['variable'],x['p']] for x in metadata_gates if x['schema'] == 'left']
    list_vars_left.sort(key = lambda x: abs(0.5 - x[1]))

    # Создаем бинарные вектора, по которым будет определяться функция для чанков входов
    binary_vectors = list(itertools.product([0, 1], repeat=bucketsize_left+bucketsize_right))

    buckets = [list_vars_right[i][0] for i in range(bucketsize_right)] + [list_vars_left[i][0] for i in range(bucketsize_left)]

    total_tasks = len(binary_vectors)
  else:
    solver = None
    buckets = None
    max_var = None
    clauses = None

  solver = comm.bcast(solver, root=0)
  buckets = comm.bcast(buckets, root=0)
  clauses = comm.bcast(clauses, root=0)
  max_var = comm.bcast(max_var, root=0) 


  if rank == 0:
      # Master process executes code below
      task_index = 0
      num_workers = size - 1
      closed_workers = 0
      results_table = []
      full_solve_flag = False
      if tasklimit > total_tasks:
        tasklimit = total_tasks
        full_solve_flag = True
      with open('tmp_log_balanced_cubes_'+str(namespace.bucketsize)+'_'+cnf_name+'_'+str(tasklimit)+'_'+solver, 'w') as f:
        print("Master starting with %d workers and %d tasks" % (num_workers, tasklimit), file = f)
        while closed_workers < num_workers:
            data = comm.recv(source=MPI.ANY_SOURCE, tag=MPI.ANY_TAG, status=status)
            source = status.Get_source()
            tag = status.Get_tag()
            if tag == tags.READY:
                # Worker is ready, so send it a task
                if task_index < tasklimit:
                    print("", file = f)
                    if full_solve_flag == True:
                      task = binary_vectors[task_index]
                    else:
                      task = random.choice(binary_vectors)
                    comm.send(task, dest=source, tag=tags.START)
                    print("Sending task %d to worker %d (current runtime % 6.2f)" % (task_index, source, (MPI.Wtime() - start_time)), file = f)
                    task_index += 1
                else:
                    comm.send(None, dest=source, tag=tags.EXIT)
            elif tag == tags.DONE:
                print("", file = f)
                print("Got data from worker %d (current runtime % 6.2f)" % (source,(MPI.Wtime() - start_time)), file = f)
                print(data, file = f)
                results_table.append(data)
            elif tag == tags.EXIT:
                print("Worker %d exited." % source, file = f)
                closed_workers += 1
        print("Master finishing", file = f)
        print('Total runtime:', MPI.Wtime() - start_time, 'on', size, 'cores', file = f)
        print('', file = f)
        res_time_ = [x[1] for x in results_table]
        avg_solvetime = round(sum(res_time_)/len(results_table), 2)
        res_conflicts_ = [x[2] for x in results_table]
        avg_conflicts = round(sum(res_conflicts_)/len(results_table), 2)
        if full_solve_flag == True:
          print('All possible tasks solved.', file = f)
        print('CNF name:', cnf_name, file = f)
        print('Bucket size:', namespace.bucketsize, file = f)
        print('Solver:', solver, file = f)
        print('Solved', len(results_table), 'tasks.', file = f)
        print('Total tasks:', total_tasks, file = f)
        print('Average solvetime:',avg_solvetime, file = f)
        print("Median time:", round(median(res_time_),2), file = f)
        print('Min solvetime:',round(min(res_time_),2), file = f)
        print('Max solvetime:',round(max(res_time_),2), file = f)
        print("Variance of time:", round(variance(res_time_),2), file=f)
        print('Estimate time for solving all tasks is ', avg_solvetime*total_tasks, sep = '', file = f)
        print('Average number of conflicts:',avg_conflicts, file = f)
        print("Median number of conflicts:", round(median(res_conflicts_),2), file = f)
        print('Min number of conflicts:',min(res_conflicts_), file = f)
        print('Max number of conflicts:',max(res_conflicts_), file = f)
        print("Variance of number of conflicts:", round(variance(res_conflicts_),2), file=f)
        print('Estimate number of conflicts for solving all tasks is ', avg_conflicts*total_tasks, sep = '', file = f)
        print('(Estimate number of conflicts / Brutforce actions) ratio:', round((avg_conflicts*total_tasks)/pow(2,len(inputs)),4), file = f)
  else:
      # Worker processes execute code below
      name = MPI.Get_processor_name()
      #print("I am a worker with rank %d on %s." % (rank, name))
      while True:
          comm.send(None, dest=0, tag=tags.READY)
          task = comm.recv(source=0, tag=MPI.ANY_TAG, status=status)
          tag = status.Get_tag()
          if tag == tags.START:
              # Do the work here
              starttime = MPI.Wtime()
              results = []
              time, conflicts = solve_vector(task, buckets, clauses, max_var, solver)
              comm.send(tuple([task, time, conflicts]), dest=0, tag=tags.DONE)
          elif tag == tags.EXIT:
              break
      comm.send(None, dest=0, tag=tags.EXIT)

