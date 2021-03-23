#!/usr/bin/env python3

import argparse
from functools import wraps
import os
from pysat.solvers import Solver
from pyswip import Prolog
import textwrap
from time import time

#######################
#######################
#
# utilities

def timing(f):
    global timings
    @wraps(f)
    def wrap(*args, **kw):
        ts = time()
        result = f(*args, **kw)
        te = time()
        timings.append(f'# {f.__name__}:'.ljust(15) + f' {te-ts:2.4f}s')
        return result
    return wrap


def show_timings():
    print('\n' + '\n'.join(timings) + '\n')

#######################
#######################
#
# piccalc

piccalc_src_dir = os.path.dirname(os.path.realpath(__file__))
piccalc_prolog = os.path.join(piccalc_src_dir, 'piccalc.pl')
piccalc_dir = os.path.dirname(piccalc_src_dir)
piccalc_domains_dir = os.path.join(piccalc_dir, 'domains/')

Prolog.assertz('piccalc_python')
Prolog.consult(piccalc_prolog)

timings = None

statens = None
transns = None
state_bitstr_atom_map = None
trans_bitstr_atom_map = None
state_nbits = None
trans_nbits = None
n_statebits = None
n_transbits = None

solver = None

#######################
#######################
#
# Prolog utilities

def call(Query):
    # this just runs a query without returning the answers
    next(Prolog.query(Query))

def call_answers(Query):
    # run a query and return the generator for the answers
    return Prolog.query(Query)

def call_one_answer(Query):
    # return the first answer to a query
    return next(Prolog.query(Query))

#######################
#######################
#
# iccalc interface: initial load

def loadf(file):
    call(f'loadf({file})')
    get_theory_info()


def get_theory_info():

    global statens
    global transns
    global state_bitstr_atom_map
    global trans_bitstr_atom_map
    global state_nbits
    global trans_nbits
    global n_statebits
    global n_transbits

    state_bitstr_atom_map = dict()
    trans_bitstr_atom_map = dict()
    state_nbits = dict()
    trans_nbits = dict()

    statens,n_statebits = get_type_info('state', state_bitstr_atom_map, state_nbits)
    transns,n_transbits = get_type_info('trans', trans_bitstr_atom_map, trans_nbits)


def get_type_info(type, bitstr_atom_map, nbits):
    n_bits = 0
    ns = call_one_answer(f'iccalc_var({type}_integers, N)')['N']
    if type == 'state':
        offset = 1
    else:
        if not ns == []:
            offset = ns[0]
        else:
            offset = 0
    for J in ns:
        atom_info = call_one_answer(f'atom_info({J}, C, NBits, NDom)')
        C = atom_info['C']
        NBits = atom_info['NBits']
        NDom = atom_info['NDom']
        nbits[J-offset] = NBits
        n_bits += NBits

        bitstr_atom_map[J-offset] = dict()
        for i in range(1, NDom+1):
            V = call_one_answer(f'nth_domain({C},{i},V)')['V']
            bitstr = int_to_bitstr(i, NDom, NBits)       
            if V == 'tt':
                Atom = f'{C}'
            elif not V == 'ff':
                Atom = f'{C}={V}'
            else:
                Atom = ''
            bitstr_atom_map[J-offset][bitstr] = Atom
    ns = [n-offset for n in ns]
    return ns,n_bits


def int_to_bitstr(i, NDom, NBits):
    if i == NDom and is_power_of_two(NDom):
        return '0' * NBits
    else:
        l = bin(i)[2:][::-1]
        return l.ljust(NBits, '0')


def is_power_of_two(n):
    return (n & (n-1) == 0) and n != 0

#######################
#######################
#
# iccalc interface: queries

def q(QueryLabel='trans', SolverName='minisat-gh'):
    
    global solver
    global timings

    Timespec = call_one_answer(f'get_query_time_range({QueryLabel},Tmin,Tmax)')
    Tmin = Timespec['Tmin']
    Tmax = Timespec['Tmax']
    
    num_models = 0
    for T in range(Tmin,Tmax+1):
        print(f'# looking for solutions with runs of length {T}...')
        timings = []
        solver = Solver(name=SolverName)
        add_cnf(QueryLabel, T)
        num_models = solve_print(T)
        solver.delete()
        if num_models != 0:
            show_timings()
            break


@timing
def add_cnf(QueryLabel, T):
    for soln in call_answers(f'cnf_clause({QueryLabel}, {T}, Clause)'):
        solver.add_clause(soln['Clause'])


@timing
def solve_print(T):
    i = 0
    for i, model in enumerate(solver.enum_models(), 1):
        print(f'\n###### SOLUTION {i}:\n')
        bitstr = ''.join('0' if lit < 0 else '1' for lit in model)
        print_model(0, T, bitstr)
    return i


def print_model(Tcurrent, T, bitstr):
    if Tcurrent <= T:
        if Tcurrent > 0:
            # show an action
            print('A:  ' +
                  '\n    '.join(filter(None,
                                (trans_bitstr_atom_map[J][bitstr[J:J+trans_nbits[J]]]
                                 for J in transns))))
            bitstr = bitstr[n_transbits:]
        # show a state
        print(f'{Tcurrent}:  ' +
              '\n    '.join(filter(None,
                            (state_bitstr_atom_map[J][bitstr[J:J+state_nbits[J]]]
                             for J in statens))))
        bitstr = bitstr[n_statebits:]
        # move to next time-step
        print_model(Tcurrent+1, T, bitstr)

#######################
#######################
#
# iccalc interface: transition systems

@timing
def transition_system(SolverName='minisat-gh'):

    global solver
    global timings

    timings = []

    dotfilename = os.path.join(piccalc_domains_dir, 'piccalc.dot')
    with open(dotfilename, 'w') as dotfile:
        write_dot_preamble(dotfile)
        # record the states
        solver = Solver(name=SolverName)
        add_cnf('states', 0)
        states = dict()
        make_states(states, dotfile)
        solver.delete()
        # record the transitions
        solver = Solver(name=SolverName)
        add_cnf('trans', 1)
        make_trans(states, dotfile)
        solver.delete()
    dotfile.close()
    show_timings()


@timing
def make_states(states, dotfile):
    for i, model in enumerate(solver.enum_models(), 1):
        bitstr = ''.join('0' if lit < 0 else '1' for lit in model)
        state = '\\n'.join(filter(None,
                                  (state_bitstr_atom_map[J][bitstr[J:J+state_nbits[J]]]
                                   for J in statens)))
        states[state] = i
        dotfile.write(f' {i} [label="{state}"];\n')
    dotfile.write('\n')


@timing
def make_trans(states, dotfile):
    for i, model in enumerate(solver.enum_models(), 1):
        bitstr = ''.join('0' if lit < 0 else '1' for lit in model)
        s0 = '\\n'.join(filter(None,
                               (state_bitstr_atom_map[J][bitstr[J:J+state_nbits[J]]]
                                for J in statens)))
        bitstr = bitstr[n_statebits:]
        s0_n = states[s0]
        event = '\\n'.join(filter(None,
                                  (trans_bitstr_atom_map[J][bitstr[J:J+trans_nbits[J]]]
                                   for J in transns)))
        bitstr = bitstr[n_transbits:]
        s1 = '\\n'.join(filter(None,
                               (state_bitstr_atom_map[J][bitstr[J:J+state_nbits[J]]]
                                for J in statens)))
        s1_n = states[s1]
        dotfile.write(f' {s0_n} -> {s1_n} [label="{event}"];\n')
    dotfile.write('}\n')


def write_dot_preamble(dotfile):
    preamble = textwrap.dedent("""\
        digraph trans_system {

         /* settings for output to A4 paper, using dot */
         margin=0.4;
         orientation=portrait;
         rankdir=TB;
         ranksep=2;
         searchsize=50;
         size="7.47,10.89";\n\n""")      
    dotfile.write(preamble)

#######################
#######################
#
# command-line mode

def command_line_args():
    parser = argparse.ArgumentParser('ICCalc')
    parser.add_argument('file',
                        help='C+ action description file')
    parser.add_argument('-pq', '--prolog_query',
                        help='prolog query to run')
    parser.add_argument('-q', '--query',
                        help='query to answer')
    parser.add_argument('-ql', '--query_label',
                        default='trans',
                        help='query label from input file to answer')
    parser.add_argument('-s', '--solver',
                        default='minisat-gh',
                        help='SAT solver to use')
    parser.add_argument('-t', '--transition_system',
                        action='store_true',
                        help='write transition system to file')
    return parser.parse_args()


def main():
    args = command_line_args()
    loadf(args.file)
    if args.transition_system:
        transition_system(SolverName=args.solver)
    else:
        q(QueryLabel=args.query_label, SolverName=args.solver)


if __name__ == '__main__':
    main()