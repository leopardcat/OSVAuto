"""Run a single theory."""

import argparse
from pstats import Stats
import cProfile

from osverify import os_parser

# Parse arguments
parser = argparse.ArgumentParser()
parser.add_argument('--theory', type=str, help='Name of theory to verify', required=True)
parser.add_argument('--lemma', type=str, help='Name of lemma to verify')
parser.add_argument('--profile', action='store_true', help='Enable profiling')
parser.add_argument('--print-time', action='store_true', help='Enable printing time')
args, unknown = parser.parse_known_args()

theory_name = args.theory
check_proof = True  # default to check all proofs
if args.lemma is not None:
    check_proof = args.lemma

if args.profile:
    pr = cProfile.Profile()
    pr.enable()

print_time = args.print_time

# Run check
os_parser.load_theory(theory_name, verbose=True, check_proof=check_proof, print_time=print_time)

if args.profile:
    p = Stats(pr)
    p.strip_dirs()
    p.sort_stats('cumtime')
    p.print_stats(100)
