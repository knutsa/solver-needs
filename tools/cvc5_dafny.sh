#!/bin/bash
# cvc5 launcher for Dafny (--solver-path). Boogie sends the resource limit,
# seed and time limit to Z3 only (and cvc5 rejects them once initialised), so
# they go on cvc5's command line here. The pipeline sets:
#   CVC5_PATH        the cvc5 binary (solver_needs.config.cvc5())
#   CVC5_RLIMIT_PER  resource limit per check-sat (0 = none)
#   CVC5_TLIMIT_PER  wall-clock limit per check-sat in ms (unset = none)
#   CVC5_SEED        random seed (unset = cvc5 default)
exec "${CVC5_PATH:?set CVC5_PATH to the cvc5 binary}" --rlimit-per="${CVC5_RLIMIT_PER:-0}" \
  ${CVC5_TLIMIT_PER:+--tlimit-per="$CVC5_TLIMIT_PER"} ${CVC5_SEED:+--seed="$CVC5_SEED"} "$@"
