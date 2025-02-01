# OSVAuto

OSVAuto is a tool designed for verifying functional specifications of operating system kernels. It consists of a language for defining data structures, invariants, and queries (verification conditions). Each query is translated into a form that can be accepted by SMT solvers. If the SMT solver returns a counterexample for a query, the tool attempts to translate it back into the form of the front-end language.

## Installation

We use Python version 3.12. The tool depends on Lark parser (version 0.12.0) and the Z3 solver (version 4.12.6.0). Install the dependencies as follows:

```bash
pip install -r requirements.txt
```

## Check examples from the paper

The following commands check examples in Section 4.4, and the uC/OS-II case study (the later should take about 3-4 minutes, timing information from an existing run is given in timing.txt).

```bash
python -m run --theory example1
python -m run --theory example2
python -m run --theory example3
python -m run --theory ucos --print-time
```


## Check a single theory or lemma

To check a theory file, place the file in the `osverify/theory` folder. Then use:

```bash
python -m run --theory <theory_name>
```

To check a single lemma in the theory, use:

```bash
python -m run --theory <theory_name> --lemma <lemma_name>
```

To print running time for each lemma, use:

```bash
python -m run --theory <theory_name> --print-time
```

## Running tests

Run all unit tests using the following:

```bash
python run_test.py
```
