# Gibbs Measures

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements
and theorem proofs. Digitisation, or formalisation, is a process where the source material,
typically a mathematical textbook or a pdf file or website or video, is transformed into definitions
in a target system consisting of a computer implementation of a logical theory (such as set theory
or type theory).

## The source

The definitions, theorems and proofs in this repository are taken from the book [Gibbs Measures and
Phase Transitions](https://doi.org/10.1515/9783110250329) by Hans-Otto Georgii.

The goal is to prove existence and uniqueness of Gibbs measures.

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a
project being developed by the [Lean FRO](https://lean-fro.org/) AWS by Leonardo de Moura and his
team.

## Content of this project

This project currently contains a definition of Gibbs measures, but no construction yet.

### Code organisation

The Lean code is contained in the directory `GibbsMeasure/`. The subdirectories are:
* `Mathlib`: Material missing from existing Mathlib developments
* `Prereqs`: New developments to be integrated to Mathlib

## What next?

On top of the new developments, there are many basic lemmas needed for this project that are
currently missing from Mathlib.

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html)
(under Regular install).
Alternatively, click on the button below to open a Gitpod workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/james18lpc/GibbsMeasure)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Build the blueprint

To build the web version of the blueprint, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip install -r blueprint/requirements.txt
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
```

## Acknowledgements

Our project builds on Mathlib. We must therefore thank its numerous contributors without whom this
project couldn't even have started.

Much of the project infrastructure has been adapted from
* [sphere eversion](https://leanprover-community.github.io/sphere-eversion/)
* [liquid tensor experiment](https://github.com/leanprover-community/liquid/)
* [unit fractions](https://github.com/b-mehta/unit-fractions/)

## Source reference

[G]: https://doi.org/10.1515/9783110250329
