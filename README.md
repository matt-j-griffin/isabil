# IsaBIL

A formalisation of the [Binary Analysis Platform (BAP) Intermediary Langugage (BIL)](https://github.com/BinaryAnalysisPlatform/bap) in Isabelle/HOL.

## Requirements 

These theories have been tested with `Isabelle/HOL 2024` and the equivalent [AFP](https://www.isa-afp.org/).

You will need to build this projects dependencies: [Eisbach Inline Match](https://github.com/matt-j-griffin/eisbach-inline-match).

## Installation

Build in the root of the repository (where `ROOT` file is located) using `isabelle build -D .`.

To use these theories in your own work, add this repository to Isabelle: `isabelle components -u .`.
