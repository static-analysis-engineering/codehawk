# CodeHawk Tool Suite

The CodeHawk Tool Suite, developed by Kestrel Technology, is a sound
static analysis platform based on the mathematical theory of
abstract interpretation developed by Patrick and Radhia Cousot.
CodeHawk consists of a programming-language independent abstract
interpretation engine and three language front ends, as shown
![below](figures/codehawk_toolsuite.png).

This repository contains the source code for the abstract
interpretation engine and the three analyzer front ends:

- **CH**: Abstract Interpretation Engine and utilities
- **CHB**: Binary analyzer (x86, mips) front end (in preparation)
- **CHC**: C source code analyzer front end
- **CHJ**: Java byte code analyzer (in preparation)

This repository is intended to be for reference only. The actual
analyzers are provided in separate repositories with an extensive
Python API to run the analyzer and report results:

- **KTAccelerate**: Binary Analyzer (to be released soon)
- **KTAdvance**: C Source Code Analyzer (to be released soon)
- **KTAlgoComplexity**: Java byte code Analyzer (to be released soon)




