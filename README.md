# Quantum Lean

A simple quantum computing simulation project implemented in Lean 4, featuring the Deutsch-Jozsa algorithm.

## Description

This project provides a basic framework for simulating quantum computations using the Lean 4 theorem prover. It includes implementations of:

- Qubit and quantum register representations
- Basic quantum gates (Hadamard, CNOT)
- Quantum circuit operations
- A simple measurement model
- The Deutsch-Jozsa algorithm

## Prerequisites

- Lean 4
- Lake (Lean's package manager)

## Installation

1. Clone the repository:
   ```
   git clone https://github.com/0x79de/quantum-lean.git
   cd quantum-lean
   ```

2. Build the project using Lake:
   ```
   lake build
   ```

## Usage

After building the project, you can run the main program:

```
lake run
```

This will execute the Deutsch-Jozsa algorithm with example functions.

## Modifying the Code

The main quantum circuit logic is in `QuantumLean.lean`. You can modify this file to implement different quantum algorithms or circuits.

