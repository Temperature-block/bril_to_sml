# BRIL to Standard ML Compiler

This project provides a translation utility to convert [BRIL (Big Restricted Intermediate Language)](https://capra.cs.cornell.edu/bril/) programs—specifically those previously transformed into Static Single Assignment (SSA) form—into executable Standard ML (SML) code.

## How it Works

The translator leverages the CFG and SSA dominance information to structure the resulting SML code. 

1. **SSA to Functional Form:** Standard ML is a functional language. To model the CFG of imperative BRIL code, each basic block in the CFG is translated into a mutually recursive SML function (`fun ... and ...`).
2. **Phi ($\phi$) Nodes to Arguments:** In SSA form, $\phi$-nodes select values based on the predecessor block. This translator models $\phi$-nodes as arguments to the SML functions representing the basic blocks.
   * If a variable is definitely defined before reaching a block, it is passed directly as an argument.
   * If a variable might be undefined (e.g., coming from a path where it was never initialized before reaching the $\phi$-node), it is wrapped in an SML `option` type (`SOME` or `NONE`), and the function signature is adjusted accordingly.
3. **Instruction Synthesis (`synthesize_block_instrs`):** BRIL instructions (arithmetic, logical, printing) are mapped directly to their SML equivalents using the `sml_correspondence` dictionary. 
4. **Control Flow (`sml_elaborator`):** BRIL branch (`br`) and jump (`jmp`) instructions are converted into tail-recursive function calls to the next block, passing the necessary arguments to satisfy the target block's $\phi$-nodes.
5. **Name Legalization (`replace_invalid_names`):** Since SSA often introduces names like `x.1` or `val.2` (which are invalid identifiers in SML due to the dot), the translator uses a regex pass to convert these to SML-compliant names like `x_1` and `val_2`.
