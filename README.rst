cl8086 - a proof-of-concept Intel 8086 emulator written in Common Lisp
======================================================================

This is a basic Intel 8086 emulator, which has enough functionality to execute
the "codegolf" program
(http://codegolf.stackexchange.com/questions/4732/emulate-an-intel-8086-cpu).

Though I wrote the code from scratch, I did use Julien Aubert's Python emulator
implementation (https://github.com/julienaubert/py8086) as a rough guide and
a source of inspiration, as well as a template for this documentation.

My code is licensed under the MIT License. The "codegolf" program has an
unknown license.

Instruction Support
-------------------

This was designed to support only the bare minimum required to run the
aforementioned program "codegolf". I have since started to further extend it.

Currently supported
~~~~~~~~~~~~~~~~~~~

- inc and dec with registers
- push and pop with registers
- xchg with registers and memory (including nop)
- mov with register and either a word or byte immediate
- mov using memory operands
- hlt
- stc and clc
- all 8 general purpose byte and word registers
- IP register
- Flags: AF, CF, OF, PF, SF, ZF
- Two fixed 64 kB segments of memory (general RAM and the stack)
- Loading instructions via a vector
- Basic arithmetic and logic (add, adc, sub, sbb, cmp, and, or, xor)
- Unconditional flow control (near call, near ret, short jmp)
- Conditional jumps using the five implemented flags (jb/jnb, jz/jnz, jbe/jnbe, js/jns, jl/jnl, jle/jnle, jp/jnp, jo/jno)
- BCD addition and subtraction (both packed and unpacked)
- test

May be supported later
~~~~~~~~~~~~~~~~~~~~~~
- Segments that be manipulated
- Opcode prefixes
- Interrupts or port IO
- String functions
- Two-byte opcodes
- Floating-point operations
