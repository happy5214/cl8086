cl8086 - a proof-of-concept Intel 8086 emulator written in Common Lisp
======================================================================

This is a basic Intel 8086 emulator, which will (eventually) have enough
functionality to execute the "codegolf" program
(http://codegolf.stackexchange.com/questions/4732/emulate-an-intel-8086-cpu).

Though I wrote the code from scratch, I did use Julien Aubert's Python emulator
implementation (https://github.com/julienaubert/py8086) as a rough guide and
a source of inspiration, as well as a template for this documentation.

This is licensed under the MIT License. 

Instruction Support
-------------------

This will probably only support the bare minimum required to run the aforementioned program "codegolf".

Currently supported
~~~~~~~~~~~~~~~~~~~

- inc and dec with registers
- push and pop with registers
- xchg with ax and another register (including nop)
- mov with register and either a word or byte immediate
- hlt
- stc and clc
- all 8 general purpose byte and word registers
- IP register
- CF, SF, and ZF flags
- Two fixed 64 kB segments of memory (general RAM and the stack)
- Loading instructions via a vector

Will be supported
~~~~~~~~~~~~~~~~~
- mov using memory operands
- Basic arithmetic and logic (add, adc, sub, sbb, cmp, and, or, xor)
- Unconditional flow control (call, ret, jmp)
- Conditional jumps using the three implemented flags (jb, jz, jbe, js, jnb, jnz, jnbe, jns)

Will not be supported
~~~~~~~~~~~~~~~~~~~~~
- Segments that be manipulated
- Opcode prefixes
- Interrupts or port IO
- String functions
- Two-byte opcodes
- Floating-point operations
