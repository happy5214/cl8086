cl8086 - a proof-of-concept Intel 8086 emulator written in Common Lisp
======================================================================

This is a basic Intel 8086 emulator, which has enough functionality to execute
the "codegolf" program
(http://codegolf.stackexchange.com/questions/4732/emulate-an-intel-8086-cpu).

Please use the "codegolf" branch to run the executable. master is not guaranteed
to remain compatible with that program's non-standard assumptions, and it will
likely break at some point.

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

- All 8086 instructions not involving stuff listed as possible future additions
- All 8 general purpose byte and word registers
- IP register
- Flags: AF, CF, DF, OF, PF, SF, ZF (also FLAGS register)
- Loading instructions via a vector
- Binary-coded decimal (both packed and unpacked)
- String functions
- rep- and loop-type prefixes
- Segment registers that can be manipulated
- Opcode prefixes for segment overrides
- Full 1 MB RAM vector

Will be supported later
~~~~~~~~~~~~~~~~~~~~~~~
- Interrupts

May be supported later
~~~~~~~~~~~~~~~~~~~~~~
- Port-mapped IO
- Floating-point operations
- LOCK assertions
