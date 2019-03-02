# Piccolo / CHERILLO

Piccolo is a simple 3-stage pipeline implementation of the RISC-V ISA, created by
Bluespec, Inc. It is primarily intended for low-end applications such as embedded
computing and IoT devices. It is specified in Bluespec SystemVerilog. The original
version can be found in Bluespec's own github at https://github.com/bluespec/Piccolo.

This repository contains modified sources, using Piccolo as a basis for implementing
a capability-based memory security model designed by the CTSRD group in the
Department of Computer Science and Technology at the University of Cambridge
(https://www.cl.cam.ac.uk/research/security/ctsrd).

The foremost changes have been made by myself (Jack Deeley), with assistance and 
contributions from Jon Woodruff, Peter Rugg, Alexandre Joannou and others in the 
research group.

This work is intended as part of my examination for Part II of the Computer Science
Tripos. All contributions and copyright should be identified at the top of any
relevant files, or in commit logs for the various repositories (Bluespec, CTSRD and
my own).
