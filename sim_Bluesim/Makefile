###  -*-Makefile-*-

# Copyright (c) 2018 Bluespec, Inc. All Rights Reserved


#-
# RVFI_DII modifications:
#     Copyright (c) 2018 Jack Deeley
#     Copyright (c) 2018 Peter Rugg
#     All rights reserved.
#
#     This software was developed by SRI International and the University of
#     Cambridge Computer Laboratory (Department of Computer Science and
#     Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
#     DARPA SSITH research programme.
#-

# ================================================================

.PHONY: help
help:
	@echo 'options: sim32 b32 sim64 b64 simV64 simV32 bV64 simD64 bD64 test32 test64'

.PHONY: all
all: compile link

.PHONY: trueall
trueall: sim32 b32 sim64 b64 simV64 bV64 simD64 bD64

# ================================================================
# Compiling the system

# ----------------
# Search path for bsc for .bsv files
REPO = ..

CORE_DIRS = $(REPO)/src_Core/ISA:$(REPO)/src_Core/RegFiles:$(REPO)/src_Core/Core:$(REPO)/src_Core/Near_Mem_VM:$(REPO)/src_Core/BSV_Additional_Libs:$(REPO)/src_Verifier
TESTBENCH_DIRS  = $(REPO)/src_Testbench/Top:$(REPO)/src_Testbench/SoC:$(REPO)/src_Testbench/Fabrics/AXI4_Lite
RVFI_DII_DIRS = $(REPO)/src_Verifier/BSV-RVFI-DII
BSC_PATH = -p $(CORE_DIRS):$(TESTBENCH_DIRS):$(RVFI_DII_DIRS):+
USEFUL_FLAGS = #-remove-unused-modules -remove-empty-rules -remove-starved-rules -remove-false-rules

# ----------------
# Top-level file and module

TOPFILE   = $(REPO)/src_Testbench/Top/Top_HW_Side.bsv
TOPMODULE = mkTop_HW_Side
RVFI_DII_TOPMODULE = mkPiccolo_RVFI_DII

#----------------
# bsc flags

# Implementation choice: SHIFT_BARREL, SHIFT_SERIAL, SHIFT_MULT, SHIFT_NONE
# Implementation choice: MULT_SYNTH, MULT_SERIAL

BSC_FLAGS += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV32 \
		-D SV32 \
		-D FABRIC32 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D ISA_M \
		-D Near_Mem_Caches \
		-D SHIFT_BARREL \
		-D MULT_SERIAL\
		-D CSR_REGFILE_UM \
		+RTS -K64M -RTS  -show-range-conflict

BSC_FLAGS64 += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV64 \
		-D FABRIC64 \
		-D SV39 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D ISA_M \
		-D Near_Mem_Caches \
		-D SHIFT_BARREL \
		-D MULT_SERIAL\
		-D CSR_REGFILE_UM \
		+RTS -K64M -RTS  -show-range-conflict

BSC_FLAGS64FULL += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV64 \
		-D FABRIC64 \
		-D SV39 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D ISA_M \
		-D ISA_A \
		-D Near_Mem_Caches \
		-D SHIFT_BARREL \
		-D MULT_SERIAL\
		-D CSR_REGFILE_UM \
		+RTS -K64M -RTS  -show-range-conflict

BSC_FLAGS64VERIF += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV64 \
		-D FABRIC64 \
		-D SV39 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D ISA_M \
		-D ISA_A \
		-D Near_Mem_Caches \
		-D SHIFT_BARREL \
		-D MULT_SERIAL\
		-D CSR_REGFILE_UM \
		-D RVFI \
		-D RVFI_DII \
		+RTS -K64M -RTS  -show-range-conflict

BSC_FLAGS32VERIF += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV32 \
		-D SV32 \
		-D FABRIC32 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D ISA_M \
		-D Near_Mem_Caches \
		-D SHIFT_BARREL \
		-D MULT_SERIAL\
		-D CSR_REGFILE_UM \
		-D RVFI \
		-D RVFI_DII \
		+RTS -K64M -RTS  -show-range-conflict

BSC_FLAGSGDB += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV64 \
		-D FABRIC64 \
		-D SV39 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_M \
		-D ISA_A \
		-D SHIFT_BARREL \
		-D MULT_SERIAL\
		-D CSR_REGFILE_UM \
		-D INCLUDE_GDB_CONTROL\
		-D Near_Mem_Caches \
		+RTS -K64M -RTS  -show-range-conflict
		
BSC_CHERIFLAGS += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV64 \
		-D FABRIC64 \
		-D SV39 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D Near_Mem_Caches \
		-D SHIFT_BARREL \
		-D CSR_REGFILE_UM \
		-D CHERI \
		+RTS -K64M -RTS  -show-range-conflict
		
		
BSC_CHERISIMS += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV64 \
		-D FABRIC64 \
		-D SV39 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D SHIFT_BARREL \
		-D CSR_REGFILE_UM \
		-D Near_Mem_Caches \
		-D CHERI\
		+RTS -K64M -RTS  -show-range-conflict
		#-D INCLUDE_GDB_CONTROL\
		
BSC_CHERIV += -keep-fires -aggressive-conditions -no-warn-action-shadowing \
		-suppress-warnings G0020 \
		-D RV64 \
		-D FABRIC64 \
		-D SV39 \
		-D ISA_PRIV_M \
		-D ISA_PRIV_U \
		-D ISA_PRIV_S \
		-D ISA_M \
		-D ISA_A \
		-D Near_Mem_Caches \
		-D SHIFT_BARREL \
		-D MULT_SERIAL\
		-D CSR_REGFILE_UM \
		-D CHERI \
		-D CHERIDEBUG \
		-D RVFI \
		-D RVFI_DII \
		+RTS -K64M -RTS  -show-range-conflict

# ================================================================
# Make targets

TMP_DIRS   = -bdir sim32 -simdir sim32 -info-dir sim32
TMP_VDIRS  = -bdir b32 -simdir b32 -info-dir b32 -vdir b32
TMP_64SIM  = -bdir sim64 -simdir sim64 -info-dir sim64
TMP_64DIRS = -bdir b64 -simdir b64 -info-dir b64 -vdir b64

TMP_64FDIRS = -bdir f64 -simdir f64 -info-dir f64 -vdir f64

TMP_VERIF64 = -bdir simv64 -simdir simv64 -info-dir simv64 -vdir simv64
TMP_VERIF32 = -bdir simv32 -simdir simv32 -info-dir simv32 -vdir simv32
TMP_LOGIF = -bdir bv64 -simdir bv64 -info-dir bv64 -vdir bv64

TMP_GDBV = -bdir gdbv -simdir gdbv -info-dir gdbv -vdir gdbv
TMP_GDB = -bdir gdb -simdir gdb -info-dir gdb -vdir gdb

TMP_CHERI = -bdir cherib -simdir cherib -info-dir cherib -vdir cherib
TMP_CHERISIM = -bdir cherisim -simdir cherisim -info-dir cherisim -vdir cherisim
TMP_CHERIV = -bdir cheriv -simdir cheriv -info-dir cheriv -vdir cheriv

.PHONY: sim32
sim32:
	@echo "INFO: Compiling simulation (CPU, 32-bit)"
	mkdir -p  sim32
	bsc -u -elab -sim -D SIM $(USEFUL_FLAGS) $(TMP_DIRS)  $(BSC_FLAGS)  $(BSC_PATH)  $(TOPFILE)
	@echo "INFO: Compiled  Core (CPU, Caches)"
	@echo "INFO: Linking bsc-compiled objects into Bluesim executable"
	bsc -sim -parallel-sim-link 8 \
		$(TMP_DIRS)\
		-e $(TOPMODULE) -o ./$(BSIM_EXE_FILE) \
		$(BSC_C_FLAGS)\
		$(REPO)/src_Testbench/Top/C_ConsoleIO_functions.c
	@echo "INFO: Linked bsc-compiled objects into Bluesim executable"

.PHONY: b32
b32:
	@echo "INFO: Compiling to verilog (CPU, 32-bit)"
	mkdir -p  b32
	bsc -u -elab -verilog -D VERILOG $(USEFUL_FLAGS) $(TMP_VDIRS)  $(BSC_FLAGS)  $(BSC_PATH)  ../src_Core/Core/CPU.bsv
	@echo "INFO: Re-compiled  Core (CPU)"

.PHONY: sim64
sim64:
	@echo "INFO: Compiling simulation (CPU, 64-bit)"
	mkdir -p  sim64
	bsc -u -elab -sim -D SIM $(USEFUL_FLAGS) $(TMP_64SIM)  $(BSC_FLAGS64FULL)  $(BSC_PATH)  $(TOPFILE)
	@echo "INFO: Re-compiled  Core (CPU, Caches)"
	@echo "INFO: linking bsc-compiled objects into Bluesim executable"
	bsc -sim -parallel-sim-link 8 \
		$(TMP_64SIM)\
		-e $(TOPMODULE) -o ./$(BSIM_EXE_FILE64) \
		$(BSC_C_FLAGS)\
		$(REPO)/src_Testbench/Top/C_ConsoleIO_functions.c
	@echo "INFO: linked bsc-compiled objects into Bluesim executable"

.PHONY: b64
b64:
	@echo "INFO: Compiling to verilog (CPU, 64-bit)"
	mkdir -p b64
	bsc -u -elab -verilog -D VERILOG $(USEFUL_FLAGS) $(TMP_64DIRS) $(BSC_FLAGS64) $(BSC_PATH) ../src_Core/Core/CPU.bsv
	@echo "INFO: Compiled 64-bit CPU to verilog"

.PHONY: bF64
bF64:
	@echo "INFO: Compiling experimental ISA_FD verilog (CPU, 64-bit)"
	mkdir -p f64
	bsc -u -elab -verilog -D VERILOG $(USEFUL_FLAGS) $(TMP_64FDIRS) $(BSC_FLAGS64) -D ISA_F -D ISA_D $(BSC_PATH) ../src_Core/Core/CPU.bsv
	@echo "INFO: Compiled 64-bit CPU to verilog"

.PHONY: simV32
simV32:
	@echo "INFO: Compiling 32-bit CPU with Verifier attachments"
	mkdir -p  simv32
	bsc -u -elab -sim -D SIM $(TMP_VERIF32) $(BSC_FLAGS32VERIF)  $(BSC_PATH)  $(TOPFILE)
	@echo "INFO: Compiled  Core (CPU, Caches)"
	@echo "INFO: Linking bsc-compiled objects into Bluesim executable"
	bsc -sim -parallel-sim-link 8 \
		$(TMP_VERIF32)\
		-e $(RVFI_DII_TOPMODULE) -o ./$(BSIM_EXE_FV32) \
		$(BSC_C_FLAGS)\
		$(REPO)/src_Testbench/Top/C_ConsoleIO_functions.c \
		$(REPO)/src_Verifier/BSV-RVFI-DII/SocketPacketUtils/socket_packet_utils.c
	@echo "INFO: Linked bsc-compiled objects into Bluesim executable"

.PHONY: bV64
bV64:
	@echo "INFO: Compiling Verifier CPU to verilog"
	mkdir -p bv64
	bsc -u -elab -verilog -D VERILOG $(TMP_LOGIF) $(BSC_FLAGS64VERIF)  $(BSC_PATH) -g mkVerifier_CPU ../src_Verifier/Verifier_CPU.bsv
	@echo "INFO: Compilation completed"


.PHONY: simD64
simD64:
	@echo "INFO: Compiling GDB CPU for simulation"
	mkdir -p gdb
	bsc -u -elab -sim -D SIM $(USEFUL_FLAGS) $(TMP_GDB) $(BSC_FLAGSGDB) $(BSC_PATH) $(TOPFILE)
	@echo "INFO: Compilation completed, starting linking"
	bsc -sim -parallel-sim-link 8 \
		$(TMP_GDB)\
		-e $(TOPMODULE) -o ./$(BSIM_EXE_FILEGDB) \
		$(BSC_C_FLAGS)\
		$(REPO)/src_Testbench/Top/C_ConsoleIO_functions.c
	@echo "INFO: linked debug objects into Bluesim executable"
    
    
.PHONY: bD64
bD64:
	@echo "INFO: Compiling GDB CPU to verilog"
	mkdir -p gdbv
	bsc -u -elab -verilog $(USEFUL_FLAGS) $(TMP_GDBV) $(BSC_FLAGSGDB) $(BSC_PATH) ../src_Core/Core/CPU.bsv
	@echo "INFO: Compilation completed"
	
.PHONY: cheri
cheri:
	@echo "INFO: Compiling CHERI..."
	mkdir -p cherib
	bsc -u -elab -verilog $(USEFUL_FLAGS) $(TMP_CHERI) $(BSC_CHERIFLAGS) $(BSC_PATH) ../src_Core/Core/CPU.bsv
	@echo "INFO: Compilation completed"


.PHONY: cherisim
cherisim:
	@echo "INFO: Compiling CHERI for simulation"
	mkdir -p cherisim
	bsc -u -elab -sim -D SIM $(USEFUL_FLAGS) $(TMP_CHERISIM) $(BSC_CHERISIMS) $(BSC_PATH) $(TOPFILE)
	@echo "INFO: Compilation completed, starting linking"
	bsc -sim -parallel-sim-link 8 \
		$(TMP_CHERISIM)\
		-e $(TOPMODULE) -o ./$(BSIM_EXE_CHERI) \
		$(BSC_C_FLAGS)\
		$(REPO)/src_Testbench/Top/C_ConsoleIO_functions.c
	@echo "INFO: linked CHERI objects into Bluesim executable"
	
.PHONY: simV64
simV64:
	@echo "INFO: Compiling 64-bit CPU with Verifier attachments"
	mkdir -p  simv64
	bsc -u -elab -sim -D SIM $(TMP_VERIF64) $(BSC_FLAGS64VERIF)  $(BSC_PATH)  $(TOPFILE)
	@echo "INFO: Compilation completed"
	@echo "INFO: linking bsc-compiled objects into Bluesim executable"
	CC=gcc-4.8 CXX=g++-4.8 bsc -sim -parallel-sim-link 8 \
		$(TMP_VERIF64) \
		-e $(RVFI_DII_TOPMODULE) -o ./$(BSIM_EXE_FV64) \
		$(BSC_C_FLAGS)\
		$(REPO)/src_Testbench/Top/C_ConsoleIO_functions.c \
		$(REPO)/src_Verifier/BSV-RVFI-DII/SocketPacketUtils/socket_packet_utils.c
	@echo "INFO: linked bsc-compiled objects into Bluesim executable"

	
.PHONY: cheriV
cheriV:
	@echo "INFO: Compiling CHERI RVFI for simulation"
	mkdir -p cheriv
	bsc -u -elab -sim -D SIM $(USEFUL_FLAGS) $(TMP_CHERIV) $(BSC_CHERIV) $(BSC_PATH) $(TOPFILE)
	@echo "INFO: Compilation completed, starting linking"
	CC=gcc-4.8 CXX=g++-4.8 bsc -sim -parallel-sim-link 8 \
		$(TMP_CHERIV)\
		-e $(RVFI_DII_TOPMODULE) -o ./$(BSIM_EXE_CHERIV) \
		$(BSC_C_FLAGS)\
		$(REPO)/src_Testbench/Top/C_ConsoleIO_functions.c \
		$(REPO)/src_Verifier/BSV-RVFI-DII/SocketPacketUtils/socket_packet_utils.c
	@echo "INFO: linked CHERI objects into Bluesim executable"


BSIM_EXE_FILE = exe_HW_bsim
BSIM_EXE_FILE64 = exe_HW_bsim64
BSIM_EXE_FV64 = exe_HW_vs64
BSIM_EXE_FV32 = exe_HW_vs32
BSIM_EXE_FILEGDB = exe_GDB
BSIM_EXE_CHERI = exe_CHERI
BSIM_EXE_CHERIV = exe_CHERIV

BSC_C_FLAGS += \
	-Xc++  -D_GLIBCXX_USE_CXX11_ABI=0 \
	-Xl -v \
	-Xc -O3 -Xc++ -O3 \

# ================================================================
# Test: run the executable on the standard 'add' RISCV ISA test

.PHONY: test32
test32:
	make -C  ../Tests/elf_to_hex
	../Tests/elf_to_hex/elf_to_hex  ../Tests/isa/rv32ui-p-add  Mem.hex
	./$(BSIM_EXE_FILE)  -m 2500  +v1  +tohost

.PHONY: test64
test64:
	make -C  ../Tests/elf_to_hex
	../Tests/elf_to_hex/elf_to_hex  ../Tests/isa/rv64ui-p-add  Mem.hex
	./$(BSIM_EXE_FILE64)  -m 2500  +v1  +tohost

# ================================================================

.PHONY: clean
clean:
	rm -r -f  *~  build
	rm -rf buildv
	rm -rf buildsoc
	rm -rf sim32 sim64 b32 b64 simv64 bv64 gdbv gdb simv32 cherib cheriv cherisim rvfib
	rm -f $(addprefix $(BSIM_EXE_FILE), *) $(addprefix $(BSIM_EXE_FILE64), *) $(addprefix $(BSIM_EXE_FV64), *) $(addprefix $(BSIM_EXE_FV32), *) $(addprefix $(BSIM_EXE_FILEGDB), *)
	rm -f Mem.hex 

.PHONY: simclean
simclean:
	rm -rf build

.PHONY: vclean
vclean:
	rm -rf buildv
	rm -rf buildsoc

.PHONY: full_clean
full_clean: clean
	rm -r -f  *~  $(SIM_EXE_FILE)*  *.log  *.vcd  *.hex

# ================================================================
