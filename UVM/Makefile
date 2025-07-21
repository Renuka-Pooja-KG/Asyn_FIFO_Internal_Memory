# Makefile for Asynchronous FIFO UVM Verification (Cadence, Questa, VCS)

# Tool selection
SIMULATOR ?= questa
TEST ?= async_fifo_basic_test

# RTL and UVM directories
RTL_DIR = ../RTL
UVM_DIR = .

# Design files
DESIGN_FILES = $(RTL_DIR)/async_fifo.sv \
               $(RTL_DIR)/fifo_mem.sv \
               $(RTL_DIR)/rptr_empty.sv \
               $(RTL_DIR)/wptr_full.sv \
               $(RTL_DIR)/rd_ndff_synch.sv \
               $(RTL_DIR)/wr_ndff_synch.sv

# UVM testbench files
TB_FILES = $(UVM_DIR)/async_fifo_pkg.sv \
           $(UVM_DIR)/interface/async_fifo_if.sv \
           $(UVM_DIR)/agent/async_fifo_driver.sv \
           $(UVM_DIR)/agent/async_fifo_monitor.sv \
           $(UVM_DIR)/agent/async_fifo_sequencer.sv \
           $(UVM_DIR)/agent/async_fifo_agent.sv \
           $(UVM_DIR)/sequence/async_fifo_base_seq.sv \
           $(UVM_DIR)/sequence/async_fifo_basic_seq.sv \
           $(UVM_DIR)/sequence/async_fifo_stress_seq.sv \
           $(UVM_DIR)/sequence/async_fifo_reset_seq.sv \
           $(UVM_DIR)/coverage/async_fifo_coverage.sv \
           $(UVM_DIR)/scoreboard/async_fifo_scoreboard.sv \
           $(UVM_DIR)/async_fifo_env.sv \
           $(UVM_DIR)/test/async_fifo_base_test.sv \
           $(UVM_DIR)/test/async_fifo_basic_test.sv \
           $(UVM_DIR)/test/async_fifo_stress_test.sv \
           $(UVM_DIR)/test/async_fifo_reset_test.sv \
           $(UVM_DIR)/async_fifo_tb.sv

# UVM library path (adjust based on your installation)
UVM_HOME ?= /opt/questa/questa-2023.4/verilog_src/uvm-1.2

# Compilation flags
VLOG_FLAGS = -sv +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
VSIM_FLAGS = -c -do "run -all; quit"

# Cadence Xcelium (xrun) flags
XRUN_FLAGS = -uvm -access +rwc -timescale 1ns/1ps -64bit -linedebug +UVM_TESTNAME=$(TEST) \
             -incdir $(UVM_DIR) -incdir $(UVM_DIR)/interface -incdir $(UVM_DIR)/agent -incdir $(UVM_DIR)/sequence \
             -incdir $(UVM_DIR)/coverage -incdir $(UVM_DIR)/scoreboard -incdir $(UVM_DIR)/test -incdir $(RTL_DIR)

# Default target
all: compile run

# Compile with QuestaSim
compile-questa:
	@echo "Compiling with QuestaSim..."
	vlib work
	vlog $(VLOG_FLAGS) $(DESIGN_FILES) $(TB_FILES)

# Compile with VCS
compile-vcs:
	@echo "Compiling with VCS..."
	vcs -full64 -sverilog +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv $(DESIGN_FILES) $(TB_FILES)

# Compile with ModelSim
compile-modelsim:
	@echo "Compiling with ModelSim..."
	vlib work
	vlog -sv +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv $(DESIGN_FILES) $(TB_FILES)

# Compile with Cadence Xcelium
compile-xrun:
	@echo "Compiling with Cadence Xcelium..."
	xrun -elaborate -64bit $(XRUN_FLAGS) $(DESIGN_FILES) $(TB_FILES)

# Run with QuestaSim
run-questa:
	@echo "Running $(TEST) with QuestaSim..."
	vsim -c async_fifo_tb +UVM_TESTNAME=$(TEST) -do "run -all; quit"

# Run with VCS
run-vcs:
	@echo "Running $(TEST) with VCS..."
	./simv +UVM_TESTNAME=$(TEST)

# Run with ModelSim
run-modelsim:
	@echo "Running $(TEST) with ModelSim..."
	vsim -c async_fifo_tb +UVM_TESTNAME=$(TEST) -do "run -all; quit"

# Run with Cadence Xcelium
run-xrun:
	@echo "Running $(TEST) with Cadence Xcelium..."
	xrun $(XRUN_FLAGS) $(DESIGN_FILES) $(TB_FILES)

# Compile based on simulator
compile: compile-$(SIMULATOR)

# Run based on simulator
run: run-$(SIMULATOR)

# Clean
clean:
	@echo "Cleaning..."
	rm -rf work
	rm -rf transcript
	rm -rf vsim.wlf
	rm -rf simv
	rm -rf simv.daidir
	rm -rf csrc
	rm -rf *.vcd
	rm -rf *.log
	rm -rf *.wlf
	rm -rf xcelium.d xcelium.h xrun.history xrun.log xrun.key INCA_libs

# Help
help:
	@echo "Available targets:"
	@echo "  compile        - Compile the design and testbench"
	@echo "  run           - Run simulation"
	@echo "  all           - Compile and run"
	@echo "  clean         - Clean generated files"
	@echo "  help          - Show this help"
	@echo ""
	@echo "Variables:"
	@echo "  SIMULATOR     - Simulation tool (questa, vcs, modelsim, xrun)"
	@echo "  TEST          - Test to run (async_fifo_basic_test, async_fifo_stress_test, async_fifo_reset_test)"
	@echo "  UVM_HOME      - Path to UVM library (for Questa/VCS/ModelSim)"
	@echo ""
	@echo "Examples:"
	@echo "  make SIMULATOR=xrun TEST=async_fifo_basic_test"
	@echo "  make SIMULATOR=questa TEST=async_fifo_stress_test"
	@echo "  make clean"

# Test targets
test-basic:
	$(MAKE) TEST=async_fifo_basic_test run

test-stress:
	$(MAKE) TEST=async_fifo_stress_test run

test-reset:
	$(MAKE) TEST=async_fifo_reset_test run

# Coverage (Cadence)
coverage-xrun:
	xrun -coverage all $(XRUN_FLAGS) $(DESIGN_FILES) $(TB_FILES)

# Waveform (Cadence)
wave-xrun:
	xrun -gui $(XRUN_FLAGS) $(DESIGN_FILES) $(TB_FILES)

.PHONY: all compile run clean help test-basic test-stress test-reset coverage-xrun wave-xrun 