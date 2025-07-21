# Makefile for Asynchronous FIFO UVM Verification

# Tool selection
SIMULATOR ?= questa
TEST ?= async_fifo_basic_test

# Design files
DESIGN_FILES = async_fifo.sv fifo_mem.sv rptr_empty.sv wptr_full.sv rd_ndff_synch.sv wr_ndff_synch.sv

# Testbench files
TB_FILES = tb/async_fifo_pkg.sv \
           tb/interface/async_fifo_if.sv \
           tb/agent/async_fifo_driver.sv \
           tb/agent/async_fifo_monitor.sv \
           tb/agent/async_fifo_sequencer.sv \
           tb/agent/async_fifo_agent.sv \
           tb/sequence/async_fifo_base_seq.sv \
           tb/sequence/async_fifo_basic_seq.sv \
           tb/sequence/async_fifo_stress_seq.sv \
           tb/sequence/async_fifo_reset_seq.sv \
           tb/coverage/async_fifo_coverage.sv \
           tb/scoreboard/async_fifo_scoreboard.sv \
           tb/async_fifo_env.sv \
           tb/test/async_fifo_base_test.sv \
           tb/test/async_fifo_basic_test.sv \
           tb/test/async_fifo_stress_test.sv \
           tb/test/async_fifo_reset_test.sv \
           tb/async_fifo_tb.sv

# UVM library path (adjust based on your installation)
UVM_HOME ?= /opt/questa/questa-2023.4/verilog_src/uvm-1.2

# Compilation flags
VLOG_FLAGS = -sv +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
VSIM_FLAGS = -c -do "run -all; quit"

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
	@echo "  SIMULATOR     - Simulation tool (questa, vcs, modelsim)"
	@echo "  TEST          - Test to run (async_fifo_basic_test, async_fifo_stress_test, async_fifo_reset_test)"
	@echo "  UVM_HOME      - Path to UVM library"
	@echo ""
	@echo "Examples:"
	@echo "  make SIMULATOR=questa TEST=async_fifo_basic_test"
	@echo "  make SIMULATOR=vcs TEST=async_fifo_stress_test"
	@echo "  make clean"

# Test targets
test-basic:
	$(MAKE) TEST=async_fifo_basic_test run

test-stress:
	$(MAKE) TEST=async_fifo_stress_test run

test-reset:
	$(MAKE) TEST=async_fifo_reset_test run

# Coverage
coverage:
	$(MAKE) VSIM_FLAGS="-c -coverage -do \"run -all; coverage save -onexit fifo.ucdb; quit\"" run

# Waveform
wave:
	vsim -gui async_fifo_tb +UVM_TESTNAME=$(TEST) -do "run -all"

.PHONY: all compile run clean help test-basic test-stress test-reset coverage wave 