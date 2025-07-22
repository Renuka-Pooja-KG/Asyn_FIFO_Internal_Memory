# Makefile for Asynchronous FIFO UVM Verification (xrun + simvision only)

RTL_DIR = ../RTL
UVM_DIR = .

DESIGN_FILES = $(RTL_DIR)/async_fifo.sv \
               $(RTL_DIR)/fifo_mem.sv \
               $(RTL_DIR)/rptr_empty.sv \
               $(RTL_DIR)/wptr_full.sv \
               $(RTL_DIR)/rd_ndff_synch.sv \
               $(RTL_DIR)/wr_ndff_synch.sv

TB_FILES = $(UVM_DIR)/async_fifo_config.sv \
           $(UVM_DIR)/async_fifo_transaction.sv \
           $(UVM_DIR)/async_fifo_if.sv \
           $(UVM_DIR)/async_fifo_driver.sv \
           $(UVM_DIR)/async_fifo_monitor.sv \
           $(UVM_DIR)/async_fifo_sequencer.sv \
           $(UVM_DIR)/async_fifo_agent.sv \
           $(UVM_DIR)/async_fifo_base_seq.sv \
           $(UVM_DIR)/async_fifo_basic_seq.sv \
           $(UVM_DIR)/async_fifo_stress_seq.sv \
           $(UVM_DIR)/async_fifo_reset_seq.sv \
           $(UVM_DIR)/async_fifo_coverage.sv \
           $(UVM_DIR)/async_fifo_scoreboard.sv \
           $(UVM_DIR)/async_fifo_env.sv \
           $(UVM_DIR)/async_fifo_base_test.sv \
           $(UVM_DIR)/async_fifo_basic_test.sv \
           $(UVM_DIR)/async_fifo_stress_test.sv \
           $(UVM_DIR)/async_fifo_reset_test.sv \
           $(UVM_DIR)/async_fifo_tb.sv

UVMHOME ?= CDNS-1.1d
TEST ?= async_fifo_basic_test

help:
	@echo "//------------------- Asynchronous FIFO UVM Verification Makefile -------------------//"
	@echo "make run TEST=<test_name>     : Run the specified UVM test (default: async_fifo_basic_test)"
	@echo "make all                     : Run all major UVM tests (basic, stress, reset)"
	@echo "make waveform                : Open SimVision waveform viewer (waves.shm)"
	@echo "make clean                   : Remove all generated files and logs"
	@echo "make help                    : Show this help message"
	@echo "Available TEST values: async_fifo_basic_test, async_fifo_stress_test, async_fifo_reset_test, ..."
	@echo "//-----------------------------------------------------------------------------------//"

INCDIRS = +incdir+$(UVM_DIR) \
          +incdir+$(RTL_DIR)

run:
	@echo "[makefile] Running test: $(TEST)"
	xrun -access +rwc $(INCDIRS) $(DESIGN_FILES) $(TB_FILES) -uvmhome $(UVMHOME) +UVM_TESTNAME=$(TEST)

all:
	$(MAKE) run TEST=async_fifo_basic_test
	$(MAKE) run TEST=async_fifo_stress_test
	$(MAKE) run TEST=async_fifo_reset_test

waveform:
	@echo "[makefile] Launching SimVision for waveform viewing"
	simvision waves.shm &

clean:
	@echo "[makefile] Cleaning all generated files and logs"
	rm -rf work xcelium.d xcelium.h xrun.history xrun.log xrun.key INCA_libs *.vcd *.log *.wlf waves.shm

.PHONY: run all waveform clean help 