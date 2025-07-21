# Asynchronous FIFO with Internal Memory - UVM Verification Plan

## Design Overview
This project implements an Asynchronous FIFO with internal memory featuring:
- **Clock Domain Crossing (CDC)** synchronization
- **Configurable parameters** for data width, depth, and features
- **Power saving** and **pipelined read/write** options
- **Soft reset** and **memory reset** capabilities
- **Overflow/Underflow** detection with sticky error support

## Design Files
- `async_fifo.sv` - Top-level FIFO module
- `fifo_mem.sv` - Internal memory module
- `rptr_empty.sv` - Read pointer and empty logic
- `wptr_full.sv` - Write pointer and full logic
- `rd_ndff_synch.sv` - Read-to-write CDC synchronizer
- `wr_ndff_synch.sv` - Write-to-read CDC synchronizer

## UVM Verification Architecture

### 1. Testbench Structure
```
tb/
├── async_fifo_tb.sv              # Top-level testbench
├── async_fifo_pkg.sv             # UVM package
├── interface/
│   ├── async_fifo_if.sv          # Interface definition
│   └── async_fifo_monitor_if.sv  # Monitor interface
├── sequence/
│   ├── async_fifo_base_seq.sv    # Base sequence
│   ├── async_fifo_basic_seq.sv   # Basic functionality sequence
│   ├── async_fifo_stress_seq.sv  # Stress testing sequence
│   ├── async_fifo_cdc_seq.sv     # CDC testing sequence
│   └── async_fifo_reset_seq.sv   # Reset testing sequence
├── test/
│   ├── async_fifo_base_test.sv   # Base test
│   ├── async_fifo_basic_test.sv  # Basic functionality test
│   ├── async_fifo_stress_test.sv # Stress test
│   ├── async_fifo_cdc_test.sv    # CDC test
│   └── async_fifo_reset_test.sv  # Reset test
├── coverage/
│   └── async_fifo_coverage.sv    # Coverage model
├── scoreboard/
│   └── async_fifo_scoreboard.sv  # Scoreboard
└── agent/
    ├── async_fifo_agent.sv       # Agent
    ├── async_fifo_driver.sv      # Driver
    ├── async_fifo_monitor.sv     # Monitor
    └── async_fifo_sequencer.sv   # Sequencer
```

### 2. Key Verification Features

#### A. Functional Coverage
- **Data Integrity**: Verify data written matches data read
- **FIFO States**: Empty, Full, Almost Empty, Almost Full
- **Pointer Behavior**: Gray code conversion, pointer synchronization
- **Reset Scenarios**: Hardware reset, soft reset, memory reset
- **CDC Synchronization**: Metastability handling, synchronization stages
- **Error Conditions**: Overflow, underflow, sticky error behavior

#### B. Test Scenarios
1. **Basic Functionality**
   - Write/Read operations
   - Empty/Full conditions
   - Almost empty/full conditions

2. **CDC Testing**
   - Different clock frequencies
   - Clock domain crossing timing
   - Metastability scenarios

3. **Reset Testing**
   - Hardware reset during operations
   - Soft reset behavior
   - Memory reset functionality

4. **Stress Testing**
   - High-frequency operations
   - Back-to-back operations
   - Corner cases

5. **Error Injection**
   - Overflow conditions
   - Underflow conditions
   - Sticky error behavior

### 3. Verification Metrics
- **Code Coverage**: Line, branch, expression coverage
- **Functional Coverage**: Custom coverage points
- **Assertion Coverage**: Property verification
- **CDC Coverage**: Clock domain crossing verification

### 4. Configuration Parameters
- `DATA_WIDTH`: 8, 16, 32, 64 bits
- `ADDRESS_WIDTH`: 3-8 (depth 8-256)
- `SYNC_STAGE`: 2 or 3 stages
- `RESET_MEM`: 0 or 1
- `SOFT_RESET`: 0-3
- `POWER_SAVE`: 0 or 1
- `STICKY_ERROR`: 0 or 1
- `PIPE_WRITE/READ`: 0 or 1

## Running Verification
```bash
# Compile and run with ModelSim/QuestaSim
vlog -sv async_fifo.sv fifo_mem.sv rptr_empty.sv wptr_full.sv rd_ndff_synch.sv wr_ndff_synch.sv
vlog -sv tb/*.sv
vsim -c async_fifo_tb -do "run -all; quit"

# Or with VCS
vcs -full64 -sverilog async_fifo.sv fifo_mem.sv rptr_empty.sv wptr_full.sv rd_ndff_synch.sv wr_ndff_synch.sv tb/*.sv
./simv
``` 
