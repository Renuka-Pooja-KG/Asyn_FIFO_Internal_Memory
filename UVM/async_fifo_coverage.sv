`timescale 1ns/1ps

// `include "async_fifo_config.sv"
// `include "async_fifo_transaction.sv"
// `include "async_fifo_if.sv"

class async_fifo_coverage extends uvm_subscriber #(async_fifo_transaction);
  `uvm_component_utils(async_fifo_coverage)

  async_fifo_config cfg;

  // Coverage groups
  covergroup fifo_cg with function sample(
    logic [31:0] wdata,
    logic write_enable,
    logic read_enable,
    logic [31:0] afull_value,
    logic [31:0] aempty_value,
    logic wfull,
    logic rdempty,
    logic wr_almost_ful,
    logic rd_almost_empty,
    logic overflow,
    logic underflow,
    int wr_level,
    int rd_level,
    logic sw_rst,
    logic hw_rst_n,
    logic mem_rst
  );
    // Data coverage
    wdata_cp: coverpoint wdata {
      bins zeros = {0};
      bins ones = {'1};
      bins alternating = {32'hAAAA_AAAA, 32'h5555_5555};
      bins others = default;
    }
    // Control signal coverage
    write_enable_cp: coverpoint write_enable;
    read_enable_cp: coverpoint read_enable;
    // Almost full/empty value coverage
    afull_value_cp: coverpoint afull_value {
      bins low = {[1:10]};
      bins medium = {[11:20]};
      bins high = {[21:30]};
    }
    aempty_value_cp: coverpoint aempty_value {
      bins low = {[1:10]};
      bins medium = {[11:20]};
      bins high = {[21:30]};
    }
    // FIFO state coverage
    fifo_state_cp: coverpoint {wfull, rdempty} {
      bins empty = {2'b01};
      bins full = {2'b10};
      bins normal = {2'b00};
      bins invalid = {2'b11};
    }
    // Almost full/empty state coverage
    almost_state_cp: coverpoint {wr_almost_ful, rd_almost_empty} {
      bins almost_full = {2'b10};
      bins almost_empty = {2'b01};
      bins normal = {2'b00};
      bins both = {2'b11};
    }
    // Error condition coverage
    error_cp: coverpoint {overflow, underflow} {
      bins no_error = {2'b00};
      bins overflow_only = {2'b10};
      bins underflow_only = {2'b01};
      bins both_errors = {2'b11};
    }
    // FIFO level coverage
    wr_level_cp: coverpoint wr_level {
      bins empty = {0};
      bins low = {[1:10]};
      bins medium = {[11:20]};
      bins high = {[21:30]};
      bins full = {32};
    }
    rd_level_cp: coverpoint rd_level {
      bins empty = {0};
      bins low = {[1:10]};
      bins medium = {[11:20]};
      bins high = {[21:30]};
      bins full = {32};
    }
    // Reset coverage
    reset_cp: coverpoint {sw_rst, hw_rst_n, mem_rst} {
      bins no_reset = {3'b000};
      bins hw_reset = {3'b010};
      bins sw_reset = {3'b100};
      bins mem_reset = {3'b001};
      bins hw_sw_reset = {3'b110};
      bins hw_mem_reset = {3'b011};
      bins sw_mem_reset = {3'b101};
      bins all_reset = {3'b111};
    }
    // Simultaneous write and read coverage
    both_enables_cp: coverpoint {write_enable, read_enable} {
      bins both_high = {2'b11};
      bins write_only = {2'b10};
      bins read_only = {2'b01};
      bins neither = {2'b00};
    }
    // Cross coverage
    write_read_cross: cross write_enable_cp, read_enable_cp, both_enables_cp;
    state_error_cross: cross fifo_state_cp, error_cp;
    level_state_cross: cross wr_level_cp, fifo_state_cp;
    reset_state_cross: cross reset_cp, fifo_state_cp;
  endgroup

  // Additional coverage for CDC scenarios
  covergroup cdc_cg with function sample(
    int wr_level,
    int rd_level,
    logic wfull,
    logic rdempty
  );
    cdc_level_diff: coverpoint (wr_level - rd_level) {
      bins small_diff = {[-5:5]};
      bins medium_diff = {[-15:-6], [6:15]};
      bins large_diff = {[-32:-16], [16:32]};
    }
    cdc_full_empty: coverpoint {wfull, rdempty} {
      bins empty = {2'b01};
      bins full = {2'b10};
      bins normal = {2'b00};
    }
  endgroup

  function new(string name = "async_fifo_coverage", uvm_component parent = null);
    super.new(name, parent);
    fifo_cg = new();
    cdc_cg = new();
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(async_fifo_config)::get(this, "", "cfg", cfg))
      `uvm_fatal("NOCFG", "Configuration not found")
  endfunction

  function void write(async_fifo_transaction t);
    // Sample coverage for write transactions
    if (t.write_enable) begin
      fifo_cg.sample(
        t.wdata, t.write_enable, t.read_enable,
        t.afull_value, t.aempty_value,
        t.wfull, t.rdempty, t.wr_almost_ful, t.rd_almost_empty,
        t.overflow, t.underflow,
        t.wr_level, t.rd_level,
        t.sw_rst, t.hw_rst_n, t.mem_rst
      );
      cdc_cg.sample(t.wr_level, t.rd_level, t.wfull, t.rdempty);
    end
    // Sample coverage for read transactions
    if (t.read_enable) begin
      fifo_cg.sample(
        t.wdata, t.write_enable, t.read_enable,
        t.afull_value, t.aempty_value,
        t.wfull, t.rdempty, t.wr_almost_ful, t.rd_almost_empty,
        t.overflow, t.underflow,
        t.wr_level, t.rd_level,
        t.sw_rst, t.hw_rst_n, t.mem_rst
      );
      cdc_cg.sample(t.wr_level, t.rd_level, t.wfull, t.rdempty);
    end
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(), $sformatf("FIFO Coverage: %.2f%%", fifo_cg.get_coverage()), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("CDC Coverage: %.2f%%", cdc_cg.get_coverage()), UVM_LOW)
    if (fifo_cg.error_cp.get_coverage() < 100) begin
      `uvm_warning(get_type_name(), "Error condition coverage not complete")
    end
    if (fifo_cg.reset_cp.get_coverage() < 100) begin
      `uvm_warning(get_type_name(), "Reset condition coverage not complete")
    end
  endfunction

endclass 