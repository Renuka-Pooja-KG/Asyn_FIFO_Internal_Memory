`timescale 1ns/1ps

import uvm_pkg::*;
import async_fifo_pkg::*;

module async_fifo_tb;
  
  // Clock and reset signals
  logic wclk, rclk, hw_rst_n;
  
  // Interface instantiation (parameterized)
  async_fifo_if #(.DATA_WIDTH(32), .ADDRESS_WIDTH(5)) fifo_if(wclk, rclk, hw_rst_n);
  
  // DUT instantiation
  async_fifo_int_mem #(
    .DATA_WIDTH(32),
    .ADDRESS_WIDTH(5),
    .SYNC_STAGE(2),
    .RESET_MEM(1),
    .SOFT_RESET(3),
    .POWER_SAVE(1),
    .STICKY_ERROR(0),
    .PIPE_WRITE(0),
    .DEBUG_ENABLE(1),
    .PIPE_READ(0)
  ) dut (
    .read_data(fifo_if.read_data),
    .wfull(fifo_if.wfull),
    .rdempty(fifo_if.rdempty),
    .wr_almost_ful(fifo_if.wr_almost_ful),
    .rd_almost_empty(fifo_if.rd_almost_empty),
    .overflow(fifo_if.overflow),
    .underflow(fifo_if.underflow),
    .fifo_write_count(fifo_if.fifo_write_count),
    .fifo_read_count(fifo_if.fifo_read_count),
    .wr_level(fifo_if.wr_level),
    .rd_level(fifo_if.rd_level),
    .sw_rst(fifo_if.sw_rst),
    .wdata(fifo_if.wdata),
    .write_enable(fifo_if.write_enable),
    .wclk(fifo_if.wclk),
    .hw_rst_n(fifo_if.hw_rst_n),
    .read_enable(fifo_if.read_enable),
    .rclk(fifo_if.rclk),
    .afull_value(fifo_if.afull_value),
    .aempty_value(fifo_if.aempty_value),
    .mem_rst(fifo_if.mem_rst)
  );

  // Clock generation
  initial begin
    wclk = 0;
    forever #5 wclk = ~wclk; // 100MHz
  end

  initial begin
    rclk = 0;
    forever #7.5 rclk = ~rclk; // 66.67MHz
  end

  // Reset generation (active low)
  initial begin
    hw_rst_n = 0;
    #100;
    hw_rst_n = 1;
  end

  // UVM test execution
  initial begin
    // Set up virtual interface
    uvm_config_db#(virtual async_fifo_if.write_mp)::set(null, "*", "vif", fifo_if);
    uvm_config_db#(virtual async_fifo_if.monitor_mp)::set(null, "*", "vif", fifo_if);
    
    // Run test
    run_test();
  end

  // Waveform dumping
  initial begin
    $dumpfile("async_fifo_tb.vcd");
    $dumpvars(0, async_fifo_tb);
  end

  // Timeout
  initial begin
    #1000000; // 1ms timeout
    $display("Simulation timeout");
    $finish;
  end

  // Monitor for simulation completion
  initial begin
    wait(uvm_report_server::get_server().get_severity_count(UVM_FATAL) > 0 ||
         uvm_report_server::get_server().get_severity_count(UVM_ERROR) > 0);
    #1000;
    $finish;
  end

endmodule 