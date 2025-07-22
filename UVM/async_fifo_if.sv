`timescale 1ns/1ps

interface async_fifo_if #(
  parameter DATA_WIDTH = 32,
  parameter ADDRESS_WIDTH = 5
) (
  input logic wclk,
  input logic rclk,
  input logic hw_rst_n
);
  // Write side signals
  logic [DATA_WIDTH-1:0] wdata;
  logic write_enable;
  logic [ADDRESS_WIDTH-1:0] afull_value;

  // Read side signals
  logic [DATA_WIDTH-1:0] read_data;
  logic read_enable;
  logic [ADDRESS_WIDTH-1:0] aempty_value;

  // Control signals
  logic sw_rst;
  logic mem_rst;

  // Status signals
  logic wfull;
  logic rdempty;
  logic wr_almost_ful;
  logic rd_almost_empty;
  logic overflow;
  logic underflow;
  logic [ADDRESS_WIDTH:0] fifo_write_count;
  logic [ADDRESS_WIDTH:0] fifo_read_count;
  logic [ADDRESS_WIDTH:0] wr_level;
  logic [ADDRESS_WIDTH:0] rd_level;

  // Write domain clocking block
  clocking write_cb @(posedge wclk);
    output wdata, write_enable, afull_value, sw_rst, mem_rst;
    input wfull, wr_almost_ful, overflow, fifo_write_count, wr_level;
  endclocking

  // Read domain clocking block
  clocking read_cb @(posedge rclk);
    output read_enable, aempty_value;
    input read_data, rdempty, rd_almost_empty, underflow, fifo_read_count, rd_level;
  endclocking

  // Modports
  modport write_mp(clocking write_cb, input hw_rst_n);
  modport read_mp(clocking read_cb, input hw_rst_n);
  modport monitor_mp(
    input wclk, rclk, hw_rst_n,
    wdata, write_enable, afull_value,
    read_data, read_enable, aempty_value, sw_rst, mem_rst,
    wfull, rdempty, wr_almost_ful, rd_almost_empty, overflow,
    underflow, fifo_write_count, fifo_read_count, wr_level, rd_level
  );

  // Default clocking
  default clocking default_cb @(posedge wclk);
  endclocking

  // Assertions (no explicit clocking event)
  property no_write_when_full;
    disable iff (!hw_rst_n)
      wfull |-> !write_enable;
  endproperty

  property no_read_when_empty;
    disable iff (!hw_rst_n)
      rdempty |-> !read_enable;
  endproperty

  property overflow_implies_full;
    disable iff (!hw_rst_n)
      overflow |-> wfull;
  endproperty

  property underflow_implies_empty;
    disable iff (!hw_rst_n)
      underflow |-> rdempty;
  endproperty

  // Assertions
  assert property (no_write_when_full)
    else $error("Write attempted when FIFO is full");
  assert property (no_read_when_empty)
    else $error("Read attempted when FIFO is empty");
  assert property (overflow_implies_full)
    else $error("Overflow occurred when FIFO is not full");
  assert property (underflow_implies_empty)
    else $error("Underflow occurred when FIFO is not empty");

endinterface 