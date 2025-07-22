`timescale 1ns/1ps

import uvm_pkg::*;
`include "uvm_macros.svh"

class async_fifo_transaction extends uvm_sequence_item;
  `uvm_object_utils(async_fifo_transaction)

  localparam int DATA_WIDTH = 32;
  localparam int ADDRESS_WIDTH = 5;
  rand logic [DATA_WIDTH-1:0] wdata;
  rand logic write_enable;
  rand logic [ADDRESS_WIDTH-1:0] afull_value;
  // Read side signals
  rand logic read_enable;
  rand logic [ADDRESS_WIDTH-1:0] aempty_value;
  // Control signals
  rand logic sw_rst;
  rand logic hw_rst_n;
  rand logic mem_rst;
  // Response signals
  logic [DATA_WIDTH-1:0] read_data;
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

  // Constraints
  constraint c_afull_value { afull_value inside {[1:30]}; }
  constraint c_aempty_value { aempty_value inside {[1:30]}; }
  constraint c_write_enable { write_enable dist {0:=70, 1:=30}; }
  constraint c_read_enable { read_enable dist {0:=70, 1:=30}; }

  function new(string name = "async_fifo_transaction");
    super.new(name);
  endfunction

  function string convert2string();
    return $sformatf("wdata=0x%h, write_en=%b, read_en=%b, wfull=%b, empty=%b, overflow=%b, underflow=%b", 
                    wdata, write_enable, read_enable, wfull, rdempty, overflow, underflow);
  endfunction

  function void do_copy(uvm_object rhs);
    async_fifo_transaction rhs_;
    if (!$cast(rhs_, rhs)) begin
      `uvm_fatal("DO_COPY", "cast failed")
      return;
    end
    super.do_copy(rhs);
    wdata = rhs_.wdata;
    write_enable = rhs_.write_enable;
    read_enable = rhs_.read_enable;
    afull_value = rhs_.afull_value;
    aempty_value = rhs_.aempty_value;
    sw_rst = rhs_.sw_rst;
    hw_rst_n = rhs_.hw_rst_n;
    mem_rst = rhs_.mem_rst;
    read_data = rhs_.read_data;
    wfull = rhs_.wfull;
    rdempty = rhs_.rdempty;
    wr_almost_ful = rhs_.wr_almost_ful;
    rd_almost_empty = rhs_.rd_almost_empty;
    overflow = rhs_.overflow;
    underflow = rhs_.underflow;
    fifo_write_count = rhs_.fifo_write_count;
    fifo_read_count = rhs_.fifo_read_count;
    wr_level = rhs_.wr_level;
    rd_level = rhs_.rd_level;
  endfunction

  function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    async_fifo_transaction rhs_;
    if (!$cast(rhs_, rhs)) return 0;
    return (wdata == rhs_.wdata && 
            write_enable == rhs_.write_enable && 
            read_enable == rhs_.read_enable);
  endfunction

endclass 