`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_sequencer extends uvm_sequencer #(async_fifo_transaction);
  `uvm_component_utils(async_fifo_sequencer)

  function new(string name = "async_fifo_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction

endclass 