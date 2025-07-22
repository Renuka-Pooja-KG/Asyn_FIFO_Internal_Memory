`timescale 1ns/1ps

class async_fifo_sequencer extends uvm_sequencer #(async_fifo_transaction);
  `uvm_component_utils(async_fifo_sequencer)

  function new(string name = "async_fifo_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction

endclass 