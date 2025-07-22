`timescale 1ns/1ps

`include "async_fifo_config.sv"
`include "async_fifo_transaction.sv"
`include "async_fifo_base_test.sv" // <-- This is required!

class async_fifo_basic_test extends async_fifo_base_test;
  `uvm_component_utils(async_fifo_basic_test)

  function new(string name = "async_fifo_basic_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    async_fifo_basic_seq seq;
    
    super.run_phase(phase);
    
    phase.raise_objection(this);
    
    seq = async_fifo_basic_seq::type_id::create("seq");
    seq.start(env.agent.sequencer);
    
    phase.drop_objection(this);
  endtask

endclass 