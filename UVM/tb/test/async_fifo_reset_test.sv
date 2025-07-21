`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_reset_test extends async_fifo_base_test;
  `uvm_component_utils(async_fifo_reset_test)

  function new(string name = "async_fifo_reset_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    async_fifo_reset_seq seq;
    
    super.run_phase(phase);
    
    phase.raise_objection(this);
    
    seq = async_fifo_reset_seq::type_id::create("seq");
    seq.start(env.agent.sequencer);
    
    phase.drop_objection(this);
  endtask

endclass 